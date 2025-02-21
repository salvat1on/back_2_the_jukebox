import os
import json
import random
import threading
import io
import time
import queue
import tkinter as tk
from tkinter import simpledialog, filedialog, messagebox
from tkinter import ttk
import pygame
import numpy as np  # for plasma effect

# Initialize pygame mixer for audio playback
pygame.mixer.init()

# Supported audio file extensions
AUDIO_EXTENSIONS = ('.mp3', '.wav', '.flac')

# Configuration files
CONFIG_FILE = "config.json"
PLAYLISTS_FILE = "playlists.json"

# Try to import Mutagen and Pillow for album art extraction.
try:
    from mutagen.id3 import ID3
    from mutagen.mp3 import MP3
    from PIL import Image, ImageTk
    HAS_ART_EXTRACTION = True
except ImportError:
    HAS_ART_EXTRACTION = False

def load_config():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r") as f:
                config = json.load(f)
        except Exception:
            config = {"music_folders": []}
    else:
        config = {"music_folders": []}
    return config

def save_config(config):
    try:
        with open(CONFIG_FILE, "w") as f:
            json.dump(config, f)
    except Exception as e:
        print("Error saving config:", e)

def load_playlists():
    if os.path.exists(PLAYLISTS_FILE):
        try:
            with open(PLAYLISTS_FILE, "r") as f:
                plist = json.load(f)
        except Exception:
            plist = {}
    else:
        plist = {}
    return plist

def save_playlists(plist):
    try:
        # Build a version of the playlists that only includes JSON-serializable track info.
        serializable = {}
        for playlist_name, playlist in plist.items():
            serializable[playlist_name] = []
            for track in playlist:
                serializable[playlist_name].append({
                    "path": track.get("path"),
                    "title": track.get("title"),
                    "artist": track.get("artist"),
                    "album": track.get("album"),
                    "duration": track.get("duration")
                })
        with open(PLAYLISTS_FILE, "w") as f:
            json.dump(serializable, f)
    except Exception as e:
        print("Error saving playlists:", e)

class BackToTheJukebox(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Back to the Jukebox")
        self.geometry("1200x800")
        self.configure(bg="#000000")  # Black background

        # Load configuration and playlists.
        self.config_data = load_config()
        self.playlists_data = load_playlists()

        # Library: list of track dictionaries.
        self.library = []
        self.filtered_library = []  # For search results.

        # Current playlist (if loaded) is stored here.
        self.current_playlist = None

        # Playback tracking.
        self.current_track_list = None   # Either current_playlist or library.
        self.current_track_index = None
        self.play_start_time = None  # Time when playback started.
        self.play_offset = 0         # Seconds offset for seeks.
        self.current_track_duration = 0

        # Next song is stored here.
        self.stored_next_song = None

        # Playback mode.
        self.random_mode = False

        # To hold treeview images.
        self.tree_images = {}

        # EQ animation variables.
        self.eq_bars = 50
        self.eq_values = [0] * self.eq_bars

        # Queue for plasma visualizer frames.
        self.plasma_queue = queue.Queue(maxsize=2)

        # Setup UI.
        self.setup_menu()
        self.setup_ui()
        self.tree.bind("<Button-3>", self.on_tree_right_click)

        # Load music folders.
        if self.config_data.get("music_folders"):
            for folder in self.config_data["music_folders"]:
                self.scan_folder(folder)
            self.update_library_view()

        # Start monitors and animations.
        self.animate_equalizer()
        self.update_progress_bar()
        self.monitor_playback()

    def setup_menu(self):
        menubar = tk.Menu(self, bg="#000000", fg="#00FFFF")
        self.config(menu=menubar)
        file_menu = tk.Menu(menubar, tearoff=0, bg="#000000", fg="#00FFFF")
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Add Music Folder", command=self.add_music_folder)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        playlist_menu = tk.Menu(menubar, tearoff=0, bg="#000000", fg="#00FFFF")
        menubar.add_cascade(label="Playlist", menu=playlist_menu)
        # Use the renamed method below.
        playlist_menu.add_command(label="Create New Playlist", command=self._create_new_playlist)
        playlist_menu.add_command(label="Load Playlist", command=self.load_playlist)
        playlist_menu.add_command(label="Show All Music", command=self.show_all_music)
        playlist_menu.add_separator()
        playlist_menu.add_command(label="Save Current Playlist", command=self.save_current_playlist)

    def setup_ui(self):
        # Left side: search area and library treeview.
        self.neon_frame = tk.Frame(self, bg="#00FFFF", padx=3, pady=3)
        self.neon_frame.pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=10)
        inner_left = tk.Frame(self.neon_frame, bg="#000000")
        inner_left.pack(fill=tk.BOTH, expand=True)
        # Search area.
        self.search_var = tk.StringVar()
        search_frame = tk.Frame(inner_left, bg="#000000")
        search_frame.pack(pady=5)
        tk.Label(search_frame, text="Search:", fg="#00FFFF", bg="#000000", font=("Helvetica", 14)).pack(side=tk.LEFT)
        self.search_entry = tk.Entry(search_frame, textvariable=self.search_var, font=("Helvetica", 14), width=20,
                                     bg="#000000", fg="#00FFFF", insertbackground="#00FFFF", relief=tk.FLAT)
        self.search_entry.pack(side=tk.LEFT, padx=5)
        tk.Button(search_frame, text="Go", command=self.search_library,
                  bg="#FF00FF", fg="#000000", font=("Helvetica", 12)).pack(side=tk.LEFT)
        # Treeview.
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview", background="#000000", fieldbackground="#000000",
                        foreground="#00FFFF", font=("Helvetica", 12))
        style.configure("Treeview.Heading", background="#000000", foreground="#00FFFF", font=("Helvetica", 14))
        self.tree = ttk.Treeview(inner_left)
        self.tree["columns"] = ("Title",)
        self.tree.column("#0", width=150, anchor="w")
        self.tree.column("Title", width=250, anchor="w")
        self.tree.heading("#0", text="Artist")
        self.tree.heading("Title", text="Title")
        self.tree.pack(pady=10, fill=tk.BOTH, expand=True)
        self.tree.bind("<Double-1>", self.on_tree_double_click)
        # Playback controls.
        controls_frame = tk.Frame(inner_left, bg="#000000")
        controls_frame.pack(pady=10)
        self.play_button = tk.Button(controls_frame, text="▶ Play", command=self.play_selected,
                                     bg="#00FF00", fg="#000000", font=("Helvetica", 14))
        self.play_button.grid(row=0, column=0, padx=5)
        self.stop_button = tk.Button(controls_frame, text="■ Stop", command=self.stop_music,
                                     bg="#FF0000", fg="#000000", font=("Helvetica", 14))
        self.stop_button.grid(row=0, column=1, padx=5)
        self.shuffle_button = tk.Button(controls_frame, text="Shuffle: OFF", command=self.toggle_shuffle,
                                        bg="#FFFF00", fg="#000000", font=("Helvetica", 14))
        self.shuffle_button.grid(row=0, column=2, padx=5)
        self.visualize_button = tk.Button(controls_frame, text="🎨 Visualize", command=self.open_visualizer_window,
                                          bg="#FFFF00", fg="#000000", font=("Helvetica", 14))
        self.visualize_button.grid(row=0, column=3, padx=5)
        # Right side: album art, EQ, progress bar, next song.
        self.right_frame = tk.Frame(self, bg="#000000")
        self.right_frame.pack(side=tk.RIGHT, expand=True, fill=tk.BOTH, padx=10, pady=10)
        self.album_art_label = tk.Label(self.right_frame, bg="#000000")
        self.album_art_label.pack(pady=10)
        try:
            self.placeholder_image = tk.PhotoImage(file="jukebox.png")
        except Exception:
            self.placeholder_image = tk.PhotoImage(width=300, height=300)
            self.placeholder_image.put(("gray",), to=(0, 0, 300, 300))
        self.album_art_label.config(image=self.placeholder_image)
        self.eq_canvas = tk.Canvas(self.right_frame, bg="#000000", width=600, height=150, highlightthickness=0)
        self.eq_canvas.pack(pady=10)
        progress_frame = tk.Frame(self.right_frame, bg="#000000")
        progress_frame.pack(pady=5, fill=tk.X)
        self.progress_label = tk.Label(progress_frame, text="0:00 / 0:00", bg="#000000", fg="#00FFFF", font=("Helvetica", 12))
        self.progress_label.pack(side=tk.LEFT, padx=5)
        self.progress_scale = tk.Scale(progress_frame, from_=0, to=100, orient=tk.HORIZONTAL, length=400,
                                       bg="#000000", fg="#00FFFF", troughcolor="#00FFFF", highlightthickness=0)
        self.progress_scale.bind("<ButtonPress-1>", lambda e: setattr(self, "user_dragging", True))
        self.progress_scale.bind("<ButtonRelease-1>", self.on_progress_release)
        self.progress_scale.pack(side=tk.LEFT, padx=5)
        self.user_dragging = False
        self.next_song_label = tk.Label(self.right_frame, text="Next Song: N/A", bg="#000000", fg="#00FFFF", font=("Helvetica", 12))
        self.next_song_label.pack(pady=5)

    def add_music_folder(self):
        folder = filedialog.askdirectory(title="Select Music Folder")
        if not folder:
            return
        if folder not in self.config_data.get("music_folders", []):
            self.config_data.setdefault("music_folders", []).append(folder)
            save_config(self.config_data)
        progress_win = tk.Toplevel(self)
        progress_win.title("Loading Music")
        progress_win.geometry("300x100")
        progress_win.configure(bg="#000000")
        tk.Label(progress_win, text="Scanning music folder...", fg="#00FFFF", bg="#000000", font=("Helvetica", 12)).pack(pady=10)
        progress = ttk.Progressbar(progress_win, mode='indeterminate')
        progress.pack(pady=5, fill=tk.X, padx=10)
        progress.start(10)
        def scan_and_update():
            self.scan_folder(folder)
            self.after(0, self.update_library_view)
            self.after(0, progress_win.destroy)
        threading.Thread(target=scan_and_update, daemon=True).start()

    def scan_folder(self, folder):
        folder = os.path.abspath(folder)
        for root, dirs, files in os.walk(folder, topdown=True, followlinks=False):
            for file in files:
                if file.lower().endswith(AUDIO_EXTENSIONS):
                    full_path = os.path.join(root, file)
                    track = self.get_track_metadata(full_path)
                    self.library.append(track)

    def get_track_metadata(self, file_path):
        metadata = {
            "path": file_path,
            "title": os.path.splitext(os.path.basename(file_path))[0],
            "artist": "Unknown Artist",
            "album": "Unknown Album",
            "album_art": None,
            "duration": 0
        }
        if HAS_ART_EXTRACTION and file_path.lower().endswith(".mp3"):
            try:
                audio_mp3 = MP3(file_path)
                metadata["duration"] = int(audio_mp3.info.length)
                tags = ID3(file_path)
                if tags.get("TIT2"):
                    metadata["title"] = tags["TIT2"].text[0]
                if tags.get("TPE1"):
                    metadata["artist"] = tags["TPE1"].text[0]
                if tags.get("TALB"):
                    metadata["album"] = tags["TALB"].text[0]
                for tag in tags.values():
                    if tag.FrameID == "APIC":
                        try:
                            image_data = tag.data
                            image = Image.open(io.BytesIO(image_data))
                            image = image.convert("RGB")
                            image = image.resize((50, 50))
                            metadata["album_art"] = image
                        except Exception:
                            metadata["album_art"] = None
                        break
            except Exception as e:
                print(f"Metadata extraction failed for {file_path}: {e}")
        return metadata

    def update_library_view(self):
        for item in self.tree.get_children():
            self.tree.delete(item)
        tracks = self.filtered_library if self.filtered_library else self.library
        artist_groups = {}
        for track in tracks:
            artist = track.get("artist", "Unknown Artist")
            artist_groups.setdefault(artist, []).append(track)
        for artist, track_list in artist_groups.items():
            artist_icon = None
            for track in track_list:
                if track.get("album_art"):
                    try:
                        artist_icon = ImageTk.PhotoImage(track["album_art"])
                    except Exception:
                        artist_icon = None
                    break
            if artist_icon:
                parent_id = self.tree.insert("", tk.END, text=artist, values=("",), open=True, image=artist_icon)
                self.tree_images[artist] = artist_icon
            else:
                parent_id = self.tree.insert("", tk.END, text=artist, values=("",), open=True)
            for track in track_list:
                self.tree.insert(parent_id, tk.END, text="", values=(track.get("title", "Unknown Title"),), tags=(track["path"],))

    def search_library(self):
        query = self.search_var.get().lower()
        if not query:
            self.filtered_library = []
        else:
            self.filtered_library = [track for track in self.library 
                                     if query in track.get("title", "").lower() or query in track.get("artist", "").lower()]
        self.update_library_view()

    def on_tree_double_click(self, event):
        item = self.tree.selection()
        if not item:
            return
        tags = self.tree.item(item[0], "tags")
        if tags:
            self.play_track_by_path(tags[0])

    def on_tree_right_click(self, event):
        iid = self.tree.identify_row(event.y)
        if not iid:
            return
        self.tree.selection_set(iid)
        tags = self.tree.item(iid, "tags")
        menu = tk.Menu(self, tearoff=0, bg="#000000", fg="#00FFFF")
        if tags:
            submenu = tk.Menu(menu, tearoff=0, bg="#000000", fg="#00FFFF")
            submenu.add_command(label="Add to current playlist", command=lambda: self.add_song_to_playlist(tags[0]))
            submenu.add_command(label="Create new playlist and add", command=lambda: self.create_playlist_and_add(tags[0]))
            menu.add_cascade(label="Add to Playlist", menu=submenu)
            if self.current_playlist is not None and any(track["path"] == tags[0] for track in self.current_playlist):
                menu.add_command(label="Remove from Playlist", command=lambda: self.remove_song_from_playlist(tags[0]))
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def create_playlist_and_add(self, track_path):
        new_name = simpledialog.askstring("New Playlist", "Enter new playlist name:")
        if new_name:
            self.current_playlist = []  # create new playlist
            self.playlists_data[new_name] = self.current_playlist
            save_playlists(self.playlists_data)
            self.add_song_to_playlist(track_path)
            messagebox.showinfo("Playlist", f"Playlist '{new_name}' created and song added.")

    def add_song_to_playlist(self, track_path):
        if self.current_playlist is None:
            messagebox.showinfo("Playlist", "No active playlist. Please load or create a playlist first.")
            return
        if any(track["path"] == track_path for track in self.current_playlist):
            messagebox.showinfo("Playlist", "Song is already in the current playlist.")
        else:
            for track in self.library:
                if track["path"] == track_path:
                    self.current_playlist.append(track)
                    # Auto-save the playlist after adding a new track.
                    save_playlists(self.playlists_data)
                    messagebox.showinfo("Playlist", "Song added to current playlist.")
                    self.update_library_view()
                    return

    def remove_song_from_playlist(self, track_path):
        if self.current_playlist is None:
            messagebox.showinfo("Playlist", "No active playlist.")
            return
        for i, track in enumerate(self.current_playlist):
            if track["path"] == track_path:
                del self.current_playlist[i]
                # Auto-save the playlist after removal.
                save_playlists(self.playlists_data)
                messagebox.showinfo("Playlist", "Song removed from current playlist.")
                self.update_library_view()
                return
        messagebox.showinfo("Playlist", "Song not found in the current playlist.")

    def play_track_by_path(self, track_path):
        try:
            self.current_track_list = self.current_playlist if self.current_playlist is not None else self.library
            for idx, track in enumerate(self.current_track_list):
                if track["path"] == track_path:
                    self.current_track_index = idx
                    self.current_track_duration = track.get("duration", 0)
                    if not self.random_mode:
                        next_idx = (idx + 1) % len(self.current_track_list)
                        self.stored_next_song = self.current_track_list[next_idx]
                    else:
                        self.stored_next_song = random.choice([t for i, t in enumerate(self.current_track_list) if i != idx])
                    break
            pygame.mixer.music.load(track_path)
            pygame.mixer.music.play()
            self.play_start_time = time.time()
            self.play_offset = 0
            album_art = self.get_album_art_full(track_path)
            if album_art:
                self.album_art_photo = ImageTk.PhotoImage(album_art)
                self.album_art_label.config(image=self.album_art_photo)
            else:
                self.album_art_label.config(image=self.placeholder_image)
            self.progress_scale.config(to=self.current_track_duration)
            self.update_next_song_label()
        except Exception as e:
            messagebox.showerror("Playback Error", str(e))

    def play_selected(self):
        selected = self.tree.selection()
        if not selected:
            messagebox.showwarning("No Selection", "Please select a track to play.")
            return
        tags = self.tree.item(selected[0], "tags")
        if tags:
            self.play_track_by_path(tags[0])

    def stop_music(self):
        pygame.mixer.music.stop()

    def get_album_art_full(self, track_path):
        if not HAS_ART_EXTRACTION or not track_path.lower().endswith(".mp3"):
            return None
        try:
            tags = ID3(track_path)
            for tag in tags.values():
                if tag.FrameID == "APIC":
                    image_data = tag.data
                    image = Image.open(io.BytesIO(image_data))
                    image = image.convert("RGB")
                    image = image.resize((300, 300))
                    return image
        except Exception as e:
            print(f"Full album art extraction failed for {track_path}: {e}")
        return None

    def animate_equalizer(self):
        self.eq_canvas.delete("all")
        canvas_width = int(self.eq_canvas['width'])
        canvas_height = int(self.eq_canvas['height'])
        bar_width = canvas_width / self.eq_bars
        if pygame.mixer.music.get_busy():
            targets = [random.randint(10, canvas_height) for _ in range(self.eq_bars)]
        else:
            targets = [random.randint(5, int(canvas_height/4)) for _ in range(self.eq_bars)]
        inertia = 0.2
        for i in range(self.eq_bars):
            self.eq_values[i] += inertia * (targets[i] - self.eq_values[i])
            bar_height = int(self.eq_values[i])
            x0 = i * bar_width
            y0 = canvas_height - bar_height
            x1 = (i + 1) * bar_width - 2
            y1 = canvas_height
            color = "#00FFFF" if pygame.mixer.music.get_busy() else "#005555"
            self.eq_canvas.create_rectangle(x0, y0, x1, y1, fill=color, outline=color)
        self.after(100, self.animate_equalizer)

    def update_progress_bar(self):
        if pygame.mixer.music.get_busy() and self.play_start_time is not None:
            computed_elapsed = (time.time() - self.play_start_time) + self.play_offset
            get_elapsed = pygame.mixer.music.get_pos() / 1000.0
            elapsed = max(computed_elapsed, get_elapsed)
            total_int = int(self.current_track_duration)
            self.progress_scale.unbind("<ButtonRelease-1>")
            if not self.user_dragging:
                self.progress_scale.set(elapsed)
            self.progress_label.config(text=f"{int(elapsed)//60}:{int(elapsed)%60:02d} / {total_int//60}:{total_int%60:02d}")
            self.progress_scale.bind("<ButtonRelease-1>", self.on_progress_release)
        self.after(250, self.update_progress_bar)

    def on_progress_release(self, event):
        self.user_dragging = True
        pos = float(self.progress_scale.get())
        try:
            pygame.mixer.music.set_pos(pos)
        except Exception as e:
            print("Seek failed:", e)
        self.play_start_time = time.time() - pos
        self.play_offset = 0
        self.user_dragging = False

    def monitor_playback(self):
        if self.current_track_duration and self.play_start_time is not None:
            computed_elapsed = (time.time() - self.play_start_time) + self.play_offset
            get_elapsed = pygame.mixer.music.get_pos() / 1000.0
            elapsed = max(computed_elapsed, get_elapsed)
            if elapsed >= self.current_track_duration - 1 and not pygame.mixer.music.get_busy():
                self.play_next_song()
        self.after(200, self.monitor_playback)

    def play_next_song(self):
        if self.current_track_list is None or self.current_track_index is None:
            return
        if self.random_mode:
            next_index = random.randint(0, len(self.current_track_list) - 1)
            if len(self.current_track_list) > 1:
                while next_index == self.current_track_index:
                    next_index = random.randint(0, len(self.current_track_list) - 1)
        else:
            next_index = self.current_track_index + 1
            if next_index >= len(self.current_track_list):
                next_index = 0
        self.current_track_index = next_index
        next_track = self.current_track_list[next_index]
        self.play_track_by_path(next_track["path"])

    def update_next_song_label(self):
        if self.stored_next_song is not None:
            self.next_song_label.config(text=f"Next Song: {self.stored_next_song.get('title', 'Unknown Title')}")
        elif self.current_track_list is not None and self.current_track_index is not None:
            if not self.random_mode:
                next_index = (self.current_track_index + 1) % len(self.current_track_list)
                self.stored_next_song = self.current_track_list[next_index]
            else:
                self.stored_next_song = random.choice([t for i, t in enumerate(self.current_track_list) if i != self.current_track_index])
            self.next_song_label.config(text=f"Next Song: {self.stored_next_song.get('title', 'Unknown Title')}")
        else:
            self.next_song_label.config(text="Next Song: N/A")

    def toggle_shuffle(self):
        self.random_mode = not self.random_mode
        state = "ON" if self.random_mode else "OFF"
        self.shuffle_button.config(text=f"Shuffle: {state}")
        self.stored_next_song = None
        self.update_next_song_label()

    def open_visualizer_window(self):
        vis_win = tk.Toplevel(self)
        vis_win.title("Psychedelic Visualizer")
        vis_win.configure(bg="#000000")
        vis_win.geometry("800x600")
        canvas = tk.Canvas(vis_win, bg="#000000", width=800, height=600, highlightthickness=0)
        canvas.pack(fill=tk.BOTH, expand=True)
        plasma_queue = queue.Queue(maxsize=2)
        stop_event = threading.Event()
        def compute_plasma():
            comp_width, comp_height = 80, 60  # low resolution for speed
            while not stop_event.is_set():
                t = time.time()
                x = np.linspace(0, 4*np.pi, comp_width)
                y = np.linspace(0, 4*np.pi, comp_height)
                X, Y = np.meshgrid(x, y)
                Z = np.sin(X + t) + np.sin(Y + t) + np.sin((X + Y + t) / 2.0)
                Z_norm = (Z - Z.min()) / (Z.max() - Z.min())
                R = np.uint8(255 * (np.sin(2*np.pi*Z_norm) + 1) / 2)
                G = np.uint8(255 * (np.sin(2*np.pi*Z_norm + 2*np.pi/3) + 1) / 2)
                B = np.uint8(255 * (np.sin(2*np.pi*Z_norm + 4*np.pi/3) + 1) / 2)
                img_array = np.dstack((R, G, B))
                from PIL import Image
                img = Image.fromarray(img_array, 'RGB')
                upscaled = img.resize((canvas.winfo_width(), canvas.winfo_height()), Image.BILINEAR)
                photo = ImageTk.PhotoImage(upscaled)
                try:
                    plasma_queue.put(photo, timeout=0.01)
                except queue.Full:
                    pass
                time.sleep(0.05)
        plasma_thread = threading.Thread(target=compute_plasma, daemon=True)
        plasma_thread.start()
        def update_canvas():
            try:
                photo = plasma_queue.get_nowait()
                canvas.create_image(0, 0, image=photo, anchor=tk.NW)
                canvas.image = photo  # keep a reference
            except queue.Empty:
                pass
            canvas.after(25, update_canvas)
        update_canvas()
        def on_close():
            stop_event.set()
            vis_win.destroy()
        vis_win.protocol("WM_DELETE_WINDOW", on_close)

    def _create_new_playlist(self):
        # This method is now renamed to avoid conflicts.
        new_name = simpledialog.askstring("New Playlist", "Enter new playlist name:")
        if new_name:
            # Create a new playlist (or keep the current one if it exists).
            if self.current_playlist is None:
                self.current_playlist = []
            self.playlists_data[new_name] = self.current_playlist
            save_playlists(self.playlists_data)
            messagebox.showinfo("Playlist", f"Playlist '{new_name}' created.")

    def load_playlist(self):
        if not self.playlists_data:
            messagebox.showinfo("Playlist", "No playlists available.")
            return
        top = tk.Toplevel(self)
        top.title("Load Playlist")
        top.configure(bg="#000000")
        tk.Label(top, text="Select a Playlist:", bg="#000000", fg="#00FFFF", font=("Helvetica", 14)).pack(pady=10)
        lb = tk.Listbox(top, bg="#000000", fg="#00FFFF", font=("Helvetica", 12))
        for name in self.playlists_data.keys():
            lb.insert(tk.END, name)
        lb.pack(pady=5)
        def load_sel():
            sel = lb.curselection()
            if sel:
                name = lb.get(sel[0])
                self.current_playlist = self.playlists_data.get(name, [])
                self.filtered_library = self.current_playlist
                self.update_library_view()
                top.destroy()
        tk.Button(top, text="Load", command=load_sel, bg="#00FF00", fg="#000000", font=("Helvetica", 12)).pack(pady=10)

    def save_current_playlist(self):
        if self.current_playlist is None:
            messagebox.showinfo("Playlist", "No playlist is currently active.")
            return
        save_playlists(self.playlists_data)
        messagebox.showinfo("Playlist", "Current playlist saved.")

    def show_all_music(self):
        self.current_playlist = None
        self.filtered_library = []
        self.update_library_view()

    def monitor_playback(self):
        if self.current_track_duration and self.play_start_time is not None:
            computed_elapsed = (time.time() - self.play_start_time) + self.play_offset
            get_elapsed = pygame.mixer.music.get_pos() / 1000.0
            elapsed = max(computed_elapsed, get_elapsed)
            if elapsed >= self.current_track_duration - 1 and not pygame.mixer.music.get_busy():
                self.play_next_song()
        self.after(200, self.monitor_playback)

    def play_next_song(self):
        if self.current_track_list is None or self.current_track_index is None:
            return
        if self.random_mode:
            next_index = random.randint(0, len(self.current_track_list) - 1)
            if len(self.current_track_list) > 1:
                while next_index == self.current_track_index:
                    next_index = random.randint(0, len(self.current_track_list) - 1)
        else:
            next_index = self.current_track_index + 1
            if next_index >= len(self.current_track_list):
                next_index = 0
        self.current_track_index = next_index
        next_track = self.current_track_list[next_index]
        self.play_track_by_path(next_track["path"])

    def update_next_song_label(self):
        if self.stored_next_song is not None:
            self.next_song_label.config(text=f"Next Song: {self.stored_next_song.get('title', 'Unknown Title')}")
        elif self.current_track_list is not None and self.current_track_index is not None:
            if not self.random_mode:
                next_index = (self.current_track_index + 1) % len(self.current_track_list)
                self.stored_next_song = self.current_track_list[next_index]
            else:
                self.stored_next_song = random.choice([t for i, t in enumerate(self.current_track_list) if i != self.current_track_index])
            self.next_song_label.config(text=f"Next Song: {self.stored_next_song.get('title', 'Unknown Title')}")
        else:
            self.next_song_label.config(text="Next Song: N/A")

    def toggle_shuffle(self):
        self.random_mode = not self.random_mode
        state = "ON" if self.random_mode else "OFF"
        self.shuffle_button.config(text=f"Shuffle: {state}")
        self.stored_next_song = None
        self.update_next_song_label()

    def open_visualizer_window(self):
        vis_win = tk.Toplevel(self)
        vis_win.title("Psychedelic Visualizer")
        vis_win.configure(bg="#000000")
        vis_win.geometry("800x600")
        canvas = tk.Canvas(vis_win, bg="#000000", width=800, height=600, highlightthickness=0)
        canvas.pack(fill=tk.BOTH, expand=True)
        plasma_queue = queue.Queue(maxsize=2)
        stop_event = threading.Event()
        def compute_plasma():
            comp_width, comp_height = 80, 60
            while not stop_event.is_set():
                t = time.time()
                x = np.linspace(0, 4*np.pi, comp_width)
                y = np.linspace(0, 4*np.pi, comp_height)
                X, Y = np.meshgrid(x, y)
                Z = np.sin(X + t) + np.sin(Y + t) + np.sin((X + Y + t) / 2.0)
                Z_norm = (Z - Z.min()) / (Z.max() - Z.min())
                R = np.uint8(255 * (np.sin(2*np.pi*Z_norm) + 1) / 2)
                G = np.uint8(255 * (np.sin(2*np.pi*Z_norm + 2*np.pi/3) + 1) / 2)
                B = np.uint8(255 * (np.sin(2*np.pi*Z_norm + 4*np.pi/3) + 1) / 2)
                img_array = np.dstack((R, G, B))
                from PIL import Image
                img = Image.fromarray(img_array, 'RGB')
                upscaled = img.resize((canvas.winfo_width(), canvas.winfo_height()), Image.BILINEAR)
                photo = ImageTk.PhotoImage(upscaled)
                try:
                    plasma_queue.put(photo, timeout=0.01)
                except queue.Full:
                    pass
                time.sleep(0.05)
        plasma_thread = threading.Thread(target=compute_plasma, daemon=True)
        plasma_thread.start()
        def update_canvas():
            try:
                photo = plasma_queue.get_nowait()
                canvas.create_image(0, 0, image=photo, anchor=tk.NW)
                canvas.image = photo
            except queue.Empty:
                pass
            canvas.after(25, update_canvas)
        update_canvas()
        def on_close():
            stop_event.set()
            vis_win.destroy()
        vis_win.protocol("WM_DELETE_WINDOW", on_close)

if __name__ == "__main__":
    app = BackToTheJukebox()
    app.mainloop()
