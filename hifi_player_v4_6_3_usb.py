import os
import re
import time
import threading
from pathlib import Path
from mutagen.wave import WAVE
from mutagen.flac import FLAC
from mutagen.oggflac import OggFLAC

def extract_track_number(filename):
    """
    Extract track number from filename using improved regex pattern.
    Handles filenames like "7 Free Will.aiff", "15 This Is The Me Me.aiff", etc.
    """
    match = re.match(r'^(\d+)\D', filename)
    if match:
        try:
            return int(match.group(1))
        except (ValueError, IndexError):
            return float('inf')
    return float('inf')

class HiFiPlayerV463USB:
    """HiFi Audio Player for USB connected devices - Version 4.6.3"""
    
    def __init__(self, usb_mount_path=None):
        self.usb_mount_path = usb_mount_path or self._find_usb_mount()
        self.playlist = []
        self.current_index = 0
        self.is_playing = False
        self.lock = threading.Lock()
        
    def _find_usb_mount(self):
        """Automatically detect USB mount point"""
        common_paths = [
            '/media/usb0',
            '/media/usb',
            '/mnt/usb',
            '/mnt/usb0'
        ]
        for path in common_paths:
            if os.path.exists(path):
                return path
        return None
    
    def load_playlist(self, directory=None):
        """Load audio files from directory and sort by track number"""
        target_dir = directory or self.usb_mount_path
        
        if not target_dir or not os.path.isdir(target_dir):
            raise ValueError(f"Invalid directory: {target_dir}")
        
        supported_formats = ('.mp3', '.flac', '.wav', '.m4a', '.aiff', '.aif')
        files = [f for f in os.listdir(target_dir) 
                if f.lower().endswith(supported_formats)]
        
        # Sort by extracted track number
        files.sort(key=lambda x: extract_track_number(x))
        
        self.playlist = [os.path.join(target_dir, f) for f in files]
        return self.playlist
    
    def get_metadata(self, filepath):
        """Extract metadata from audio file"""
        ext = os.path.splitext(filepath)[1].lower()
        
        try:
            if ext == '.flac':
                audio = FLAC(filepath)
            elif ext == '.wav':
                audio = WAVE(filepath)
            else:
                return None
            
            return {
                'title': audio.get('title', ['Unknown'])[0],
                'artist': audio.get('artist', ['Unknown'])[0],
                'duration': int(audio.info.length) if audio.info else 0
            }
        except Exception as e:
            print(f"Error reading metadata: {e}")
            return None

if __name__ == "__main__":
    player = HiFiPlayerV463USB()
    playlist = player.load_playlist()
    print(f"Loaded {len(playlist)} tracks")
    for track in playlist:
        print(f"  - {os.path.basename(track)}")
