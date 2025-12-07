#!/usr/bin/env python3

# -*- coding: utf-8 -*-

"""
===============================================================================
Ultimate HiFi Audio Player v4.6.3 - Multi-Format + USB-DAC Support
===============================================================================

NEW FEATURES in v4.6.3:
✓ USB-DAC Direct Playback (soundfile-based, future-proof, NO aifc)
✓ Auto-Detection of iFi & Compatible USB DACs
✓ Mode Switching (UPnP Network ↔ USB Direct)
✓ Device Selection & Configuration
✓ Fallback Support (UPnP→USB when renderer unavailable)
✓ All v4.6.2 Features Preserved:
  - Multi-Format Support (MP3, FLAC, WAV, AIFF, M4A, DSF)
  - Intelligente Format-Erkennung
  - DIDL-Lite Metadaten mit Format-spezifischen protocolInfo-Varianten
  - Optionale Metadaten-Extraktion mit mutagen (ID3, MP4, Vorbis)
  - 4 Fallback-Varianten pro Format für DAC-Kompatibilität
  - 100% Backward-Kompatibilität mit v4.6.2

ARCHITEKTUR:
- Threading: Command Queue + 970ms Polling (Wireshark-validated)
- Format Config: Global AUDIO_FORMAT_CONFIG mit 6 Formate
- HTTP Streaming: Chunked, mit AIFF↔WAV Echtzeit-Konvertierung
- UPnP Discovery: SSDP mit automatischer Renderer-Erkennung
- USB Playback: soundfile-based (libsndfile), future-proof
- Interactive UI: Terminal-basiert mit Play All & Auto-Next + Mode Switching

INSTALLATION:
pip install sounddevice soundfile numpy tqdm
pip install mutagen  # Optional für Metadaten

VERWENDUNG (UPnP):
python3 hifi_player_v4_6_3_usb. py --dir /path/to/music/ [--debug]

VERWENDUNG (USB):
python3 hifi_player_v4_6_3_usb.py --dir /path/to/music/ --usb [--device 2] [--debug]

VERWENDUNG (List USB Devices):
python3 hifi_player_v4_6_3_usb.py --dir /path/to/music/ --list-devices

===============================================================================
"""

import argparse
import http.server
import mimetypes
import os
import socket
import socketserver
import threading
import time
import urllib.request
import urllib.parse
import xml.etree.ElementTree as ET
from urllib.parse import urljoin
from xml.sax.saxutils import escape
import soundfile as sf
import struct
import numpy as np
import sys
import sounddevice as sd
from tqdm import tqdm
from io import BytesIO
from queue import Queue, Empty
from dataclasses import dataclass
from enum import Enum
from collections import deque
#from usb_playback_engine import USBPlaybackEngine, USBCommandType

# Optional dependencies
try:
    import mutagen
    from mutagen.mp3 import MP3
    from mutagen.m4a import M4A
    from mutagen.flac import FLAC
    MUTAGEN_SUPPORT = True
except ImportError:
    MUTAGEN_SUPPORT = False
    print("[INFO] mutagen not installed - limited metadata support for MP3/M4A/FLAC")

# USB device queryability check
try:
    sd.query_devices()
    USB_DEVICES_QUERYABLE = True
except Exception:
    USB_DEVICES_QUERYABLE = False
    print("[INFO] USB device enumeration not available")

# =====================================================================
# SECTION 1: Audio Format Configuration (v4.6.2 BASE)
# =====================================================================

AUDIO_FORMAT_CONFIG = {
    "mp3": {
        "mime_types": ["audio/mpeg", "audio/mp3"],
        "protocol_info_variants": [
            "http-get:*:audio/mpeg:DLNA.ORG_PN=MP3",
            "http-get:*:audio/mpeg:DLNA.ORG_PN=MP3X",
            "http-get:*:audio/mp3:*",
            "http-get:*:audio/mpeg:*"
        ],
        "requires_metadata_extraction": True
    },
    "m4a": {
        "mime_types": ["audio/m4a", "audio/aac"],
        "protocol_info_variants": [
            "http-get:*:audio/m4a:DLNA.ORG_PN=AAC_ISO",
            "http-get:*:audio/aac:DLNA.ORG_PN=AAC_ISO",
            "http-get:*:audio/vnd.dlna.adts:DLNA.ORG_PN=AAC_ADTS",
            "http-get:*:audio/m4a:*"
        ],
        "requires_metadata_extraction": True
    },
    "flac": {
        "mime_types": ["audio/flac"],
        "protocol_info_variants": ["http-get:*:audio/flac:*"],
        "requires_metadata_extraction": True
    },
    "dsf": {
        "mime_types": ["audio/vnd.sony.dsf", "audio/dsf"],
        "protocol_info_variants": [
            "http-get:*:audio/vnd.sony.dsf:*",
            "http-get:*:audio/dsf:*"
        ],
        "requires_metadata_extraction": True
    },
    "wav": {
        "mime_types": ["audio/wav", "audio/x-wav"],
        "protocol_info_variants": [
            "http-get:*:audio/wav:DLNA.ORG_PN=LPCM",
            "http-get:*:audio/x-wav:DLNA.ORG_PN=LPCM",
            "http-get:*:audio/wav:*",
            "http-get:*:audio/x-wav:*"
        ],
        "requires_metadata_extraction": False
    },
    "aiff": {
        "mime_types": ["audio/aiff", "audio/x-aiff"],
        "protocol_info_variants": ["http-get:*:audio/wav:DLNA.ORG_PN=LPCM"],
        "requires_metadata_extraction": False
    }
}

# =====================================================================
# SECTION 1.5: USB-DAC Configuration (v4.6.3 NEW - soundfile based)
# =====================================================================

USB_DAC_CONFIG = {
    "auto_detect": True,
    "preferred_names": ["iFi", "Pro iDSD", "XMOS"],
    "fallback_to_usb": True,
    "usb_buffer_frames": 4096,
}

class PlaybackMode(Enum):
    """Playback mode enumeration"""
    UPNP_NETWORK = 1
    USB_DIRECT = 2

# USB_PLAYBACK_ENGINE.py
# Standalone USB Audio Playback Engine for hifi_player v4.6.3+
# Implements dedicated 3-thread architecture for USB DAC control
# Drop-in replacement for CommandWorkerThread when using --usb mode

import threading
import queue
import time
import os
import sounddevice as sd
import soundfile as sf
from enum import Enum

# =====================================================================
# USB Command Types
# =====================================================================

class USBCommandType(Enum):
    """USB-specific command types"""
    PLAY = 1
    NEXT = 2
    PREVIOUS = 3
    STOP = 4
    PLAY_ALL = 5
    PAUSE = 6
    QUIT = 7


# =====================================================================
# USB Playback Engine
# =====================================================================

class USBPlaybackEngine:
    """
    Dedicated USB audio engine with 3-thread architecture.
    
    Threads:
    1. Command Handler - processes user input commands
    2. Playback Worker - streams PCM data to USB DAC
    3. Status Poller - monitors position every 970ms (like UPnP)
    
    This is a completely separate implementation from UPnP CommandWorkerThread.
    """
    
    def __init__(self, audio_dir, device_idx, debug=False):
        """
        Initialize USB Playback Engine.
        
        Args:
            audio_dir: Directory containing audio files
            device_idx: sounddevice device index for USB DAC
            debug: Enable debug logging
        """
        self.audio_dir = audio_dir
        self.device_idx = device_idx
        self.debug = debug
        
        # Scan audio files
        self.files = self._list_audio_files()
        if not self.files:
            raise ValueError(f"No audio files found in {audio_dir}")
        
        # Internal playback state (isolated from UPnP)
        self.current_track_idx = 0
        self.is_playing = False
        self.is_paused = False
        self.play_all_enabled = False
        self.transport_state = 'STOPPED'  # STOPPED, PLAYING, PAUSED
        self.current_position = 0.0
        self.track_duration = 0.0
        self.track_start_time = None
        self.track_start_position = 0.0
        
        # Threading components
        self.command_thread = None
        self.playback_thread = None
        self.status_thread = None
        self.running = True
        
        # Queues and events
        self.command_queue = queue.Queue()
        self.stop_event = threading.Event()
        self.pause_event = threading.Event()
        
        # Lock for thread-safe state updates
        self.state_lock = threading.RLock()
    
    def _list_audio_files(self):
        """List all supported audio files in directory"""
        supported_exts = {'.wav', '.aiff', '.aif', '.flac', '.mp3', '.m4a', '.aac', '.dsf'}
        
        files = []
        try:
            for f in sorted(os.listdir(self.audio_dir)):
                if os.path.splitext(f)[1].lower() in supported_exts:
                    files.append(f)
        except Exception as e:
            if self.debug:
                print(f"[USBEngine] Error listing files: {e}")
        
        return files
    
    def start(self):
        """Start all 3 threads"""
        if self.debug:
            print("[USBEngine] Starting playback engine...")
        
        print("[USBEngine] Starting command handler thread...")
        self.command_thread = threading.Thread(
            target=self._command_handler_loop,
            daemon=True,
            name="USB-CommandHandler"
        )
        self.command_thread.start()
        
        print("[USBEngine] Starting status poller thread (970ms interval)...")
        self.status_thread = threading.Thread(
            target=self._status_poller_loop,
            daemon=True,
            name="USB-StatusPoller"
        )
        self.status_thread.start()
        
        if self.debug:
            print("[USBEngine] All threads started")
            
    def _command_handler_loop(self):
        """
        Thread 1: Process commands from UI.
        
        Commands:
        - PLAY: Start playback of specific track
        - NEXT: Skip to next track
        - PREVIOUS: Go back to previous track
        - STOP: Stop playback
        - PAUSE: Pause playback
        - PLAY_ALL: Queue all tracks starting from index
        - QUIT: Shutdown engine
        """
        if self.debug:
            print("[USBEngine-CMD] Handler loop started")
        
        while self.running:
            try:
                cmd = self.command_queue.get(timeout=0.5)
                
                if cmd['type'] == USBCommandType.PLAY:
                    track_idx = cmd.get('track_idx', self.current_track_idx)
                    self._do_play(track_idx)
                
                elif cmd['type'] == USBCommandType.NEXT:
                    self._do_next()
                
                elif cmd['type'] == USBCommandType.PREVIOUS:
                    self._do_previous()
                
                elif cmd['type'] == USBCommandType.STOP:
                    self._do_stop()
                
                elif cmd['type'] == USBCommandType.PAUSE:
                    self._do_pause()
                
                elif cmd['type'] == USBCommandType.PLAY_ALL:
                    start_idx = cmd.get('start_idx', 0)
                    self._do_play_all(start_idx)
                
                elif cmd['type'] == USBCommandType.QUIT:
                    self._do_stop()
                    self.running = False
                    if self.debug:
                        print("[USBEngine-CMD] Quit command received, exiting loop")
                    break
            
            except queue.Empty:
                continue
            except Exception as e:
                print(f"[USBEngine-CMD] Error: {e}")
    
    def _do_play(self, track_idx):
        """Play a specific track"""
        with self.state_lock:
            if track_idx < 0 or track_idx >= len(self.files):
                print(f"[USBEngine] Invalid track index: {track_idx}")
                return
            
            filename = self.files[track_idx]
            filepath = os.path.join(self.audio_dir, filename)
            
            # Stop any existing playback
            self._do_stop()
            time.sleep(0.1)
            
            # Update state
            self.current_track_idx = track_idx
            self.is_playing = True
            self.is_paused = False
            self.transport_state = 'PLAYING'
            self.track_start_time = time.time()
            self.track_start_position = 0.0
            self.current_position = 0.0
            
            # Get format info
            format_type = self._get_format_from_extension(filename)
            fmt = format_type.upper() if format_type else '?'
            
            print(f"[USBEngine] Playing: {filename} [{fmt}]")
            
            # Start playback in separate thread (CRITICAL - non-blocking!)
            self.stop_event.clear()
            self.pause_event.clear()
            
            self.playback_thread = threading.Thread(
                target=self._playback_worker,
                args=(filepath, track_idx),
                daemon=True,
                name=f"USB-Playback-{track_idx}"
            )
            self.playback_thread.start()
    
    def _do_next(self):
        """Play next track"""
        with self.state_lock:
            if self.current_track_idx >= len(self.files) - 1:
                print("[USBEngine] Already at last track")
                return
            
            if self.debug:
                print("[USBEngine-CMD] Next track")
            
            next_idx = self.current_track_idx + 1
            self._do_play(next_idx)
    
    def _do_previous(self):
        """Play previous track"""
        with self.state_lock:
            if self.current_track_idx <= 0:
                print("[USBEngine] Already at first track")
                return
            
            if self.debug:
                print("[USBEngine-CMD] Previous track")
            
            prev_idx = self.current_track_idx - 1
            self._do_play(prev_idx)
    
    def _do_stop(self):
        """Stop playback"""
        with self.state_lock:
            if self.debug:
                print("[USBEngine-CMD] Stop")
            
            self.stop_event.set()
            self.pause_event.clear()
            
            try:
                sd.stop()
            except:
                pass
            
            self.is_playing = False
            self.is_paused = False
            self.transport_state = 'STOPPED'
            self.current_position = 0.0
            self.track_start_time = None
    
    def _do_pause(self):
        """Pause playback"""
        with self.state_lock:
            if not self.is_playing or self.is_paused:
                return
            
            if self.debug:
                print("[USBEngine-CMD] Pause")
            
            self.pause_event.set()
            self.is_paused = True
            self.transport_state = 'PAUSED'
    
    def _do_play_all(self, start_idx):
        """Start Play All from specific track"""
        with self.state_lock:
            if start_idx < 0 or start_idx >= len(self.files):
                start_idx = 0
            
            if self.debug:
                print(f"[USBEngine-CMD] Play All from track {start_idx + 1}")
            
            self.play_all_enabled = True
            self._do_play(start_idx)
            
    def _playback_worker(self, filepath, track_idx):
        """
        Thread 2: Stream PCM data to USB DAC.
        
        This is a long-running thread that:
        - Reads audio file
        - Plays to USB DAC
        - Monitors for stop/pause events
        - Detects track end
        - Triggers auto-next for Play All
        """
        if self.debug:
            print(f"[USBEngine-PB] Worker started for track {track_idx}: {os.path.basename(filepath)}")
        
        try:
            
            devices = sd.query_devices()
            if self.device_idx < 0 or self.device_idx >= len(devices):
                print(f"[USBEngine-PB] âœ— Device {self.device_idx} not available")
                with self.state_lock:
                    self.is_playing = False
                    self.transport_state = 'STOPPED'
                return
            try:
                # Try soundfile first (WAV, FLAC, DSF, AIFF)
                data, sr = sf.read(filepath, dtype='float32')
                if self.debug:
                    print(f"[USBEngine-PB] Read with soundfile")
            
            except Exception as sf_error:
                # soundfile failed - try librosa for M4A/AAC/MP3
                if filepath.lower().endswith(('.m4a', '.aac', '.mp3')):
                    try:
                        import librosa
                        if self.debug:
                            print(f"[USBEngine-PB] soundfile failed, trying librosa")
                        
                        data, sr = librosa.load(filepath, sr=None, mono=False, dtype='float32')
                        if len(data.shape) == 1:
                            data = data.reshape(1, -1)  # Convert mono to (1, samples)
                        if data.shape[0] > 2:
                            data = data[:2, :]  # Limit to max 2 channels
                        if self.debug:
                            print(f"[USBEngine-PB] Read with librosa")
                    
                    except ImportError:
                        print(f"[USBEngine-PB] âœ— librosa not installed: pip install librosa")
                        with self.state_lock:
                            self.is_playing = False
                            self.transport_state = 'STOPPED'
                        return
                    
                    except Exception as e:
                        print(f"[USBEngine-PB] âœ— librosa error: {e}")
                        with self.state_lock:
                            self.is_playing = False
                            self.transport_state = 'STOPPED'
                        return
                else:
                    print(f"[USBEngine-PB] âœ— soundfile error: {sf_error}")
                    with self.state_lock:
                        self.is_playing = False
                        self.transport_state = 'STOPPED'
                    return
            
            with self.state_lock:
                self.track_duration = len(data) / sr
                if self.debug:
                    channels = 1 if len(data.shape) == 1 else data.shape[1]
                    print(f"[USBEngine-PB] Format: {sr}Hz, {channels}ch, {self.track_duration:.1f}s")
                    
            
            
            device_info = devices[self.device_idx]
            if self.debug:
                print(f"[USBEngine-PB] Device: {device_info['name']}")
            
            # Set device and play
            sd.default.device = self.device_idx
            
            if self.debug:
                print(f"[USBEngine-PB] Starting playback at {sr}Hz")
            
            sd.play(data, samplerate=sr, device=self.device_idx)
            
            
            last_is_playing = True
            
            duration = len(data) / sr
            starttime = time.time()
            while time.time() - starttime < duration and not self.stopevent.isset():
                # Update position and check for pause/stop
                elapsed = time.time() - starttime
                self.currentposition = self.trackstartposition + elapsed
                # Update position
                with self.state_lock:
                    if self.track_start_time:
                        elapsed = time.time() - self.track_start_time
                        self.current_position = self.track_start_position + elapsed
                    
                    # Handle pause
                    if self.pauseevent.is_set() and self.transport_state == 'PLAYING':
                        sd.stop()
                        self.transport_state = 'PAUSED'
                        last_is_playing = False
                    
                    elif not self.pauseevent.is_set() and not last_is_playing:
                        # Resume from pause
                        remaining_data = data[int(self.current_position * sr):]
                        if len(remaining_data) > 0:
                            sd.play(remaining_data, samplerate=sr, device=self.device_idx)
                            self.track_start_time = time.time()
                            self.track_start_position = self.current_position
                            self.transport_state = 'PLAYING'
                            last_is_playing = True
                
                time.sleep(0.05)  # Check every 50ms for responsiveness
            
            
            
            with self.state_lock:
                if self.stopevent.is_set():
                    sd.stop()
                    if self.debug:
                        print(f"[USBEngine-PB] Stopped by command")
                    self.is_playing = False
                    self.transport_state = 'STOPPED'
                
                else:
                    # Playback finished naturally
                    if self.debug:
                        print(f"[USBEngine-PB] âœ“ Playback finished")
                    
                    self.is_playing = False
                    self.transport_state = 'STOPPED'
                    self.current_position = self.track_duration
                    
                    # Auto-next if Play All enabled
                    if self.play_all_enabled and track_idx < len(self.files) - 1:
                        if self.debug:
                            print(f"[USBEngine-PB] Auto-next to track {track_idx + 2}")
                        
                        # Enqueue next track
                        self.command_queue.put({
                            'type': USBCommandType.PLAY,
                            'track_idx': track_idx + 1
                        })
                    else:
                        # Play All finished or single track ended
                        if self.play_all_enabled:
                            print(f"[USBEngine-PB] Play All finished")
                            self.play_all_enabled = False
        
        except Exception as e:
            print(f"[USBEngine-PB] âœ— Playback worker error: {e}")
            with self.state_lock:
                self.is_playing = False
                self.transport_state = 'STOPPED'
    
    
    def _status_poller_loop(self):
        """
        Thread 3: Poll status every 970ms.
        
        This mirrors UPnP's polling thread, ensuring UI updates at regular intervals.
        """
        if self.debug:
            print("[USBEngine-POLL] Status poller started (970ms interval)")
        
        while self.running:
            try:
                time.sleep(0.97)
                
                with self.state_lock:
                    if self.debug and self.is_playing:
                        print(f"[USBEngine-POLL] Track {self.current_track_idx + 1}: "
                              f"{self.current_position:.1f}s / {self.track_duration:.1f}s "
                              f"({self.transport_state})")
            
            except Exception as e:
                print(f"[USBEngine-POLL] Error: {e}")
    
    
    
    def enqueue_command(self, cmd_type, **kwargs):
        """
        Public API to enqueue commands (called by UI).
        
        Args:
            cmd_type: USBCommandType enum value
            **kwargs: Additional command arguments (e.g., track_idx)
        """
        cmd = {'type': cmd_type, **kwargs}
        self.command_queue.put(cmd)
    
    def get_state(self):
        """
        Get current playback state (thread-safe).
        
        Returns:
            dict with current state for UI display
        """
        with self.state_lock:
            return {
                'current_track_idx': self.current_track_idx,
                'track_name': self.files[self.current_track_idx] if self.current_track_idx < len(self.files) else "",
                'is_playing': self.is_playing,
                'is_paused': self.is_paused,
                'transport_state': self.transport_state,
                'position': self.current_position,
                'duration': self.track_duration,
                'play_all': self.play_all_enabled,
                'total_tracks': len(self.files),
                'files': self.files,
            }
    
    def stop_all(self):
        """Stop everything and shut down"""
        self.enqueue_command(USBCommandType.QUIT)
        self.running = False
        
        # Wait for threads to finish
        if self.playback_thread:
            self.playback_thread.join(timeout=2.0)
        if self.command_thread:
            self.command_thread.join(timeout=2.0)
        if self.status_thread:
            self.status_thread.join(timeout=2.0)
    
    def _get_format_from_extension(self, filename):
        """Get audio format from file extension"""
        ext = os.path.splitext(filename)[1].lower()
        
        format_map = {
            '.mp3': 'mp3',
            '.m4a': 'm4a',
            '.aac': 'm4a',
            '.flac': 'flac',
            '.dsf': 'dsf',
            '.wav': 'wav',
            '.aif': 'aiff',
            '.aiff': 'aiff'
        }
        
        return format_map.get(ext, None)
# =====================================================================
# SECTION 2: Threading Architecture (v4.6.1 + v4.6.2 enhancements)
# =====================================================================

class CommandType(Enum):
    """User command types"""
    PLAY = 1
    PAUSE = 2
    STOP = 3
    NEXT = 4
    PREVIOUS = 5
    SET_TRACK = 6
    QUIT = 7

@dataclass
class Command:
    """Command with timestamp for debouncing"""
    type: CommandType
    args: dict = None
    timestamp: float = None

    def __post_init__(self):
        if self.timestamp is None:
            self.timestamp = time.time()

class SharedState:
    """Thread-safe shared state with Play All support + USB mode"""

    def __init__(self):
        self._lock = threading.Lock()
        self.state = {
            'position': 0,
            'duration': 0,
            'is_playing': False,
            'current_track_idx': 0,
            'current_track_name': '',
            'transport_state': 'STOPPED',
            'last_update': 0,
            'error': None,
            'play_all_enabled': False,
            'play_all_start_idx': 0,
            'last_position': 0,
            'total_tracks': 0,
            'track_started': False,
            'track_start_time': 0,
            # USB-specific state
            'playback_mode': PlaybackMode. UPNP_NETWORK,
            'usb_device_index': None,
            'usb_device_name': '',
        }

    def get(self, key):
        with self._lock:
            return self.state.get(key)

    def set(self, key, value):
        with self._lock:
            self. state[key] = value

    def update(self, updates_dict):
        with self._lock:
            self.state.update(updates_dict)

    def get_all(self):
        with self._lock:
            return self.state.copy()

class DebouncedQueue:
    """Queue with debouncing for rapid user input"""

    def __init__(self, debounce_ms=100):
        self.queue = deque()
        self.debounce_ms = debounce_ms / 1000.0
        self.last_command_time = 0
        self._lock = threading.Lock()

    def put(self, command):
        with self._lock:
            now = time.time()
            if (self.queue and
                self.queue[-1].type == command.type and
                now - self.last_command_time < self.debounce_ms):
                return

            self.queue.append(command)
            self.last_command_time = now

    def get(self, block=True, timeout=None):
        start_time = time.time()
        while True:
            with self._lock:
                if self.queue:
                    return self.queue.popleft()

            if not block:
                raise Empty

            if timeout and (time.time() - start_time) >= timeout:
                raise Empty

            time.sleep(0.01)

# Global instances
SHARED_STATE = SharedState()
COMMAND_QUEUE = DebouncedQueue(debounce_ms=100)

# =====================================================================
# SECTION 3: Audio Format Utilities (v4.6.2 BASE)
# =====================================================================

def get_format_from_extension(filename):
    """Detect audio format from file extension"""
    ext = os.path.splitext(filename)[1].lower()
    ext_map = {
        '.mp3': 'mp3',
        '.m4a': 'm4a',
        '.aac': 'm4a',
        '.flac': 'flac',
        '.dsf': 'dsf',
        '.wav': 'wav',
        '.aif': 'aiff',
        '.aiff': 'aiff'
    }
    return ext_map.get(ext, None)

def extract_metadata(filepath):
    """Extract metadata from audio file using mutagen (v4.6.2 NEW)"""
    if not MUTAGEN_SUPPORT:
        return None
    
    try:
        audio = mutagen.File(filepath)
        if audio is None:
            return None
        
        metadata = {
            'duration': float(audio.info.length) if hasattr(audio.info, 'length') else 0,
            'title': str(audio.get('TIT2', audio.get('title', 'Unknown'))).strip('[]'),
            'album': str(audio.get('TALB', audio.get('album', 'Unknown'))).strip('[]'),
            'artist': str(audio.get('TPE1', audio.get('artist', 'Unknown'))).strip('[]'),
        }
        return metadata
    except Exception:
        return None

def format_duration(seconds):
    """Format seconds to HH:MM:SS.mmm (v4.6.2 NEW)"""
    if seconds <= 0:
        return "0:00:00.000"
    hours = int(seconds // 3600)
    minutes = int((seconds % 3600) // 60)
    secs = seconds % 60
    return f"{hours}:{minutes:02d}:{secs:06.3f}"

def get_file_size(filepath):
    """Get file size in bytes (v4.6.2 NEW)"""
    try:
        return os.path.getsize(filepath)
    except Exception:
        return 0

def get_protocol_info_for_format(format_type, index=0):
    """Get protocolInfo for given format (with fallback variants) (v4.6.2 NEW)"""
    if format_type not in AUDIO_FORMAT_CONFIG:
        return None
    
    variants = AUDIO_FORMAT_CONFIG[format_type]['protocol_info_variants']
    if index < len(variants):
        return variants[index]
    return variants[-1] if variants else None

def get_mime_type_for_format(format_type):
    """Get primary MIME type for format (v4.6.2 NEW)"""
    if format_type not in AUDIO_FORMAT_CONFIG:
        return "application/octet-stream"
    
    mime_types = AUDIO_FORMAT_CONFIG[format_type]['mime_types']
    return mime_types[0] if mime_types else "application/octet-stream"

# =====================================================================
# SECTION 3.5: USB-DAC Detection & Playback (v4.6.3 NEW - soundfile based)
# =====================================================================

def list_usb_dacs(debug=False):
    """List all available USB audio output devices (soundfile compatible)"""
    if not USB_DEVICES_QUERYABLE:
        return []
    
    try:
        devices = sd.query_devices()
        dacs = []
        
        for idx, device in enumerate(devices):
            if device['max_output_channels'] >= 2:
                dac_info = {
                    'index': idx,
                    'name': device['name'],
                    'channels': device['max_output_channels'],
                    'sample_rate': int(device['default_samplerate']),
                    'hostapi': sd.query_hostapis(device['hostapi'])['name']
                }
                dacs.append(dac_info)
                if debug:
                    print(f"[USB] Device {idx}: {device['name']}")
        
        return dacs
    except Exception as e:
        if debug:
            print(f"[USB] Error querying devices: {e}")
        return []

def find_ifi_dac(debug=False):
    """Auto-detect iFi or compatible DAC (soundfile compatible)"""
    try:
        devices = sd.query_devices()
        preferred_keywords = USB_DAC_CONFIG.get("preferred_names", [])
        
        # First pass: exact match on preferred names
        for idx, device in enumerate(devices):
            name_lower = device['name'].lower()
            for keyword in preferred_keywords:
                if keyword. lower() in name_lower:
                    if debug:
                        print(f"[USB] Found: {device['name']} at index {idx}")
                    return idx, device
        
        # Fallback: any stereo+ output device (skip defaults)
        for idx, device in enumerate(devices):
            if (device['max_output_channels'] >= 2 and 
                'default' not in device['name']. lower() and
                'built' not in device['name'].lower()):
                if debug:
                    print(f"[USB] Auto-fallback: {device['name']} at index {idx}")
                return idx, device
        
        return None, None
    except Exception as e:
        if debug:
            print(f"[USB] DAC detection error: {e}")
        return None, None

def play_audio_usb(filepath, device_idx, debug=False):
    """
    Play audio file through USB DAC with native sample rate.
    Uses soundfile for file reading (supports all formats).
    Uses sounddevice for playback with explicit device selection.
    """
    try:
        import soundfile as sf
        import sounddevice as sd
        
        if debug:
            print(f"[USB] Reading: {filepath}")
        
        # soundfile reads ANY format (WAV, AIFF, FLAC, M4A, MP3, DSF, etc.)
        try:
            # Try soundfile first (WAV, FLAC, DSF, AIFF supported)
            data, samplerate = sf.read(filepath, dtype='float32')
            if debug:
                print(f"[USB] Read with soundfile")
        
        except Exception as sf_error:
            # soundfile failed - try librosa for M4A/AAC support
            if filepath.lower().endswith(('.m4a', '.aac', '.mp3')):
                try:
                    import librosa
                    print(f"[USB] soundfile failed, using librosa for M4A/AAC/MP3")
                    
                    # librosa returns (data, sr) like soundfile
                    data, samplerate = librosa.load(filepath, sr=None, mono=False, dtype='float32')
                    
                    if debug:
                        print(f"[USB] Read with librosa")
                
                except ImportError:
                    print(f"[USB] âœ— M4A not supported: install librosa")
                    print(f"[USB] pip install librosa")
                    return False
                
                except Exception as librosa_error:
                    if debug:
                        print(f"[USB] âœ— librosa error: {librosa_error}")
                    return False
            else:
                # Not M4A and soundfile failed
                if debug:
                    print(f"[USB] âœ— soundfile error: {sf_error}")
                return False
        
        if debug:
            channels = 1 if len(data.shape) == 1 else data.shape[1]
            print(f"[USB] Format detected:")
            print(f"  Sample rate: {samplerate} Hz")
            print(f"  Channels: {channels}")
        
        # Check if device exists and is valid
        devices = sd.query_devices()
        if device_idx < 0 or device_idx >= len(devices):
            print(f"[USB] âœ— Device index {device_idx} not available")
            return False
        
        device_info = devices[device_idx]
        
        if debug:
            print(f"[USB] Using device: {device_info['name']}")
            print(f"  Max output channels: {device_info['max_output_channels']}")
            print(f"  Default sample rate: {device_info['default_samplerate']} Hz")
        
        
        # Set the device explicitly (CRITICAL for USB)
        sd.default.device = device_idx
        
        
        try:
            if debug:
                print(f"[USB] Starting playback at {samplerate} Hz...")
            
            # Play using file's native sample rate - CRITICAL!
            stream = sd.play(data, samplerate=samplerate, device=device_idx)
            
            # Wait for playback to complete
            sd.wait()
            
            if debug:
                print(f"[USB] âœ“ Playback complete")
            
            return True
        
        except RuntimeError as e:
            if debug:
                print(f"[USB] âœ— Playback error: {e}")
            return False
        
        except Exception as e:
            if debug:
                print(f"[USB] âœ— Unexpected error: {e}")
            return False
    
    except ImportError as e:
        print(f"[USB] âœ— Missing library: {e}")
        print(f"[USB] Install with: pip install soundfile sounddevice")
        return False
    
    except Exception as e:
        if debug:
            print(f"[USB] âœ— File read error: {e}")
        return False

def play_aiff_via_usb(filepath, device_index=None, debug=False):
    """
    Play AIFF file via USB-DAC using soundfile (NO aifc - future-proof). 
    
    soundfile handles AIFF natively via libsndfile, automatically converting
    big-endian AIFF to PCM for USB output.
    """
    if not USB_DEVICES_QUERYABLE:
        print("[USB] USB playback not available")
        return False
    
    try:
        SHARED_STATE.update({
            'is_playing': True,
            'transport_state': 'PLAYING',
            'track_started': True,
            'track_start_time': time.time()
        })
        
        # soundfile automatically handles AIFF→PCM conversion via libsndfile
        info = sf.info(filepath)
        
        if debug:
            print(f"[USB AIFF] {info. channels}ch, {info.samplerate}Hz, {info.frames} frames")
            print(f"[USB AIFF] Format: {info.format}, Subtype: {info.subtype}")
        
        # Read AIFF file - soundfile handles all conversion automatically
        with sf.SoundFile(filepath, 'r') as f:
            # Stream in chunks to avoid loading entire file in memory
            chunk_frames = USB_DAC_CONFIG.get('usb_buffer_frames', 4096)
            
            with sd.OutputStream(
                samplerate=f.samplerate,
                channels=f.channels,
                device=device_index,
                dtype='float32'
            ) as stream:
                frames_read = 0
                while True:
                    if not SHARED_STATE.get('is_playing'):
                        SHARED_STATE.set('is_playing', False)
                        return False
                    
                    # soundfile read() automatically converts AIFF→float32 PCM
                    data = f.read(chunk_frames)
                    
                    if len(data) == 0:
                        break
                    
                    stream.write(data)
                    frames_read += len(data)
        
        SHARED_STATE.set('is_playing', False)
        if debug:
            print(f"[USB AIFF] Finished playback: {frames_read} frames")
        return True
        
    except Exception as e:
        if debug:
            print(f"[USB AIFF] Playback error: {e}")
        SHARED_STATE.update({'is_playing': False, 'error': str(e)})
        return False

# =====================================================================
# SECTION 4: DIDL-Lite Metadata Functions (v4.6.1 compatible, v4.6.2 enhanced)
# =====================================================================

def build_didl_with_size(url, title, protocol_info, size=None):
    """Build DIDL-Lite XML metadata"""
    title_escaped = escape(title or "Track")
    size_attr = f' size="{int(size)}"' if isinstance(size, (int, float)) and size > 0 else ''
    didl_open = '<DIDL-Lite xmlns:dc="http://purl.org/dc/elements/1.1/" xmlns:upnp="urn:schemas-upnp-org:metadata-1-0/upnp/" xmlns="urn:schemas-upnp-org:metadata-1-0/DIDL-Lite/">'
    item_open = '<item id="0" parentID="0">'
    title_elem = f'<dc:title>{title_escaped}</dc:title>'
    class_elem = '<upnp:class>object.item.audioItem.musicTrack</upnp:class>'
    res_elem = f'<res protocolInfo="{protocol_info}"{size_attr}>{escape(url)}</res>'
    item_close = '</item>'
    didl_close = '</DIDL-Lite>'
    return f'{didl_open}\n{item_open}\n{title_elem}\n{class_elem}\n{res_elem}\n{item_close}\n{didl_close}'

def minimal_protocol_info(mime):
    """Minimal protocolInfo for DIDL"""
    return f'http-get:*:{mime}:*'

def protocol_info_wav_lpcm(alt_x=False):
    """Full protocolInfo for WAV/LPCM with DLNA flags"""
    mime = 'audio/x-wav' if alt_x else 'audio/wav'
    flags = 'DLNA. ORG_PN=LPCM'
    return mime, f'http-get:*:{mime}:{flags}'

def filesize_bytes_aiff_as_wav(directory, filename):
    """Calculate expected WAV file size for AIFF conversion"""
    try:
        full_path = os.path.join(directory, filename)
        ext = os.path.splitext(filename)[1].lower()
        if ext in ('.aif', '.aiff'):
            with sf.SoundFile(full_path, 'r') as af:
                nch = af.channels
                nf = af.frames
                subtype = (af.subtype or '').upper()
                if 'FLOAT' in subtype:
                    out_sw = 4
                elif '24' in subtype:
                    out_sw = 3
                elif '32' in subtype:
                    out_sw = 4
                else:
                    out_sw = 2
                return 44 + (nf * nch * out_sw)
        else:
            return os.path. getsize(full_path)
    except Exception:
        return None
    
def filesize_bytes_m4a_as_wav(directory, filename):
    """Calculate expected WAV file size for M4A/AAC conversion"""
    try:
        full_path = os.path.join(directory, filename)
        ext = os.path.splitext(filename)[1].lower()
        if ext in ('.m4a', '.aac'):
            with sf.SoundFile(full_path, 'r') as af:
                nch = af.channels
                nf = af.frames
                # M4A/AAC typically converts to 16-bit PCM WAV
                out_sw = 2  # 16-bit = 2 bytes
                return 44 + (nf * nch * out_sw)
        else:
            return os.path.getsize(full_path)
    except Exception:
        return None

# =====================================================================
# SECTION 5: SOAP/UPnP Functions (v4.6.1 + v4.6.2 multi-format logic)
# =====================================================================

def send_soap_request(control_url, soap_body, action, debug=False, timeout=10, retries=3, backoff=0.75):
    """Send SOAP request with retry logic"""
    headers = {
        'Content-Type': 'text/xml; charset="utf-8"',
        'SOAPAction': f'"{action}"',
    }

    for attempt in range(retries):
        try:
            req = urllib.request.Request(control_url, data=soap_body.encode('utf-8'), headers=headers)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return True, resp.read().decode('utf-8')
        except Exception as e:
            if debug:
                print(f"[SOAP] Attempt {attempt+1}/{retries} failed: {e}")
            if attempt < retries - 1:
                time.sleep(backoff * (attempt + 1))
    
    return False, None

def stop_upnp(control_url, debug=False):
    """Stop UPnP playback"""
    body = '<InstanceID>0</InstanceID>'
    envelope = f'<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/"><s:Body><u:Stop xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">{body}</u:Stop></s:Body></s:Envelope>'
    action = "urn:schemas-upnp-org:service:AVTransport:1#Stop"
    ok, _ = send_soap_request(control_url, envelope, action, debug=debug, timeout=10, retries=1, backoff=0.5)
    return ok

def pause_upnp(control_url, debug=False):
    """Pause UPnP playback"""
    body = '<InstanceID>0</InstanceID>'
    envelope = f'<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/"><s:Body><u:Pause xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">{body}</u:Pause></s:Body></s:Envelope>'
    action = "urn:schemas-upnp-org:service:AVTransport:1#Pause"
    ok, _ = send_soap_request(control_url, envelope, action, debug=debug, timeout=10, retries=1, backoff=0.5)
    return ok

def play_upnp(control_url, debug=False):
    """Play UPnP"""
    body = '<InstanceID>0</InstanceID><Speed>1</Speed>'
    soap_body = f'<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/"><s:Body><u:Play xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">{body}</u:Play></s:Body></s:Envelope>'
    action = "urn:schemas-upnp-org:service:AVTransport:1#Play"
    try:
        ok, _ = send_soap_request(control_url, soap_body, action, debug, timeout=20)
        return ok
    except Exception as e:
        if debug:
            print(f"[SOAP ERROR Play] {e}")
        return False

def get_position_info(control_url, debug=False):
    """Get current position info (Wireshark: called every ~970ms)"""
    body = '<InstanceID>0</InstanceID>'
    envelope = f'<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/"><s:Body><u:GetPositionInfo xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">{body}</u:GetPositionInfo></s:Body></s:Envelope>'
    action = "urn:schemas-upnp-org:service:AVTransport:1#GetPositionInfo"
    try:
        ok, resp = send_soap_request(control_url, envelope, action, debug, timeout=10)
        if ok and resp:
            try:
                root = ET.fromstring(resp)
                rel_time_elem = root.find('.//RelTime')
                track_duration_elem = root.find('.//TrackDuration')
                rel_time = rel_time_elem.text if rel_time_elem is not None else '0:00:00'
                track_duration = track_duration_elem.text if track_duration_elem is not None else '0:00:00'
                
                def time_to_seconds(time_str):
                    try:
                        parts = time_str.split(':')
                        if len(parts) == 3:
                            h, m, s = parts
                            return int(h) * 3600 + int(m) * 60 + float(s)
                    except:
                        pass
                    return 0
                
                return True, {
                    'position': time_to_seconds(rel_time),
                    'duration': time_to_seconds(track_duration)
                }
            except Exception as e:
                if debug:
                    print(f"[GetPositionInfo] Parse error: {e}")
                return False, None
    except Exception as e:
        if debug:
            print(f"[GetPositionInfo] Error: {e}")
        return False, None

def set_avtransport_uri(control_url, url, metadata, debug=False):
    """Set AVTransport URI with DIDL metadata"""
    body = f'<InstanceID>0</InstanceID><CurrentURI>{escape(url)}</CurrentURI><CurrentURIMetaData>{escape(metadata)}</CurrentURIMetaData>'
    envelope = f'<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/"><s:Body><u:SetAVTransportURI xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">{body}</u:SetAVTransportURI></s:Body></s:Envelope>'
    action = "urn:schemas-upnp-org:service:AVTransport:1#SetAVTransportURI"
    ok, _ = send_soap_request(control_url, envelope, action, debug=debug, timeout=30, retries=3, backoff=0.75)
    return ok

def set_avtransport_uri_variants(avtransport_url, url, filename, directory, actual_filename, debug=False):
    """Try multiple DIDL variants for DAC compatibility - v4.6.2 multi-format version (ENHANCED)"""
    try:
        stop_upnp(avtransport_url, debug=debug)
    except Exception:
        pass

    time.sleep(0.8)

    ext = os.path.splitext(actual_filename)[1]. lower()
    if ext in ('.m4a', '.aac'):
        sz = filesize_bytes_m4a_as_wav(directory, actual_filename)
    else:
        sz = filesize_bytes_aiff_as_wav(directory, actual_filename)

    format_type = get_format_from_extension(filename)
    
    attempts = []
    
    # For MP3, M4A, FLAC, DSF: use format-specific variants (v4.6.2 ENHANCED)
    if format_type in ('mp3', 'm4a', 'flac', 'dsf'):
        filesize = get_file_size(os.path.join(directory, actual_filename))
        metadata_dict = extract_metadata(os.path.join(directory, actual_filename)) if AUDIO_FORMAT_CONFIG.get(format_type, {}).get('requires_metadata_extraction', False) else None
        
        # Add format-specific DIDL variants
        protocol_variants = AUDIO_FORMAT_CONFIG.get(format_type, {}).get('protocol_info_variants', [])
        for idx, proto in enumerate(protocol_variants):
            title = filename
            didl = build_didl_with_size(url, title, proto, filesize)
            attempts.append((f'didl_{format_type}_v{idx}', didl))
    
    # For WAV/AIFF: use original logic (unchanged from v4.6.1)
    elif ext in ('.wav', '.aif', '.aiff'):
        attempts.append(('didl_min_wav', build_didl_with_size(url, filename, minimal_protocol_info('audio/wav'), sz)))
        attempts.append(('didl_min_xwav', build_didl_with_size(url, filename, minimal_protocol_info('audio/x-wav'), sz)))
        pi_wav = protocol_info_wav_lpcm(alt_x=False)
        pi_xwav = protocol_info_wav_lpcm(alt_x=True)
        attempts.append(('didl_lpcm_wav', build_didl_with_size(url, filename, pi_wav[1], sz)))
        attempts.append(('didl_lpcm_xwav', build_didl_with_size(url, filename, pi_xwav[1], sz)))
    else:
        base_mime = 'audio/mpeg' if ext == '.mp3' else 'application/octet-stream'
        attempts.append(('didl_min_generic', build_didl_with_size(url, filename, minimal_protocol_info(base_mime), sz)))

    # NOW try all attempts
    for i, (label, meta) in enumerate(attempts, 1):
        if debug:
            print(f"[SetAVTransportURI] Attempt {i}/{len(attempts)}: {label} (format={format_type})")
        
        ok = set_avtransport_uri(avtransport_url, url, meta, debug=debug)
        if ok:
            if debug:
                print(f"[SetAVTransportURI] ✓ Success with variant: {label}")
            return True
        
        time.sleep(1.0)

    return False

# =====================================================================
# SECTION 6: Polling Thread (v4.6.1, unchanged)
# =====================================================================

class PollingThread(threading.Thread):
    """Polls GetPositionInfo every 970ms with auto-next detection"""

    def __init__(self, control_url, interval_ms=970, debug=False):
        super().__init__(daemon=True)
        self.control_url = control_url
        self.interval = interval_ms / 1000.0
        self.running = True
        self.debug = debug
        self.paused = False

    def run(self):
        """Polling thread (970ms interval) - ONLY for UPnP mode"""
        while self.running:
            try:
                playback_mode = SHARED_STATE.get('playback_mode')
                
                # CRITICAL: Only poll if UPnP mode
                if not self.avtransport_url or playback_mode == PlaybackMode.USB_DIRECT:
                    # USB mode - no polling needed
                    time.sleep(0.97)
                    continue
            except Exception:
                pass
            try:
                start = time.time()
                ok, position_info = get_position_info(self.control_url, debug=self.debug)

                if ok and position_info:
                    pos = position_info['position']
                    dur = position_info['duration']

                    SHARED_STATE. update({
                        'position': pos,
                        'duration': dur,
                        'last_update': time.time()
                    })

                    if SHARED_STATE.get('play_all_enabled'):
                        track_started = SHARED_STATE.get('track_started')
                        track_start_time = SHARED_STATE. get('track_start_time')
                        last_pos = SHARED_STATE.get('last_position')

                        if not track_started and pos > 2.0:
                            SHARED_STATE.update({
                                'track_started': True,
                                'track_start_time': time.time()
                            })
                            if self.debug:
                                print(f"[Poll] Track started playing (pos={pos:.1f}s)")

                        if track_started:
                            time_since_start = time.time() - track_start_time

                            if time_since_start > 3.0:
                                track_ended = False

                                if last_pos > 5 and pos < 3 and dur > 0:
                                    track_ended = True
                                    if self.debug:
                                        print(f"[Poll] Track ended (position reset: {last_pos:.1f}s -> {pos:.1f}s)")

                                elif dur > 0 and pos >= dur - 2:
                                    track_ended = True
                                    if self.debug:
                                        print(f"[Poll] Track ended (near end: {pos:.1f}s / {dur:.1f}s)")

                                if track_ended:
                                    current_idx = SHARED_STATE.get('current_track_idx')
                                    total_tracks = SHARED_STATE. get('total_tracks')

                                    if current_idx < total_tracks - 1:
                                        if self.debug:
                                            print(f"[Poll] Auto-next to track {current_idx + 2}")
                                        SHARED_STATE.set('track_started', False)
                                        COMMAND_QUEUE.put(Command(CommandType.NEXT))
                                    else:
                                        SHARED_STATE.set('play_all_enabled', False)
                                        if self.debug:
                                            print(f"[Poll] Play All finished")

                    SHARED_STATE.set('last_position', pos)

                elapsed = time.time() - start
                remaining = self.interval - elapsed

                if remaining > 0:
                    time.sleep(remaining)
                else:
                    if self.debug:
                        print(f"[Poll] Warning: SOAP call took {elapsed:.1f}s")

            except Exception as e:
                if self.debug:
                    print(f"[Poll] Error: {e}")
                time.sleep(self.interval)

    def pause_polling(self):
        self.paused = True

    def resume_polling(self):
        self.paused = False

    def stop(self):
        self.running = False

# =====================================================================
# SECTION 7: Command Worker Thread (v4.6.1 + v4.6.2 format awareness + USB)
# =====================================================================

class CommandWorkerThread(threading.Thread):
    """Processes user commands from queue"""

    def __init__(self, control_url, files, directory, advertise_host, port, debug=False):
        super().__init__(daemon=True)
        self.control_url = control_url
        self.files = files
        self.directory = directory
        self.advertise_host = advertise_host
        self.port = port
        self.debug = debug
        self.running = True

    def run(self):
        """Main command processing loop"""
        while self.running:
            try:
                cmd = COMMAND_QUEUE.get(timeout=0.1)
                
                if cmd.type == CommandType.PLAY:
                    self._handle_play(cmd)
                elif cmd.type == CommandType.PAUSE:
                    self._handle_pause(cmd)
                elif cmd.type == CommandType.STOP:
                    self._handle_stop(cmd)
                elif cmd.type == CommandType.NEXT:  # â† MUST be here!
                    self._handle_next(cmd)
                elif cmd.type == CommandType.PREVIOUS:  # â† MUST be here!
                    self._handle_previous(cmd)
                elif cmd.type == CommandType.SET_TRACK:
                    self._handle_set_track(cmd)
                elif cmd.type == CommandType.QUIT:
                    break

            except Empty:
                continue
            except Exception as e:
                if self.debug:
                    print(f"[CommandWorker] Error: {e}")
                SHARED_STATE.set('error', str(e))

    def _handle_play(self, cmd):
        """Handle play command with format-aware metadata"""
        
        track_idx = cmd.args.get('track_idx', SHARED_STATE.get('current_track_idx'))
        
        if track_idx < 0 or track_idx >= len(self.files):
            print(f"[CommandWorker] Invalid track index: {track_idx}")
            return
        
        filename = self.files[track_idx]
        fullpath = os.path.join(self.directory, filename)
        format_type = get_format_from_extension(filename)
        
        # CRITICAL: Define ext ONCE at the top, not inside conditionals
        ext = os.path.splitext(filename)[1].lower()
        
        if format_type is None:
            print(f"[CommandWorker] Unsupported format: {filename}")
            SHARED_STATE.set('error', f"Unsupported format: {filename}")
            return
        
        SHARED_STATE.update({
            'current_track_idx': track_idx,
            'current_track_name': filename,
            'is_playing': True,
            'transport_state': 'TRANSITIONING',
            'track_started': False,
            'track_start_time': 0,
            'last_position': 0
        })
        
        playback_mode = SHARED_STATE.get('playback_mode')
        
        
        if playback_mode == PlaybackMode.USB_DIRECT:
            usb_device_idx = SHARED_STATE.get('usb_device_index')
            
            if self.debug:
                print(f"[CommandWorker] USB playback: {filename} on device {usb_device_idx}")
            
            # play_audio_usb() now handles sample rate correctly!
            success = play_audio_usb(fullpath, usb_device_idx, self.debug)
            
            if success:
                fmt = format_type.upper() if format_type else '?'
                SHARED_STATE.set('transport_state', 'PLAYING')
                print(f"[CommandWorker] âœ“ Played (USB): {filename} [{fmt}]")
            else:
                SHARED_STATE.update({
                    'is_playing': False,
                    'transport_state': 'STOPPED',
                    'error': 'USB playback failed'
                })
                print(f"[CommandWorker] âœ— USB playback failed: {filename}")
            
            return  # CRITICAL: Don't run UPnP code!
        
        # UPnP Network Playback (existing logic)
        if ext in ('.aif', '.aiff', '.m4a', '.aac'):
            wav_name = os.path.splitext(filename)[0] + '.wav'
            file_url = f"http://{self.advertise_host}:{self.port}/{urllib.parse.quote(wav_name)}"
        else:
            file_url = f"http://{self.advertise_host}:{self.port}/{urllib.parse.quote(filename)}"

        stop_upnp(self.control_url, debug=self.debug)
        time.sleep(0.3)

        ok = set_avtransport_uri_variants(
            self.control_url,
            file_url,
            wav_name if ext in ('.aif', '.aiff', '.m4a', '.aac') else filename,
            self.directory,
            filename,
            debug=self.debug
        )

        if not ok:
            print(f"[CommandWorker] SetAVTransportURI failed (all variants)")
            SHARED_STATE.update({'is_playing': False, 'error': 'SetAVTransportURI failed'})
            return

        time.sleep(0.3)

        ok = play_upnp(self.control_url, debug=self.debug)
        if ok:
            SHARED_STATE.set('transport_state', 'PLAYING')
            fmt = format_type.upper() if format_type else "?"
            print(f"[CommandWorker] ✓ Playing: {filename} [{fmt}]")
        else:
            SHARED_STATE.update({'is_playing': False, 'error': 'Play failed'})
            print(f"[CommandWorker] ✗ Play failed")

    def _handle_pause(self, cmd):
        playback_mode = SHARED_STATE.get('playback_mode')
        
        if playback_mode == PlaybackMode.USB_DIRECT:
            SHARED_STATE.update({'is_playing': False, 'transport_state': 'PAUSED'})
            sd.stop()
            print(f"[CommandWorker] ✓ Paused (USB)")
        else:
            ok = pause_upnp(self.control_url, debug=self.debug)
            if ok:
                SHARED_STATE.update({'is_playing': False, 'transport_state': 'PAUSED'})
                print(f"[CommandWorker] ✓ Paused")
            else:
                print(f"[CommandWorker] ✗ Pause failed")

    def _handle_next(self, cmd):
        """Handle next track command (works for both USB and UPnP)"""
        playback_mode = SHARED_STATE.get('playback_mode')
        current_idx = SHARED_STATE.get('current_track_idx')
        
        if current_idx >= len(self.files) - 1:
            print("[CommandWorker] Already at last track")
            return
        
        if playback_mode == PlaybackMode.USB_DIRECT:
            # USB mode: stop current, play next
            try:
                import sounddevice as sd
                sd.stop()
            except:
                pass
            
            next_idx = current_idx + 1
            self._handle_play(Command(CommandType.PLAY, {'track_idx': next_idx}))
        else:
            # UPnP mode: use existing logic
            stop_upnp(self.control_url, debug=self.debug)
            time.sleep(0.3)
            
            next_idx = current_idx + 1
            self._handle_play(Command(CommandType.PLAY, {'track_idx': next_idx}))

    def _handle_previous(self, cmd):
        """Handle previous track command (works for both USB and UPnP)"""
        playback_mode = SHARED_STATE.get('playback_mode')
        current_idx = SHARED_STATE.get('current_track_idx')
        
        if current_idx <= 0:
            print("[CommandWorker] Already at first track")
            return
        
        if playback_mode == PlaybackMode.USB_DIRECT:
            # USB mode: stop current, play previous
            try:
                import sounddevice as sd
                sd.stop()
            except:
                pass
            
            prev_idx = current_idx - 1
            self._handle_play(Command(CommandType.PLAY, {'track_idx': prev_idx}))
        else:
            # UPnP mode: use existing logic
            stop_upnp(self.control_url, debug=self.debug)
            time.sleep(0.3)
            
            prev_idx = current_idx - 1
            self._handle_play(Command(CommandType.PLAY, {'track_idx': prev_idx}))

    def _handle_stop(self, cmd):
        """Stop playback (works for both USB and UPnP)"""
        playback_mode = SHARED_STATE.get('playback_mode')
        
        if playback_mode == PlaybackMode.USB_DIRECT:
            # USB mode: stop sounddevice
            try:
                import sounddevice as sd
                sd.stop()
            except:
                pass
            
            SHARED_STATE.update({
                'is_playing': False,
                'transport_state': 'STOPPED'
            })
            print("[CommandWorker] âœ“ Stopped")
        else:
            # UPnP mode: use existing logic
            ok = pause_upnp(self.control_url, debug=self.debug)
            time.sleep(0.2)
            ok = stop_upnp(self.control_url, debug=self.debug)
            
            if ok:
                SHARED_STATE.update({
                    'is_playing': False,
                    'transport_state': 'STOPPED'
                })
                print("[CommandWorker] âœ“ Stopped")
            else:
                print("[CommandWorker] âœ— Stop failed")

    def _handle_set_track(self, cmd):
        """Set track and play it"""
        track_idx = cmd.args.get('track_idx', 0)
        # Immediately play the selected track
        self._handle_play(Command(CommandType.PLAY, {'track_idx': track_idx}))

    def stop(self):
        self.running = False

# =====================================================================
# SECTION 8: HTTP Server (v4.6.1 + v4.6.2 multi-format MIME types)
# =====================================================================

BASE_DIR = "."

def ensure_mime_types():
    mimetypes.add_type('audio/wav', '.wav')
    mimetypes.add_type('audio/x-wav', '.x-wav')
    mimetypes.add_type('audio/flac', '.flac')
    mimetypes.add_type('audio/aac', '.aac')
    mimetypes.add_type('audio/mpeg', '.mp3')
    mimetypes.add_type('audio/mp3', '.mp3')
    mimetypes.add_type('audio/m4a', '.m4a')
    mimetypes.add_type('audio/ogg', '.ogg')
    mimetypes.add_type('audio/vnd.sony.dsf', '.dsf')

class StaticAudioHandler(http.server.SimpleHTTPRequestHandler):
    """HTTP handler with multi-format support and chunked streaming"""

    def do_GET(self):
        """GET handler with base_dir-aware file serving (v4.6.2.2 FIXED)"""
        from urllib.parse import unquote
        base_dir = self.server.base_dir  # Get from server object!

        path = unquote(self.path[1:])  # Remove leading /
        fullpath = os.path.join(base_dir, path)
        
        # Debug logging
        if hasattr(self. server, 'debug') and self.server.debug:
            print(f"[HTTP] GET request: /{path}")
            print(f"[HTTP] Full path: {fullpath}")
            print(f"[HTTP] Exists: {os.path.exists(fullpath)}")
        
        # Check if file exists in base_dir
        if not os.path.exists(fullpath):
            # Try AIFF fallback for .wav requests
            if path.lower().endswith('.wav'):
                possible_aiff = fullpath[:-4] + '.aiff'
                possible_aif = fullpath[:-4] + '.aif'
                
                for candidate in [possible_aiff, possible_aif]:
                    if os.path.exists(candidate):
                        try:
                            # Stream AIFF as WAV
                            info = sf.info(candidate)
                            samplerate = info.samplerate
                            nch = info.channels
                            nframes = info.frames
                            sampwidth = 2
                            datasize = nframes * nch * sampwidth
                            totalsize = 44 + datasize
                            
                            header = self._wav_header_bytes(nch, sampwidth, samplerate, nframes)
                            
                            self.send_response(200)
                            self.send_header('Content-Type', 'audio/wav')
                            self.send_header('Content-Length', str(totalsize))
                            self. send_header('Accept-Ranges', 'bytes')
                            self.end_headers()
                            
                            self.wfile.write(header)
                            
                            CHUNKSIZE = 65536
                            with sf.SoundFile(candidate, 'r') as f:
                                while True:
                                    try:
                                        data = f.read(CHUNKSIZE, dtype='int16')
                                        if data.size == 0:
                                            break
                                        self. wfile.write(data.tobytes())
                                        self.wfile.flush()
                                    except (BrokenPipeError, ConnectionResetError):
                                        if hasattr(self.server, 'debug') and self.server. debug:
                                            print(f"[HTTP] Client disconnected")
                                        break
                                    except Exception as e:
                                        if hasattr(self. server, 'debug') and self.server.debug:
                                            print(f"[HTTP] Streaming error: {e}")
                                        break
                            
                            if hasattr(self.server, 'debug') and self.server. debug:
                                print(f"[HTTP] ✓ Streamed AIFF→WAV")
                            return
                        except BrokenPipeError:
                            return
                        except Exception as e:
                            print(f"[HTTP] Error: {e}")
                            try:
                                self.send_error(500)
                            except:
                                pass
                            return
            if path.lower().endswith('.wav'):
                possible_m4a = fullpath[:-4] + '.m4a'
                possible_aac = fullpath[:-4] + '.aac'
                
                for candidate in [possible_m4a, possible_aac]:
                    if os.path.exists(candidate):
                        try:
                            # Stream M4A/AAC as WAV
                            info = sf.info(candidate)
                            samplerate = info.samplerate
                            nch = info.channels
                            nframes = info.frames
                            sampwidth = 2  # 16-bit PCM
                            datasize = nframes * nch * sampwidth
                            totalsize = 44 + datasize
                            
                            header = self.wav_header_bytes(nch, sampwidth, samplerate, nframes)
                            
                            self.send_response(200)
                            self.send_header('Content-Type', 'audio/wav')
                            self.send_header('Content-Length', str(totalsize))
                            self.send_header('Accept-Ranges', 'bytes')
                            self.end_headers()
                            
                            self.wfile.write(header)
                            
                            CHUNKSIZE = 65536
                            with sf.SoundFile(candidate, 'r') as f:
                                while True:
                                    try:
                                        data = f.read(CHUNKSIZE, dtype='int16')
                                        if data.size == 0:
                                            break
                                        self.wfile.write(data.tobytes())
                                        self.wfile.flush()
                                    except (BrokenPipeError, ConnectionResetError):
                                        if hasattr(self.server, 'debug') and self.server.debug:
                                            print(f"[HTTP] Client disconnected")
                                        break
                                    except Exception as e:
                                        if hasattr(self.server, 'debug') and self.server.debug:
                                            print(f"[HTTP] Streaming error: {e}")
                                        break
                            
                            if hasattr(self.server, 'debug') and self.server.debug:
                                print(f"[HTTP] âœ“ Streamed M4Aâ†’WAV")
                            return
                        
                        except BrokenPipeError:
                            return
                        except Exception as e:
                            print(f"[HTTP] Error: {e}")
                            try:
                                self.send_error(500)
                            except:
                                pass
                            return            
            # Try M4A/AAC fallback for .wav requests
            possible_m4a = fullpath[:-4] + '.m4a'
            possible_aac = fullpath[:-4] + '. aac'
            
            for candidate in [possible_m4a, possible_aac]:
                if os.path.exists(candidate):
                    try:
                        # Stream M4A/AAC as WAV
                        info = sf.info(candidate)
                        samplerate = info.samplerate
                        nch = info. channels
                        nframes = info.frames
                        sampwidth = 2  # 16-bit PCM
                        datasize = nframes * nch * sampwidth
                        totalsize = 44 + datasize
                        
                        header = self._wav_header_bytes(nch, sampwidth, samplerate, nframes)
                        
                        self.send_response(200)
                        self.send_header('Content-Type', 'audio/wav')
                        self.send_header('Content-Length', str(totalsize))
                        self.send_header('Accept-Ranges', 'bytes')
                        self.end_headers()
                        
                        self.wfile.write(header)
                        
                        CHUNKSIZE = 65536
                        with sf.SoundFile(candidate, 'r') as f:
                            while True:
                                try:
                                    data = f.read(CHUNKSIZE, dtype='int16')
                                    if data.size == 0:
                                        break
                                    self.wfile.write(data.tobytes())
                                    self.wfile.flush()
                                except (BrokenPipeError, ConnectionResetError):
                                    if hasattr(self.server, 'debug') and self.server.debug:
                                        print(f"[HTTP] Client disconnected")
                                    break
                                except Exception as e:
                                    if hasattr(self.server, 'debug') and self. server.debug:
                                        print(f"[HTTP] Streaming error: {e}")
                                    break
                        
                        if hasattr(self.server, 'debug') and self. server.debug:
                            print(f"[HTTP] ✓ Streamed M4A/AAC→WAV")
                        return
                    except BrokenPipeError:
                        return
                    except Exception as e:
                        print(f"[HTTP] Error: {e}")
                        try:
                            self.send_error(500)
                        except:
                            pass
                        return
                    
            # File not found
            if hasattr(self.server, 'debug') and self.server.debug:
                print(f"[HTTP] ✗ 404: {fullpath}")
            self.send_error(404)
            return
        
        # FILE EXISTS
        if hasattr(self.server, 'debug') and self.server.debug:
            print(f"[HTTP] ✓ Found: {fullpath}")
        
        try:
            stat_info = os.stat(fullpath)
            size = stat_info.st_size
            
            self.send_response(200)
            
            # Guess MIME type
            mime_type, _ = mimetypes.guess_type(fullpath)
            if mime_type is None:
                mime_type = 'application/octet-stream'
            
            self.send_header('Content-Type', mime_type)
            self.send_header('Content-Length', str(size))
            self.send_header('Accept-Ranges', 'bytes')
            self.end_headers()
            
            # Stream file
            with open(fullpath, 'rb') as f:
                self.wfile.write(f. read())

        except Exception as e:
            if hasattr(self.server, 'debug') and self.server.debug:
                print(f"[HTTP] Error serving {fullpath}: {e}")
            try:
                self.send_error(500)
            except:
                pass

    def _wav_header_bytes(self, nch, sampwidth, framerate, nframes):
        datasize = nframes * nch * sampwidth
        header = struct.pack(
            "<4sI4s4sIHHIIHH4sI",
            b"RIFF",
            36 + datasize,
            b"WAVE",
            b"fmt ",
            16,
            1,
            nch,
            framerate,
            framerate * nch * sampwidth,
            nch * sampwidth,
            sampwidth * 8,
            b"data",
            datasize,
        )
        return header

    def log_message(self, format, *args):
        if hasattr(self. server, 'debug') and self.server.debug:
            super().log_message(format, *args)

class ThreadedHTTPServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True

def start_http_server(directory, host, port, debug=False):
    httpd = ThreadedHTTPServer((host, port), StaticAudioHandler)
    httpd.debug = debug
    httpd.base_dir = os.path.abspath(directory)  # KEY LINE
    
    t = threading.Thread(target=httpd.serve_forever, daemon=True)
    t.start()
    
    print(f"[HTTP] Serving {directory} on {host}:{port}")
    print(f"[HTTP] BASE_DIR: {httpd.base_dir}")
    
    return httpd


# =====================================================================
# SECTION 9: UPnP Discovery (v4.6.1, unchanged)
# =====================================================================

def discover_upnp_devices(service_type, timeout=5, debug=False):
    MSEARCH = (
        'M-SEARCH * HTTP/1.1\r\n'
        'HOST:239.255.255.250:1900\r\n'
        'MAN:"ssdp:discover"\r\n'
        f'ST:{service_type}\r\n'
        'MX:1\r\n\r\n'
    )

    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
    sock.settimeout(timeout)
    devices = []

    try:
        sock.sendto(MSEARCH.encode('utf-8'), ('239.255.255.250', 1900))
        start_time = time.time()

        while True:
            try:
                data, addr = sock.recvfrom(65507)
                text = data.decode('utf-8', errors='replace')
                location = None

                for line in text.split("\r\n"):
                    if line.lower().startswith("location:"):
                        location = line.split(":", 1)[1].strip()

                if location and location not in devices:
                    devices. append(location)

            except socket.timeout:
                break

            if time.time() - start_time > timeout:
                break

    finally:
        try:
            sock.close()
        except Exception:
            pass

    return devices

def get_service_urls(description_url, debug=False):
    try:
        with urllib.request.urlopen(description_url, timeout=10) as resp:
            xml_data = resp.read()
        root = ET.fromstring(xml_data)
    except Exception:
        return None, None

    ns = {"urn": "urn:schemas-upnp-org:device-1-0"}

    avtransport_url = None
    connectionmgr_url = None

    for service in root.findall(".//urn:service", ns):
        st = service.find("urn:serviceType", ns)
        cu = service.find("urn:controlURL", ns)

        if st is None or cu is None:
            continue

        service_type = (st.text or "")
        control_url = (cu.text or "")

        base = description_url.rsplit("/", 1)[0]
        full_url = urljoin(base + "/", control_url)

        if "AVTransport" in service_type:
            avtransport_url = full_url
        elif "ConnectionManager" in service_type:
            connectionmgr_url = full_url

    return avtransport_url, connectionmgr_url

def get_lan_advertise_ip(fallback='127.0.0.1'):
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return fallback

def list_audio_files(directory):
    audio_ext = ('.wav', '.flac', '.aac', '.mp3', '.m4a', '. ogg', '.aif', '.aiff', '.dsf')
    try:
        files = []
        for f in os.listdir(directory):
            if f.startswith('._'):
                continue
            if f.lower().endswith(audio_ext):
                files.append(f)
        return sorted(files)
    except Exception as e:
        print("Directory error:", e)
        return []

# =====================================================================
# SECTION 10: Interactive UI (v4.6.1 + v4.6.2 format display + USB mode switching)
# =====================================================================

def interactive_ui(files, polling_thread, command_worker, debug=False):
    print(f"\n{'='*80}")
    print("ULTIMATE HIFI AUDIO PLAYER v4.6.3 - Multi-Format + USB Support")
    print(f"{'='*80}")
    print("Threading: Command Queue + 970ms Polling (Wireshark-validated)")
    print("Formats: WAV, AIFF, MP3, FLAC, M4A, DSF")
    print("Modes: UPnP Network + USB Direct")
    if USB_DEVICES_QUERYABLE:
        print("✓ USB Detection Available")
    else:
        print("✗ USB Detection Not Available")
    print(f"{'='*80}\n")

    SHARED_STATE.set('total_tracks', len(files))

    while True:
        state = SHARED_STATE.get_all()
        playback_mode = state. get('playback_mode', PlaybackMode.UPNP_NETWORK)

        print(f"\n{'='*80}")
        print("AVAILABLE TRACKS")
        print(f"{'='*80}")

        for i, f in enumerate(files):
            if i == state['current_track_idx'] and state['is_playing']:
                prefix = "▶"
            else:
                prefix = " "
            
            fmt = get_format_from_extension(f).upper() if get_format_from_extension(f) else "?"
            print(f"{prefix} {i+1:2d}. {f:<50} [{fmt}]")

        print(f"\n{'='*80}")
        print("STATUS")
        print(f"{'='*80}")

        mode_name = "USB Direct" if playback_mode == PlaybackMode.USB_DIRECT else "UPnP Network"
        print(f"Mode: {mode_name}")

        if playback_mode == PlaybackMode.USB_DIRECT and state.get('usb_device_name'):
            print(f"Device: {state['usb_device_name']}")

        if state['is_playing']:
            if playback_mode == PlaybackMode.USB_DIRECT:
                print(f"▶ Playing: {state['current_track_name']} (USB Direct)")
            else:
                pos = state['position']
                dur = state['duration']
                print(f"▶ Playing: {state['current_track_name']}")

                if state['play_all_enabled']:
                    start_idx = state['play_all_start_idx']
                    print(f" Mode: Sequential (Play All from track {start_idx+1})")
                else:
                    print(f" Mode: Single Track")

                print(f" Position: {int(pos//60)}:{int(pos%60):02d} / {int(dur//60)}:{int(dur%60):02d}")
        else:
            print(f"⸸ State: {state['transport_state']}")

        if state['error']:
            print(f"✗ Error: {state['error']}")
            SHARED_STATE.set('error', None)

        print(f"\n{'='*80}")
        print("COMMANDS")
        print(f"{'='*80}")
        print(f"1-{len(files)}: Play single track")
        print(f"a: Play All from track (sequential)")
        print(f"p: Play/Resume | s: Stop | n: Next | b: Previous")
        if USB_DEVICES_QUERYABLE:
            print(f"m: Toggle Mode (USB ↔ UPnP)")
            print(f"d: Select USB Device")
        print(f"q: Quit")
        print(f"{'='*80}")

        choice = input("\nCommand: ").strip().lower()

        if choice == 'q':
            SHARED_STATE.set('play_all_enabled', False)
            COMMAND_QUEUE.put(Command(CommandType.STOP))
            if state['is_playing']:
                print("\n[Quit] Stopping playback before exit...")
                SHARED_STATE.set('play_all_enabled', False)
                COMMAND_QUEUE.put(Command(CommandType.STOP))
                
                timeout = 5
                start = time.time()
                while (SHARED_STATE.get('transport_state') != 'STOPPED' and 
                       (time.time() - start) < timeout):
                    time.sleep(0.1)
                
                if SHARED_STATE.get('is_playing'):
                    print("[Quit] Warning: Playback did not stop in time, continuing shutdown...")
                else:
                    print("[Quit] Playback stopped successfully")

            COMMAND_QUEUE.put(Command(CommandType.QUIT))
            break

        elif choice == 'm' and USB_DEVICES_QUERYABLE:
            current_mode = SHARED_STATE.get('playback_mode')
            new_mode = PlaybackMode.USB_DIRECT if current_mode == PlaybackMode. UPNP_NETWORK else PlaybackMode. UPNP_NETWORK
            SHARED_STATE.set('playback_mode', new_mode)
            mode_name = "USB Direct" if new_mode == PlaybackMode. USB_DIRECT else "UPnP Network"
            print(f"✓ Switched to {mode_name} mode")
            
            if new_mode == PlaybackMode.USB_DIRECT:
                polling_thread.pause_polling()
            else:
                polling_thread. resume_polling()

        elif choice == 'd' and USB_DEVICES_QUERYABLE:
            dacs = list_usb_dacs(debug=debug)
            
            print(f"\n{'='*80}")
            print("AVAILABLE USB DEVICES")
            print(f"{'='*80}")
            
            for dac in dacs:
                print(f"[{dac['index']}] {dac['name']}")
                print(f"    {dac['channels']}ch @ {dac['sample_rate']}Hz ({dac['hostapi']})")
            
            sel = input("\nSelect device index (or Enter for auto): ").strip()
            if sel.isdigit():
                idx = int(sel)
                if any(d['index'] == idx for d in dacs):
                    selected_dac = next(d for d in dacs if d['index'] == idx)
                    SHARED_STATE.update({
                        'usb_device_index': idx,
                        'usb_device_name': selected_dac['name']
                    })
                    print(f"✓ Selected: {selected_dac['name']}")
                else:
                    print("✗ Invalid device index")
            else:
                idx, device = find_ifi_dac(debug=debug)
                if idx is not None:
                    SHARED_STATE.update({
                        'usb_device_index': idx,
                        'usb_device_name': device['name']
                    })
                    print(f"✓ Auto-detected: {device['name']}")
                else:
                    print("✗ No compatible device found")

        elif choice == 'a':
            try:
                start_track = input(f"Start from track (1-{len(files)}, default=1): ").strip()
                start_idx = int(start_track) - 1 if start_track else 0
                if 0 <= start_idx < len(files):
                    SHARED_STATE.update({
                        'play_all_enabled': True,
                        'play_all_start_idx': start_idx,
                        'last_position': 0,
                        'track_started': False,
                        'track_start_time': 0
                    })
                    # MUST send PLAY command, not SET_TRACK!
                    COMMAND_QUEUE.put(Command(CommandType.PLAY, {'track_idx': start_idx}))
                    print(f"â–¶ Starting Play All from track {start_idx+1}")
                else:
                    print("Invalid track number")
            except ValueError:
                print("Invalid input")

        elif choice == 'p':
            current_idx = state['current_track_idx']
            COMMAND_QUEUE.put(Command(CommandType.PLAY, {'track_idx': current_idx}))

        elif choice == 'n':
            # Next track command
            playback_mode = state.get('playback_mode', PlaybackMode.UPNP_NETWORK)
            
            if state['current_track_idx'] < len(files) - 1:
                COMMAND_QUEUE.put(Command(CommandType.NEXT))
                if playback_mode == PlaybackMode.USB_DIRECT:
                    print(f"â–¶ Next: {files[state['current_track_idx'] + 1]}")
                else:
                    print("â–¶ Next")
            else:
                print("Already at last track")
        
        elif choice == 'b':
            # Previous track command
            playback_mode = state.get('playback_mode', PlaybackMode.UPNP_NETWORK)
            
            if state['current_track_idx'] > 0:
                COMMAND_QUEUE.put(Command(CommandType.PREVIOUS))
                if playback_mode == PlaybackMode.USB_DIRECT:
                    print(f"â–¶ Previous: {files[state['current_track_idx'] - 1]}")
                else:
                    print("â–¶ Previous")
            else:
                print("Already at first track")
        
        elif choice == 's':
            # Stop command
            playback_mode = state.get('playback_mode', PlaybackMode.UPNP_NETWORK)
            
            SHARED_STATE.set('play_all_enabled', False)
            COMMAND_QUEUE.put(Command(CommandType.STOP))
            
            if playback_mode == PlaybackMode.USB_DIRECT:
                print("â¹ Stopping USB playback")
            else:
                print("â¹ Stopping")

        else:
            try:
                sel = int(choice)
                if 1 <= sel <= len(files):
                    SHARED_STATE.set('play_all_enabled', False)
                    COMMAND_QUEUE.put(Command(CommandType.SET_TRACK, {'track_idx': sel - 1}))
                else:
                    print("Invalid track number")
            except ValueError:
                print("Invalid command")

def interactive_ui_usb(usb_engine, debug=False):
    """
    Interactive UI for USB playback mode.
    
    This is the USB equivalent to interactive_ui() for UPnP mode.
    Completely separate implementation with its own event loop.
    """
    files = usb_engine.get_state()['files']
    
    def get_format_label(filename):
        """Get audio format for display"""
        ext = os.path.splitext(filename)[1].lower()
        ext_map = {
            '.mp3': 'MP3', '.m4a': 'M4A', '.aac': 'AAC',
            '.flac': 'FLAC', '.dsf': 'DSF', '.wav': 'WAV',
            '.aif': 'AIFF', '.aiff': 'AIFF'
        }
        return ext_map.get(ext, '?')
    
    try:
        while True:
            state = usb_engine.get_state()
            
            # Clear screen
            os.system('clear' if os.name == 'posix' else 'cls')
            
            # Header
            print(f"\n{'='*80}")
            print("ULTIMATE HIFI AUDIO PLAYER v4.6.3 - USB Direct Mode")
            print(f"{'='*80}\n")
            
            # Track list
            print(f"{'='*80}")
            print("AVAILABLE TRACKS")
            print(f"{'='*80}")
            for i, f in enumerate(files, 1):
                marker = "▶ " if i == state['current_track_idx'] + 1 else "   "
                fmt = get_format_label(f)
                print(f"{marker}{i:2}. {f:<50} [{fmt}]")
            
            # Status
            print(f"\n{'='*80}")
            print("STATUS")
            print(f"{'='*80}")
            print(f"Device: {state.get('device', 'iFi Pro iDSD')}")
            
            if state['is_playing']:
                pos_m, pos_s = divmod(int(state['position']), 60)
                dur_m, dur_s = divmod(int(state['duration']), 60)
                print(f"⏵ PLAYING")
                print(f"▶ {state['track_name']}")
                print(f"  Position: {pos_m}:{pos_s:02d} / {dur_m}:{dur_s:02d}")
            elif state['is_paused']:
                print(f"⏸ PAUSED")
                print(f"▶ {state['track_name']}")
            else:
                print(f"⏹ STOPPED")
            
            if state['play_all']:
                print(f"  Mode: Play All")
            
            # Commands
            print(f"\n{'='*80}")
            print("COMMANDS")
            print(f"{'='*80}")
            print("1-N: Play single track")
            print("a: Play All from track (sequential)")
            print("p: Play/Pause | s: Stop | n: Next | b: Previous")
            print("q: Quit")
            print(f"{'='*80}\n")
            
            # Read command
            choice = input("Command: ").strip().lower()
            
            if not choice:
                continue
            
            if choice == 'q':
                print("\n[USB-UI] Stopping playback...")
                usb_engine.enqueue_command(USBCommandType.STOP)
                time.sleep(0.5)
                break
            
            elif choice == 'a':
                try:
                    prompt = f"Start from track (1-{len(files)}, default=1): "
                    start_input = input(prompt).strip()
                    start_idx = int(start_input) - 1 if start_input else 0
                    
                    if 0 <= start_idx < len(files):
                        print(f"▶ Starting Play All from track {start_idx + 1}")
                        usb_engine.enqueue_command(
                            USBCommandType.PLAY_ALL,
                            start_idx=start_idx
                        )
                    else:
                        print("Invalid track number")
                
                except ValueError:
                    print("Invalid input")
            
            elif choice == 'n':
                print("▶ Next")
                usb_engine.enqueue_command(USBCommandType.NEXT)
            
            elif choice == 'b':
                print("▶ Previous")
                usb_engine.enqueue_command(USBCommandType.PREVIOUS)
            
            elif choice == 's':
                print("⏹ Stopping")
                usb_engine.enqueue_command(USBCommandType.STOP)
            
            elif choice == 'p':
                state = usb_engine.get_state()
                if state['is_playing']:
                    print("⏸ Pausing")
                    usb_engine.enqueue_command(USBCommandType.PAUSE)
                elif state['is_paused']:
                    print("⏵ Resuming")
                    usb_engine.enqueue_command(USBCommandType.PLAY)
                else:
                    if state['current_track_idx'] < len(files):
                        print("▶ Playing")
                        usb_engine.enqueue_command(USBCommandType.PLAY)
            
            else:
                try:
                    track_num = int(choice)
                    if 1 <= track_num <= len(files):
                        print(f"▶ Playing track {track_num}")
                        usb_engine.enqueue_command(
                            USBCommandType.PLAY,
                            track_idx=track_num - 1
                        )
                    else:
                        print("Invalid track number")
                
                except ValueError:
                    print("Invalid command")
            
            time.sleep(0.1)
    
    except KeyboardInterrupt:
        print("\n\nInterrupted by user")
                

def main():
    parser = argparse.ArgumentParser(
        description="Ultimate HiFi Audio Player v4.6.3 - Multi-Format + USB Support",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
%(prog)s --dir /music/
%(prog)s --dir /music/ --usb
%(prog)s --dir /music/ --usb --device 2
%(prog)s --dir /music/ --list-devices
%(prog)s --dir /music/ --debug
        """
    )
    
    parser.add_argument("--dir", required=True, help="Directory with audio files")
    parser.add_argument("--bind-host", default="0.0.0.0", help="HTTP server bind host")
    parser.add_argument("--port", type=int, default=8000, help="HTTP server port")
    parser.add_argument("--advertise-host", default=None, help="Host/IP in URLs for renderer")
    parser.add_argument("--discover-timeout", type=int, default=5, help="SSDP discovery timeout (s)")
    parser.add_argument("--usb", action="store_true", help="Start in USB mode")
    parser.add_argument("--device", type=int, default=None, help="USB device index")
    parser.add_argument("--list-devices", action="store_true", help="List USB devices and exit")
    parser.add_argument("--debug", action="store_true", help="Enable debug logging")
    
    args = parser.parse_args()
    
    # List USB devices and exit
    if args.list_devices:
        if USB_DEVICES_QUERYABLE:
            print(f"\n{'='*80}")
            print("AVAILABLE USB AUDIO DEVICES")
            print(f"{'='*80}")
            dacs = list_usb_dacs(debug=args.debug)
            if dacs:
                for dac in dacs:
                    print(f"[{dac['index']}] {dac['name']}")
                    print(f" {dac['channels']}ch @ {dac['sample_rate']}Hz ({dac['hostapi']})")
            else:
                print("No USB audio devices found")
            print(f"{'='*80}\n")
        else:
            print("USB device enumeration not available")
        return
    
    advertise_host = args.advertise_host or get_lan_advertise_ip()
    if advertise_host in ("0.0.0.0", "127.0.0.1"):
        advertise_host = get_lan_advertise_ip() or advertise_host
    
    print(f"\n{'='*80}")
    print("HIFI AUDIO PLAYER v4.6.3 - MULTI-FORMAT + USB SUPPORT")
    print(f"{'='*80}")
    print("Architecture: Command Queue + 970ms Polling (Wireshark)")
    print("Formats: WAV, AIFF, MP3, FLAC, M4A, DSF")
    print("Modes: UPnP Network + USB Direct")
    print(f"{'='*80}\n")
    
    # Initialize playback mode
    playback_mode = PlaybackMode.USB_DIRECT if args.usb else PlaybackMode.UPNP_NETWORK
    usb_device_index = args.device
    usb_device_name = ""
    
    # If USB mode requested, find/configure device
    if args.usb and USB_DEVICES_QUERYABLE:
        if usb_device_index is None:
            idx, device = find_ifi_dac(debug=args.debug)
            if idx is not None:
                usb_device_index = idx
                usb_device_name = device['name']
                print(f"âœ“ Auto-detected USB Device: {usb_device_name}")
            else:
                print("âš  No USB DAC found, falling back to UPnP mode")
                playback_mode = PlaybackMode.UPNP_NETWORK
        else:
            dacs = list_usb_dacs()
            matching = [d for d in dacs if d['index'] == usb_device_index]
            if matching:
                usb_device_name = matching[0]['name']
                print(f"âœ“ Using USB Device {usb_device_index}: {usb_device_name}")
            else:
                print(f"âš  USB Device {usb_device_index} not found, falling back to UPnP mode")
                playback_mode = PlaybackMode.UPNP_NETWORK
    
    SHARED_STATE.update({
        'playback_mode': playback_mode,
        'usb_device_index': usb_device_index,
        'usb_device_name': usb_device_name
    })
    
    av_transport_url = None
    connection_mgr_url = None
    httpd = None
    
    # Only discover UPnP if not starting in USB mode (or may fallback)
    if playback_mode == PlaybackMode.USB_DIRECT:
        # USB-only mode - no network needed
        print(f"[USB Mode] âœ“ Ready for USB playback (no UPnP needed)")
        print(f"[USB Mode] â„¹ No network connection required")
        
        ensure_mime_types()  # Still needed for MIME type detection
        httpd = None
    av_transport_url = None
    connection_mgr_url = None
    devices = []
    
    if playback_mode == PlaybackMode.USB_DIRECT:
      
        print(f"[USB Mode] âœ“ Ready for USB playback (no UPnP needed)")
        print(f"[USB Mode] â„¹ No network connection required")
        
        ensure_mime_types()
        # av_transport_url stays None for USB mode
        
    elif playback_mode == PlaybackMode.UPNP_NETWORK:
      
        print(f"[HTTP] Advertised host: {advertise_host}")
        ensure_mime_types()
        
        try:
            httpd = start_http_server(args.dir, args.bind_host, args.port, debug=args.debug)
        except OSError as e:
            print(f"Error starting HTTP server: {e}")
            return
        
        print("Searching for UPnP renderers...")
        devices = discover_upnp_devices("urn:schemas-upnp-org:device:MediaRenderer:1",
                                        timeout=args.discover_timeout, debug=args.debug)
        
        if not devices:
            print("âš  No UPnP devices found.")
            
            if USB_DEVICES_QUERYABLE:
                idx, device = find_ifi_dac(debug=args.debug)
                if idx is not None:
                    print(f"âœ“ Falling back to USB mode: {device['name']}")
                    playback_mode = PlaybackMode.USB_DIRECT
                    usb_device_index = idx
                    usb_device_name = device['name']
                    SHARED_STATE.update({
                        'playback_mode': playback_mode,
                        'usb_device_index': usb_device_index,
                        'usb_device_name': usb_device_name
                    })
                    # av_transport_url stays None
                else:
                    print("âœ— No USB devices either. Cannot proceed.")
                    if httpd:
                        httpd.shutdown()
                    return
            else:
                print("âœ— USB fallback not available. Cannot proceed.")
                if httpd:
                    httpd.shutdown()
                return
        else:
            # Found UPnP devices - get URLs
            for desc_url in devices:
                av_transport_url, connection_mgr_url = get_service_urls(desc_url, debug=args.debug)
                if av_transport_url:
                    print(f"âœ“ AVTransport: {av_transport_url}")
                if connection_mgr_url:
                    print(f"âœ“ ConnectionManager: {connection_mgr_url}")
                if av_transport_url:
                    break
            
            if not av_transport_url:
                print("âœ— No UPnP renderer with AVTransport found")
                if httpd:
                    httpd.shutdown()
                return
    
    else:
        print("âœ— Invalid playback mode")
        return
    
    files = list_audio_files(args.dir)
    if not files:
        print("No audio files found")
        if httpd:
            httpd.shutdown()
        return
    
    print(f"\nFound {len(files)} audio files")
    
    print("\n[Threading] Starting Command Worker...")
    command_worker = CommandWorkerThread(
        av_transport_url, files, args.dir, advertise_host, args.port, debug=args.debug
    )
    command_worker.start()
    
    print("[Threading] Starting Polling Thread (970ms interval)...")
    polling_thread = PollingThread(av_transport_url, interval_ms=970, debug=args.debug)
    polling_thread.start()
    
    print("[Threading] All threads started\n")
    
    try:
        if playback_mode == PlaybackMode.USB_DIRECT:
            # ═══════════════════════════════════════════════════════════
            # USB MODE: Use dedicated engine
            # ═══════════════════════════════════════════════════════════
            print(f"\n[Main] Starting USB Playback Engine...")
            
            usb_engine = USBPlaybackEngine(
                args.dir,
                usb_device_index,
                debug=args.debug
            )
            usb_engine.start()
            
            # Run USB-specific UI (non-blocking, separate from engine threads)
            interactive_ui_usb(usb_engine, debug=args.debug)
            
            # Shutdown engine cleanly
            usb_engine.stop_all()
        
        else:
            # ═══════════════════════════════════════════════════════════
            # UPnP MODE: Use existing architecture (unchanged)
            # ═══════════════════════════════════════════════════════════
            interactive_ui(files, polling_thread, command_worker, debug=args.debug)
    
    except KeyboardInterrupt:
        print("\n\nInterrupted by user.")

    finally:
        print("\n[Shutdown] Stopping threads...")
        polling_thread.stop()
        command_worker.stop()
        
        print("[Shutdown] Stopping HTTP server...")
        try:
            if httpd:
                httpd.shutdown()
        except Exception:
            pass
        
        print("[Shutdown] Clean exit")


if __name__ == "__main__":
    main()
