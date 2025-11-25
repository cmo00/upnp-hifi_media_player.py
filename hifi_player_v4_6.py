#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Ultimate HiFi Audio Player v4.6 - Auto-Stop on Quit
---------------------------------------------------
Based on Wireshark network capture analysis of commercial UPnP players.

NEW in v4.6:
- Auto-stop playback when quitting (sends Stop command before exit)

Previous fixes:
- Fixed Auto-Next detection (waits for track to actually start playing)
- Added grace period before enabling auto-next detection
- DIDL-Lite metadata with fallback variants
- Command Queue + 970ms polling (Wireshark-validated)

Features in v4.6:
- âœ“ DIDL-Lite metadata with fallback variants
- âœ“ Command Queue + 970ms polling (Wireshark-validated)
- âœ“ Thread-safe shared state
- âœ“ Chunked HTTP streaming
- âœ“ Sequential Play All with Auto-Next (FIXED!)
- âœ“ Auto-Stop on Quit (NEW!)
- âœ“ Single track mode
- âœ“ Play/Pause/Stop/Next/Previous

Requirements:
pip install sounddevice soundfile numpy tqdm
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

# Optional dependencies
try:
    import sounddevice as sd
    USB_SUPPORT = True
except ImportError:
    USB_SUPPORT = False
    print("[WARNING] sounddevice/soundfile not installed - USB mode disabled")

try:
    from tqdm import tqdm
    TQDM_SUPPORT = True
except ImportError:
    TQDM_SUPPORT = False
    print("[WARNING] tqdm not installed - progress bar disabled")

# ----------------------
# Threading Architecture
# ----------------------

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
    """Thread-safe shared state with Play All support"""
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
            'play_all_enabled': False,      # Sequential playback flag
            'play_all_start_idx': 0,        # Starting track for Play All
            'last_position': 0,             # Track position from last poll
            'total_tracks': 0,              # Total number of tracks
            'track_started': False,         # Track has started playing (pos > 0)
            'track_start_time': 0,          # Timestamp when track started
        }
    
    def get(self, key):
        with self._lock:
            return self.state.get(key)
    
    def set(self, key, value):
        with self._lock:
            self.state[key] = value
    
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

# ----------------------
# DIDL-Lite Metadata Functions
# ----------------------

def build_didl_with_size(url, title, protocol_info, size=None):
    """Build DIDL-Lite XML metadata"""
    title_escaped = escape(title or "Track")
    size_attr = f' size="{int(size)}"' if isinstance(size, (int, float)) and size > 0 else ''
    
    return f'''<DIDL-Lite xmlns="urn:schemas-upnp-org:metadata-1-0/DIDL-Lite/" xmlns:dc="http://purl.org/dc/elements/1.1/" xmlns:upnp="urn:schemas-upnp-org:metadata-1-0/upnp/">
<item id="1" parentID="0" restricted="1">
<dc:title>{title_escaped}</dc:title>
<upnp:class>object.item.audioItem.musicTrack</upnp:class>
<res protocolInfo="{protocol_info}"{size_attr}>{escape(url)}</res>
</item>
</DIDL-Lite>'''

def minimal_protocol_info(mime):
    """Minimal protocolInfo for DIDL"""
    return f'http-get:*:{mime}:*'

def protocol_info_wav_lpcm(alt_x=False):
    """Full protocolInfo for WAV/LPCM with DLNA flags"""
    mime = 'audio/x-wav' if alt_x else 'audio/wav'
    flags = 'DLNA.ORG_PN=LPCM'
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
            return os.path.getsize(full_path)
    except Exception:
        return None

# ----------------------
# SOAP/UPnP Functions
# ----------------------

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
    body = '''<u:Stop xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">
<InstanceID>0</InstanceID>
</u:Stop>'''
    
    envelope = f'''<?xml version="1.0"?>
<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
<s:Body>{body}</s:Body>
</s:Envelope>'''
    
    action = "urn:schemas-upnp-org:service:AVTransport:1#Stop"
    ok, _ = send_soap_request(control_url, envelope, action, debug=debug, timeout=10, retries=1, backoff=0.5)
    return ok

def pause_upnp(control_url, debug=False):
    """Pause UPnP playback"""
    body = '''<u:Pause xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">
<InstanceID>0</InstanceID>
</u:Pause>'''
    
    envelope = f'''<?xml version="1.0"?>
<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
<s:Body>{body}</s:Body>
</s:Envelope>'''
    
    action = "urn:schemas-upnp-org:service:AVTransport:1#Pause"
    ok, _ = send_soap_request(control_url, envelope, action, debug=debug, timeout=10, retries=1, backoff=0.5)
    return ok

def play_upnp(control_url, debug=False):
    """Play UPnP"""
    body = '''<u:Play xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">
<InstanceID>0</InstanceID>
<Speed>1</Speed>
</u:Play>'''
    
    soap_body = f'''<?xml version="1.0"?>
<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
<s:Body>{body}</s:Body>
</s:Envelope>'''
    
    action = "urn:schemas-upnp-org:service:AVTransport:1#Play"
    try:
        ok, _ = send_soap_request(control_url, soap_body, action, debug, timeout=20)
        return ok
    except Exception as e:
        if debug:
            print("[SOAP ERROR Play]", e)
        return False

def get_position_info(control_url, debug=False):
    """Get current position info (Wireshark: called every ~970ms)"""
    body = '''<u:GetPositionInfo xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">
<InstanceID>0</InstanceID>
</u:GetPositionInfo>'''
    
    envelope = f'''<?xml version="1.0"?>
<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
<s:Body>{body}</s:Body>
</s:Envelope>'''
    
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
    body = f'''<u:SetAVTransportURI xmlns:u="urn:schemas-upnp-org:service:AVTransport:1">
<InstanceID>0</InstanceID>
<CurrentURI>{escape(url)}</CurrentURI>
<CurrentURIMetaData>{escape(metadata)}</CurrentURIMetaData>
</u:SetAVTransportURI>'''
    
    envelope = f'''<?xml version="1.0"?>
<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
<s:Body>{body}</s:Body>
</s:Envelope>'''
    
    action = "urn:schemas-upnp-org:service:AVTransport:1#SetAVTransportURI"
    ok, _ = send_soap_request(control_url, envelope, action, debug=debug, timeout=30, retries=3, backoff=0.75)
    return ok

def set_avtransport_uri_variants(avtransport_url, url, filename, directory, actual_filename, debug=False):
    """Try multiple DIDL variants for DAC compatibility"""
    try:
        stop_upnp(avtransport_url, debug=debug)
    except Exception:
        pass
    time.sleep(0.8)
    
    sz = filesize_bytes_aiff_as_wav(directory, actual_filename)
    ext = os.path.splitext(filename)[1].lower()
    
    attempts = []
    attempts.append(('empty', ''))
    
    if ext in ('.wav', '.aif', '.aiff'):
        attempts.append(('didl_min_wav', build_didl_with_size(url, filename, minimal_protocol_info('audio/wav'), sz)))
        attempts.append(('didl_min_xwav', build_didl_with_size(url, filename, minimal_protocol_info('audio/x-wav'), sz)))
        
        pi_wav = protocol_info_wav_lpcm(alt_x=False)
        pi_xwav = protocol_info_wav_lpcm(alt_x=True)
        attempts.append(('didl_lpcm_wav', build_didl_with_size(url, filename, pi_wav[1], sz)))
        attempts.append(('didl_lpcm_xwav', build_didl_with_size(url, filename, pi_xwav[1], sz)))
    else:
        base_mime = 'audio/mpeg' if ext == '.mp3' else 'application/octet-stream'
        attempts.append(('didl_min_generic', build_didl_with_size(url, filename, minimal_protocol_info(base_mime), sz)))
    
    for i, (label, meta) in enumerate(attempts, 1):
        if debug:
            print(f"[SetAVTransportURI] Attempt {i}/{len(attempts)}: {label} (meta_len={len(meta) if meta else 0})")
        
        ok = set_avtransport_uri(avtransport_url, url, meta, debug=debug)
        if ok:
            if debug:
                print(f"[SetAVTransportURI] âœ“ Success with variant: {label}")
            return True
        
        time.sleep(1.0)
    
    return False

# ----------------------
# Polling Thread with FIXED Auto-Next
# ----------------------

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
        while self.running:
            if not SHARED_STATE.get('is_playing') or self.paused:
                time.sleep(0.1)
                continue
            
            try:
                start = time.time()
                
                ok, position_info = get_position_info(self.control_url, debug=self.debug)
                
                if ok and position_info:
                    pos = position_info['position']
                    dur = position_info['duration']
                    
                    SHARED_STATE.update({
                        'position': pos,
                        'duration': dur,
                        'last_update': time.time()
                    })
                    
                    # FIXED: Auto-next detection for Play All
                    if SHARED_STATE.get('play_all_enabled'):
                        track_started = SHARED_STATE.get('track_started')
                        track_start_time = SHARED_STATE.get('track_start_time')
                        last_pos = SHARED_STATE.get('last_position')
                        
                        # Mark track as started when position > 2s (grace period)
                        if not track_started and pos > 2.0:
                            SHARED_STATE.update({
                                'track_started': True,
                                'track_start_time': time.time()
                            })
                            if self.debug:
                                print(f"[Poll] Track started playing (pos={pos:.1f}s)")
                        
                        # Only detect track-end AFTER track has started AND grace period passed
                        if track_started:
                            time_since_start = time.time() - track_start_time
                            
                            # Track ended (position reset OR near end) - with 3s grace period
                            if time_since_start > 3.0:  # At least 3s after track started
                                track_ended = False
                                
                                # Position jumped backwards significantly (track ended and reset)
                                if last_pos > 5 and pos < 3 and dur > 0:
                                    track_ended = True
                                    if self.debug:
                                        print(f"[Poll] Track ended (position reset: {last_pos:.1f}s â†’ {pos:.1f}s)")
                                
                                # Position near end of track
                                elif dur > 0 and pos >= dur - 2:
                                    track_ended = True
                                    if self.debug:
                                        print(f"[Poll] Track ended (near end: {pos:.1f}s / {dur:.1f}s)")
                                
                                if track_ended:
                                    current_idx = SHARED_STATE.get('current_track_idx')
                                    total_tracks = SHARED_STATE.get('total_tracks')
                                    
                                    if current_idx < total_tracks - 1:
                                        if self.debug:
                                            print(f"[Poll] Auto-next to track {current_idx + 2}")
                                        
                                        # Reset track_started flag for next track
                                        SHARED_STATE.set('track_started', False)
                                        COMMAND_QUEUE.put(Command(CommandType.NEXT))
                                    else:
                                        SHARED_STATE.set('play_all_enabled', False)
                                        if self.debug:
                                            print(f"[Poll] Play All finished - last track complete")
                        
                        SHARED_STATE.set('last_position', pos)
                    
                    if self.debug:
                        print(f"[Poll] Position: {pos:.1f}s / {dur:.1f}s")
                
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

# ----------------------
# Command Worker Thread
# ----------------------

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
        while self.running:
            try:
                cmd = COMMAND_QUEUE.get(block=True, timeout=0.5)
                
                if self.debug:
                    print(f"[CommandWorker] Processing: {cmd.type}")
                
                if cmd.type == CommandType.PLAY:
                    self._handle_play(cmd)
                elif cmd.type == CommandType.PAUSE:
                    self._handle_pause(cmd)
                elif cmd.type == CommandType.STOP:
                    self._handle_stop(cmd)
                elif cmd.type == CommandType.NEXT:
                    self._handle_next(cmd)
                elif cmd.type == CommandType.PREVIOUS:
                    self._handle_previous(cmd)
                elif cmd.type == CommandType.SET_TRACK:
                    self._handle_set_track(cmd)
                elif cmd.type == CommandType.QUIT:
                    self.running = False
                    
            except Empty:
                continue
            except Exception as e:
                if self.debug:
                    print(f"[CommandWorker] Error: {e}")
                SHARED_STATE.set('error', str(e))
    
    def _handle_play(self, cmd):
        """Handle play command with DIDL metadata variants"""
        track_idx = cmd.args.get('track_idx', SHARED_STATE.get('current_track_idx'))
        
        if track_idx < 0 or track_idx >= len(self.files):
            print(f"[CommandWorker] Invalid track index: {track_idx}")
            return
        
        filename = self.files[track_idx]
        full_path = os.path.join(self.directory, filename)
        
        SHARED_STATE.update({
            'current_track_idx': track_idx,
            'current_track_name': filename,
            'is_playing': True,
            'transport_state': 'TRANSITIONING',
            'track_started': False,      # Reset for new track
            'track_start_time': 0,
            'last_position': 0
        })
        
        ext = os.path.splitext(filename)[1].lower()
        if ext in ('.aif', '.aiff'):
            wav_name = os.path.splitext(filename)[0] + '.wav'
            file_url = f"http://{self.advertise_host}:{self.port}/{urllib.parse.quote(wav_name)}"
        else:
            file_url = f"http://{self.advertise_host}:{self.port}/{urllib.parse.quote(filename)}"
        
        stop_upnp(self.control_url, debug=self.debug)
        time.sleep(0.3)
        
        ok = set_avtransport_uri_variants(
            self.control_url, 
            file_url, 
            wav_name if ext in ('.aif', '.aiff') else filename,
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
            print(f"[CommandWorker] âœ“ Playing: {filename}")
        else:
            SHARED_STATE.update({'is_playing': False, 'error': 'Play failed'})
            print(f"[CommandWorker] âœ— Play failed")
    
    def _handle_pause(self, cmd):
        ok = pause_upnp(self.control_url, debug=self.debug)
        if ok:
            SHARED_STATE.update({'is_playing': False, 'transport_state': 'PAUSED'})
            print(f"[CommandWorker] âœ“ Paused")
        else:
            print(f"[CommandWorker] âœ— Pause failed")
    
    def _handle_stop(self, cmd):
        ok = stop_upnp(self.control_url, debug=self.debug)
        if ok:
            SHARED_STATE.update({'is_playing': False, 'transport_state': 'STOPPED'})
            print(f"[CommandWorker] âœ“ Stopped")
        else:
            print(f"[CommandWorker] âœ— Stop failed")
    
    def _handle_next(self, cmd):
        current = SHARED_STATE.get('current_track_idx')
        if current < len(self.files) - 1:
            next_idx = current + 1
            COMMAND_QUEUE.put(Command(CommandType.PLAY, {'track_idx': next_idx}))
        else:
            print(f"[CommandWorker] Already at last track")
    
    def _handle_previous(self, cmd):
        current = SHARED_STATE.get('current_track_idx')
        if current > 0:
            prev_idx = current - 1
            COMMAND_QUEUE.put(Command(CommandType.PLAY, {'track_idx': prev_idx}))
        else:
            print(f"[CommandWorker] Already at first track")
    
    def _handle_set_track(self, cmd):
        track_idx = cmd.args.get('track_idx', 0)
        COMMAND_QUEUE.put(Command(CommandType.PLAY, {'track_idx': track_idx}))
    
    def stop(self):
        self.running = False

# ----------------------
# HTTP Server
# ----------------------

BASE_DIR = "."

def ensure_mime_types():
    mimetypes.add_type('audio/wav', '.wav')
    mimetypes.add_type('audio/flac', '.flac')
    mimetypes.add_type('audio/aac', '.aac')
    mimetypes.add_type('audio/mpeg', '.mp3')
    mimetypes.add_type('audio/mp4', '.m4a')
    mimetypes.add_type('audio/ogg', '.ogg')

class StaticAudioHandler(http.server.SimpleHTTPRequestHandler):
    """HTTP handler with AIFFâ†’WAV conversion and chunked streaming"""
    
    def do_GET(self):
        from urllib.parse import unquote
        path = unquote(self.path[1:])
        full_path = os.path.join(BASE_DIR, path)
        
        if path.lower().endswith(".wav") and not os.path.exists(full_path):
            possible_aiff = full_path[:-4] + ".aiff"
            possible_aif = full_path[:-4] + ".aif"
            
            for candidate in (possible_aiff, possible_aif):
                if os.path.exists(candidate):
                    try:
                        info = sf.info(candidate)
                        samplerate = info.samplerate
                        nch = info.channels
                        nframes = info.frames
                        sampwidth = 2
                        
                        datasize = nframes * nch * sampwidth
                        total_size = 44 + datasize
                        
                        header = self._wav_header_bytes(nch, sampwidth, samplerate, nframes)
                        
                        self.send_response(200)
                        self.send_header("Content-Type", "audio/wav")
                        self.send_header("Content-Length", str(total_size))
                        self.send_header("Accept-Ranges", "bytes")
                        self.end_headers()
                        
                        self.wfile.write(header)
                        
                        CHUNK_SIZE = 65536
                        with sf.SoundFile(candidate, 'r') as f:
                            while True:
                                try:
                                    data = f.read(CHUNK_SIZE, dtype='int16')
                                    if data.size == 0:
                                        break
                                    
                                    self.wfile.write(data.tobytes())
                                    self.wfile.flush()
                                    
                                except (BrokenPipeError, ConnectionResetError):
                                    if hasattr(self.server, 'debug') and self.server.debug:
                                        print(f"[HTTP] Client disconnected: {candidate}")
                                    break
                                except Exception as e:
                                    if hasattr(self.server, 'debug') and self.server.debug:
                                        print(f"[HTTP] Streaming error: {e}")
                                    break
                        
                        if hasattr(self.server, 'debug') and self.server.debug:
                            print(f"[HTTP] Streamed AIFFâ†’WAV: {candidate}")
                        return
                        
                    except BrokenPipeError:
                        return
                    except Exception as e:
                        print(f"[HTTP] Error setting up stream for {candidate}: {e}")
                        try:
                            self.send_error(500)
                        except:
                            pass
                        return
        
        return super().do_GET()
    
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
        if hasattr(self.server, 'debug') and self.server.debug:
            super().log_message(format, *args)

class ThreadedHTTPServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True

def start_http_server(directory, host, port, debug=False):
    global BASE_DIR
    BASE_DIR = os.path.abspath(directory)
    
    httpd = ThreadedHTTPServer((host, port), StaticAudioHandler)
    httpd.debug = debug
    
    t = threading.Thread(target=httpd.serve_forever, daemon=True)
    t.start()
    
    print(f"[HTTP] Serving {directory} on {host}:{port}")
    print(f"[HTTP] BASE_DIR: {BASE_DIR}")
    return httpd

# ----------------------
# UPnP Discovery
# ----------------------

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
                    devices.append(location)
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
    audio_ext = ('.wav', '.flac', '.aac', '.mp3', '.m4a', '.ogg', '.aif', '.aiff')
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

# ----------------------
# Interactive UI with Auto-Stop on Quit
# ----------------------

def interactive_ui(files, polling_thread, command_worker, debug=False):
    print(f"\n{'='*80}")
    print("ULTIMATE HIFI AUDIO PLAYER v4.6 - Auto-Stop on Quit")
    print(f"{'='*80}")
    print("Threading: Command Queue + 970ms Polling (Wireshark-validated)")
    print("Features: FIXED Play All + Auto-Stop on Quit")
    print(f"{'='*80}\n")
    
    # Set total tracks count
    SHARED_STATE.set('total_tracks', len(files))
    
    while True:
        state = SHARED_STATE.get_all()
        
        print(f"\n{'='*80}")
        print("AVAILABLE TRACKS")
        print(f"{'='*80}")
        
        for i, f in enumerate(files):
            if i == state['current_track_idx'] and state['is_playing']:
                prefix = "â–¶"
            else:
                prefix = " "
            print(f"{prefix} {i+1:2d}. {f}")
        
        print(f"\n{'='*80}")
        print("STATUS")
        print(f"{'='*80}")
        
        if state['is_playing']:
            pos = state['position']
            dur = state['duration']
            print(f"â–¶ Playing: {state['current_track_name']}")
            
            if state['play_all_enabled']:
                start_idx = state['play_all_start_idx']
                print(f"  Mode: Sequential (Play All from track {start_idx+1})")
            else:
                print(f"  Mode: Single Track")
            
            print(f"  Position: {int(pos//60)}:{int(pos%60):02d} / {int(dur//60)}:{int(dur%60):02d}")
        else:
            print(f"â¸ State: {state['transport_state']}")
        
        if state['error']:
            print(f"âœ— Error: {state['error']}")
            SHARED_STATE.set('error', None)
        
        print(f"\n{'='*80}")
        print("COMMANDS")
        print(f"{'='*80}")
        print(f"1-{len(files)}: Play single track")
        print(f"a: Play All from track (sequential)")
        print(f"p: Play/Resume | s: Stop | n: Next | b: Previous")
        print(f"q: Quit")
        print(f"{'='*80}")
        
        choice = input("\nCommand: ").strip().lower()
        
        if choice == 'q':
            # NEW: Auto-stop playback before quitting
            if state['is_playing']:
                print("\n[Quit] Stopping playback before exit...")
                SHARED_STATE.set('play_all_enabled', False)  # Disable Play All
                COMMAND_QUEUE.put(Command(CommandType.STOP))
                time.sleep(0.5)  # Wait for stop to complete
            
            COMMAND_QUEUE.put(Command(CommandType.QUIT))
            break
        elif choice == 'a':
            # Play All mode
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
                    COMMAND_QUEUE.put(Command(CommandType.SET_TRACK, {'track_idx': start_idx}))
                    print(f"â–¶ Starting Play All from track {start_idx+1}")
                else:
                    print("Invalid track number")
            except ValueError:
                print("Invalid input")
        elif choice == 'p':
            current_idx = state['current_track_idx']
            COMMAND_QUEUE.put(Command(CommandType.PLAY, {'track_idx': current_idx}))
        elif choice == 's':
            SHARED_STATE.set('play_all_enabled', False)  # Stop Play All
            COMMAND_QUEUE.put(Command(CommandType.STOP))
        elif choice == 'n':
            if state['current_track_idx'] < len(files) - 1:
                COMMAND_QUEUE.put(Command(CommandType.NEXT))
            else:
                print("Already at last track")
        elif choice == 'b':
            if state['current_track_idx'] > 0:
                COMMAND_QUEUE.put(Command(CommandType.PREVIOUS))
            else:
                print("Already at first track")
        else:
            try:
                sel = int(choice)
                if 1 <= sel <= len(files):
                    SHARED_STATE.set('play_all_enabled', False)  # Single track mode
                    COMMAND_QUEUE.put(Command(CommandType.SET_TRACK, {'track_idx': sel - 1}))
                else:
                    print("Invalid track number")
            except ValueError:
                print("Invalid command")

# ----------------------
# Main
# ----------------------

def main():
    parser = argparse.ArgumentParser(
        description="Ultimate HiFi Audio Player v4.6 - Auto-Stop on Quit",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --dir /music/
  %(prog)s --dir /music/ --debug
"""
    )
    
    parser.add_argument("--dir", required=True, help="Directory with audio files")
    parser.add_argument("--bind-host", default="0.0.0.0", help="HTTP server bind host")
    parser.add_argument("--port", type=int, default=8000, help="HTTP server port")
    parser.add_argument("--advertise-host", default=None, help="Host/IP in URLs for renderer")
    parser.add_argument("--discover-timeout", type=int, default=5, help="SSDP discovery timeout (s)")
    parser.add_argument("--debug", action="store_true", help="Enable debug logging")
    
    args = parser.parse_args()
    
    advertise_host = args.advertise_host or get_lan_advertise_ip()
    if advertise_host in ("0.0.0.0", "127.0.0.1"):
        advertise_host = get_lan_advertise_ip() or advertise_host
    
    print(f"\n{'='*80}")
    print("HIFI AUDIO PLAYER v4.6 - AUTO-STOP ON QUIT")
    print(f"{'='*80}")
    print("Architecture: Command Queue + 970ms Polling (Wireshark)")
    print("Features: DIDL + Streaming + FIXED Play All + Auto-Stop on Quit")
    print(f"{'='*80}\n")
    
    print(f"[HTTP] Advertised host: {advertise_host}")
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
        httpd.shutdown()
        return
    
    avtransport_url = None
    connectionmgr_url = None
    
    for desc_url in devices:
        avtransport_url, connectionmgr_url = get_service_urls(desc_url, debug=args.debug)
        if avtransport_url:
            print(f"âœ“ AVTransport: {avtransport_url}")
            if connectionmgr_url:
                print(f"âœ“ ConnectionManager: {connectionmgr_url}")
            break
    
    if not avtransport_url:
        print("âœ— No UPnP renderer with AVTransport found")
        httpd.shutdown()
        return
    
    files = list_audio_files(args.dir)
    if not files:
        print("No audio files found")
        httpd.shutdown()
        return
    
    print(f"\nâœ“ Found {len(files)} audio files")
    
    print("\n[Threading] Starting Command Worker...")
    command_worker = CommandWorkerThread(
        avtransport_url, files, args.dir, advertise_host, args.port, debug=args.debug
    )
    command_worker.start()
    
    print("[Threading] Starting Polling Thread (970ms interval)...")
    polling_thread = PollingThread(avtransport_url, interval_ms=970, debug=args.debug)
    polling_thread.start()
    
    print("[Threading] âœ“ All threads started\n")
    
    try:
        interactive_ui(files, polling_thread, command_worker, debug=args.debug)
    except KeyboardInterrupt:
        print("\n\nInterrupted by user.")
    finally:
        print("\n[Shutdown] Stopping threads...")
        polling_thread.stop()
        command_worker.stop()
        
        print("[Shutdown] Stopping HTTP server...")
        try:
            httpd.shutdown()
        except Exception:
            pass
        
        print("[Shutdown] âœ“ Clean exit")

if __name__ == "__main__":
    main()
