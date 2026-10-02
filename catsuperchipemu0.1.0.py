#!/usr/bin/env python3
"""catsuperchipemu 0.1.0 - CHIP-8 + modern SUPER-CHIP, blue/black Tk GUI.

Run: python3 catsuperchipemu0.1.0.py [optional-rom.ch8]
Python 3.9+ and Tk required. The main window is fixed at 600x400.
Load ROM -> Play; Space pauses; Ctrl/Cmd+O loads, Ctrl/Cmd+R resets, F1 helps.
Physical 1234/QWER/ASDF/ZXCV maps to CHIP-8 123C/456D/789E/A0BF.
A tiny original built-in demo is available through Game > Built-in demo.

Supports classic 64x32 CHIP-8 plus modern SUPER-CHIP: 128x64 mode, 16x16
sprites in both modes, scrolling, large hexadecimal font, interpreter exit,
and eight RPL flags. Flags persist across Reset in RAM; loading a ROM clears
them. Settings, tones, flags, demo and emulated RAM stay in memory. ROMs are
read-only. No saves, configuration, logs, audio files or network access.

Compatibility profiles: SUPER-CHIP (default, Vx jumps); CHIP-8 Modern
(V0 jumps); Classic VIP (Vy shifts, advance I, logic VF clear, display wait).
Modern SCHIP uses logical-pixel scrolling and clears display on mode select.
This is not HP48 cycle-accurate emulation: historical half-pixel scrolling,
8x16 low-res sprites and collision-row counts are not emulated. XO-CHIP and
other systems are unsupported. Legacy 0nnn machine-code calls are ignored.

Sound uses native Core Audio on macOS or an already-installed pygame mixer
elsewhere. Audio buffers are RAM-only; no automatic dependency installs.
A silent fallback is shown when no working audio device is available.
Optional outside macOS: python3 -m pip install pygame

Implementation references (not runtime dependencies):
https://chip-8.github.io/extensions/
https://github.com/Timendus/chip8-test-suite
https://github.com/Timendus/chip8-test-suite/blob/main/legacy-superchip.md
"""

import sys
sys.dont_write_bytecode = True  # FILES OFF also applies to Python import caches.

import argparse
import math
import random
import time
from dataclasses import dataclass
from pathlib import Path

TITLE = "catsuperchipemu 0.1.0 by ac [c] kondo ac 1999-2026"
VERSION = "0.1.0"
FONT_START = 0x50
FONT = bytes.fromhex(
    "F0909090F0 2060202070 F010F080F0 F010F010F0 9090F01010 "
    "F080F010F0 F080F090F0 F010204040 F090F090F0 F090F010F0 "
    "F090F09090 E090E090E0 F0808080F0 E0909090E0 F080F080F0 F080F08080"
)
# Double each 4-bit-wide small font pixel to obtain readable 8x10 glyphs.
# Original generator; extends the decimal SCHIP font to all hexadecimal digits.
BIG_FONT_START = 0xA0
BIG_FONT = bytes(value for row in FONT for value in
                 [sum(3 << (6 - 2 * bit) for bit in range(4)
                      if row & (0x80 >> bit))] * 2)

KEY_MAP = dict(zip("1234qwerasdfzxcv", (1, 2, 3, 12, 4, 5, 6, 13,
                                                7, 8, 9, 14, 10, 0, 11, 15)))


class EmulationError(Exception):
    """A malformed or unsupported ROM operation, safe to show in the UI."""


@dataclass
class Compatibility:
    shift_vy: bool = False
    increment_i: bool = False
    reset_vf: bool = False
    jump_vx: bool = False
    draw_wrap: bool = False
    wait_for_release: bool = True
    display_wait: bool = False

    @classmethod
    def schip(cls):
        return cls(jump_vx=True)

    @classmethod
    def classic(cls):
        return cls(shift_vy=True, increment_i=True, reset_vf=True, display_wait=True)


class Chip8:
    """Display/audio independent core. Nothing here opens or writes a file."""

    def __init__(self, compatibility=None, rng=None):
        self.compatibility = compatibility or Compatibility()
        self.rng = rng or random.Random()
        self.rom = b""
        self.rpl = [0] * 8
        self.reset()

    def reset(self):
        self.memory = bytearray(4096)
        self.memory[FONT_START:FONT_START + len(FONT)] = FONT
        self.memory[BIG_FONT_START:BIG_FONT_START + len(BIG_FONT)] = BIG_FONT
        self.memory[0x200:0x200 + len(self.rom)] = self.rom
        self.v = [0] * 16
        self.i = 0
        self.pc = 0x200
        self.stack = []
        self.hires = False
        self.width, self.height = 64, 32
        self.halted = False
        self.display = bytearray(self.width * self.height)
        self.keys = [False] * 16
        self.delay_timer = 0
        self.sound_timer = 0
        self.waiting_register = None
        self.waiting_key = None
        self.draw_ready = True
        self.dirty = True
        self.instruction_count = 0

    def load_rom(self, data):
        data = bytes(data)
        if not 2 <= len(data) <= 4096 - 0x200:
            raise EmulationError("ROM must contain 2 to 3584 bytes for CHIP-8 / SUPER-CHIP.")
        self.rom = data
        self.rpl[:] = [0] * 8
        self.reset()

    def key_down(self, key):
        if not 0 <= key < 16:
            return
        was_down = self.keys[key]
        self.keys[key] = True
        if self.waiting_register is not None and self.waiting_key is None and not was_down:
            if self.compatibility.wait_for_release:
                self.waiting_key = key
            else:
                self.v[self.waiting_register] = key
                self.waiting_register = None

    def key_up(self, key):
        if not 0 <= key < 16:
            return
        self.keys[key] = False
        if self.waiting_register is not None and self.waiting_key == key:
            self.v[self.waiting_register] = key
            self.waiting_register = None
            self.waiting_key = None

    def release_keys(self):
        # Focus loss is not a deliberate ROM input. Cancel pending release,
        # leave Fx0A waiting, and avoid phantom/stuck keys on return.
        self.keys[:] = [False] * 16
        self.waiting_key = None

    def tick_timers(self, n=1):
        n = max(0, int(n))
        self.delay_timer = max(0, self.delay_timer - n)
        self.sound_timer = max(0, self.sound_timer - n)
        if n:
            self.draw_ready = True

    def _memory_range(self, start, count):
        if start < 0 or start + count > len(self.memory):
            raise EmulationError(f"Memory access outside 0x000–0xFFF (I=0x{start:04X}, {count} bytes).")

    def step(self):
        """Execute one opcode; False means awaiting a key or display refresh."""
        if self.halted or self.waiting_register is not None:
            return False
        self._memory_range(self.pc, 2)
        address = self.pc
        op = (self.memory[address] << 8) | self.memory[address + 1]
        group, x, y, n = op >> 12, (op >> 8) & 15, (op >> 4) & 15, op & 15
        nn, nnn = op & 255, op & 4095
        c = self.compatibility
        # Deferring the fetch leaves PC unchanged until the next 60 Hz tick.
        if group == 0xD and c.display_wait and not self.draw_ready:
            return False
        self.pc += 2
        self.instruction_count += 1
        vx, vy = self.v[x], self.v[y]  # Snapshot operands before writing VF.

        if op == 0x00E0:
            self.display[:] = bytes(self.width * self.height)
            self.dirty = True
        elif op == 0x00EE:
            if not self.stack:
                raise EmulationError(f"Stack underflow at 0x{address:03X}.")
            self.pc = self.stack.pop()
        elif op in (0x00FE, 0x00FF):
            self.hires = op == 0x00FF
            self.width, self.height = (128, 64) if self.hires else (64, 32)
            self.display = bytearray(self.width * self.height)
            self.dirty = True
            self.draw_ready = True
        elif op == 0x00FD:
            self.halted = True
            self.sound_timer = 0
            self.release_keys()
        elif op in (0x00FB, 0x00FC):
            self._scroll(4 if op == 0x00FB else -4, 0)
        elif op & 0xFFF0 == 0x00C0:
            self._scroll(0, n)
        elif group == 0:
            if op & 0xFFF0 in (0x00B0, 0x00D0):
                raise EmulationError(f"0x{op:04X} is not a standard SUPER-CHIP instruction (scroll-up extension).")
            # RCA 1802 machine-code calls have no meaning on a modern host.
        elif group == 1:
            self.pc = nnn
        elif group == 2:
            if len(self.stack) >= 16:
                raise EmulationError(f"Stack overflow at 0x{address:03X} (maximum 16 calls).")
            self.stack.append(self.pc)
            self.pc = nnn
        elif group == 3:
            self.pc += 2 if vx == nn else 0
        elif group == 4:
            self.pc += 2 if vx != nn else 0
        elif group == 5 and n == 0:
            self.pc += 2 if vx == vy else 0
        elif group == 6:
            self.v[x] = nn
        elif group == 7:
            self.v[x] = (vx + nn) & 255
        elif group == 8:
            if n == 0:
                self.v[x] = vy
            elif n in (1, 2, 3):
                self.v[x] = (vx | vy) if n == 1 else (vx & vy) if n == 2 else (vx ^ vy)
                if c.reset_vf:
                    self.v[15] = 0
            elif n == 4:
                self.v[x] = (vx + vy) & 255
                self.v[15] = int(vx + vy > 255)
            elif n == 5:
                self.v[x] = (vx - vy) & 255
                self.v[15] = int(vx >= vy)
            elif n == 7:
                self.v[x] = (vy - vx) & 255
                self.v[15] = int(vy >= vx)
            elif n == 6:
                source = vy if c.shift_vy else vx
                self.v[x] = source >> 1
                self.v[15] = source & 1
            elif n == 14:
                source = vy if c.shift_vy else vx
                self.v[x] = (source << 1) & 255
                self.v[15] = (source >> 7) & 1
            else:
                self._bad_opcode(op, address)
        elif group == 9 and n == 0:
            self.pc += 2 if vx != vy else 0
        elif group == 10:
            self.i = nnn
        elif group == 11:
            self.pc = nnn + self.v[x if c.jump_vx else 0]
        elif group == 12:
            self.v[x] = self.rng.randrange(256) & nn
        elif group == 13:
            width, height = self.width, self.height
            sprite_width, sprite_height = (16, 16) if n == 0 else (8, n)
            row_bytes = sprite_width // 8
            self._memory_range(self.i, sprite_height * row_bytes)
            start_x, start_y, collision = vx % width, vy % height, 0
            for row in range(sprite_height):
                py = start_y + row
                if py >= height and not c.draw_wrap:
                    break
                offset = self.i + row * row_bytes
                sprite = self.memory[offset]
                if row_bytes == 2:
                    sprite = (sprite << 8) | self.memory[offset + 1]
                for col in range(sprite_width):
                    px = start_x + col
                    if px >= width and not c.draw_wrap:
                        break
                    if sprite & (1 << (sprite_width - 1 - col)):
                        idx = (py % height) * width + px % width
                        collision |= self.display[idx]
                        self.display[idx] ^= 1
            self.v[15] = collision
            self.dirty = True
            self.draw_ready = False
        elif group == 14 and nn in (0x9E, 0xA1):
            pressed = self.keys[vx & 15]
            self.pc += 2 if pressed == (nn == 0x9E) else 0
        elif group == 15:
            if nn == 0x07:
                self.v[x] = self.delay_timer
            elif nn == 0x0A:
                self.waiting_register = x
                held = next((key for key in range(16) if self.keys[key]), None)
                if c.wait_for_release:
                    self.waiting_key = held
                elif held is not None:
                    self.v[x] = held
                    self.waiting_register = None
            elif nn == 0x15:
                self.delay_timer = vx
            elif nn == 0x18:
                self.sound_timer = vx
            elif nn == 0x1E:
                self.i = (self.i + vx) & 0xFFFF
            elif nn == 0x29:
                self.i = FONT_START + (vx & 15) * 5
            elif nn == 0x30:
                self.i = BIG_FONT_START + (vx & 15) * 10
            elif nn in (0x75, 0x85):
                if x > 7:
                    raise EmulationError("SUPER-CHIP has 8 RPL flags: Fx75/Fx85 require x <= 7.")
                if nn == 0x75:
                    self.rpl[:x + 1] = self.v[:x + 1]
                else:
                    self.v[:x + 1] = self.rpl[:x + 1]
            elif nn == 0x33:
                self._memory_range(self.i, 3)
                self.memory[self.i:self.i + 3] = bytes((vx // 100, vx // 10 % 10, vx % 10))
            elif nn in (0x55, 0x65):
                self._memory_range(self.i, x + 1)
                if nn == 0x55:
                    self.memory[self.i:self.i + x + 1] = bytes(self.v[:x + 1])
                else:
                    self.v[:x + 1] = self.memory[self.i:self.i + x + 1]
                if c.increment_i:
                    self.i = (self.i + x + 1) & 0xFFFF
            else:
                self._bad_opcode(op, address)
        else:
            self._bad_opcode(op, address)
        return True

    def _scroll(self, dx, dy):
        """Modern SCHIP scrolling in logical pixels, with zero-filled edges."""
        w, h = self.width, self.height
        output = bytearray(w * h)
        for y in range(h):
            sy = y - dy
            if 0 <= sy < h:
                if dx >= 0:
                    output[y*w + dx:(y+1)*w] = self.display[sy*w:(sy+1)*w - dx]
                else:
                    output[y*w:(y+1)*w + dx] = self.display[sy*w - dx:(sy+1)*w]
        self.display = output
        self.dirty = True

    @staticmethod
    def _bad_opcode(op, address):
        raise EmulationError(f"Unsupported opcode 0x{op:04X} at 0x{address:03X}.")


"""RAM-only CHIP-8 tone output. Nothing in this module writes a file.

macOS uses the system AudioToolbox framework through ctypes. Other systems,
or a Mac without a usable AudioToolbox output, can use an installed pygame.
No dependency is installed automatically. Call close() before destroying Tk.
"""
import atexit as _audio_atexit
import array as _audio_array
import ctypes as _audio_ctypes
import math as _audio_math
import os as _audio_os
import sys as _audio_sys

# Also prevent optional third-party imports from creating bytecode files.
_audio_sys.dont_write_bytecode = True


def _audio_level(value):
    value = float(value)
    return max(0.0, min(1.0, value)) if _audio_math.isfinite(value) else 0.0


def _audio_pcm(frequency, sample_rate=48000, channels=1):
    """A seamless, approximately 50 ms, signed-16-bit sine loop in RAM.

    Fit a whole number of cycles to the buffer so repeating it never creates
    a boundary click. At 440 Hz / 48 kHz the requested frequency is exact.
    Other pitches are rounded by at most a small fraction of one percent.
    """
    cycles = max(1, round(frequency * 0.05))
    frames = max(16, round(sample_rate * cycles / frequency))
    samples = _audio_array.array('h')
    for i in range(frames):
        sample = round(16383 * _audio_math.sin(2 * _audio_math.pi * cycles * i / frames))
        samples.extend([sample] * channels)
    # Both native AudioToolbox and pygame use native-endian signed PCM here.
    return samples.tobytes()


class _MacMemoryAudio:
    """AudioQueue owns the buffers; the callback simply loops their PCM."""

    def __init__(self, frequency, volume):
        C = _audio_ctypes
        self._queue = C.c_void_p()
        self._closed = False
        self._started = False
        self.error = None
        self._lib = C.CDLL('/System/Library/Frameworks/AudioToolbox.framework/AudioToolbox')

        class Format(C.Structure):
            _fields_ = [
                ('mSampleRate', C.c_double), ('mFormatID', C.c_uint32),
                ('mFormatFlags', C.c_uint32), ('mBytesPerPacket', C.c_uint32),
                ('mFramesPerPacket', C.c_uint32), ('mBytesPerFrame', C.c_uint32),
                ('mChannelsPerFrame', C.c_uint32), ('mBitsPerChannel', C.c_uint32),
                ('mReserved', C.c_uint32),
            ]

        class Buffer(C.Structure):
            _fields_ = [
                ('mAudioDataBytesCapacity', C.c_uint32), ('mAudioData', C.c_void_p),
                ('mAudioDataByteSize', C.c_uint32), ('mUserData', C.c_void_p),
                ('mPacketDescriptionCapacity', C.c_uint32),
                ('mPacketDescriptions', C.c_void_p), ('mPacketDescriptionCount', C.c_uint32),
            ]

        BufferPointer = C.POINTER(Buffer)
        Callback = C.CFUNCTYPE(None, C.c_void_p, C.c_void_p, BufferPointer)
        signatures = {
            'AudioQueueNewOutput': [C.POINTER(Format), Callback, C.c_void_p,
                                    C.c_void_p, C.c_void_p, C.c_uint32, C.POINTER(C.c_void_p)],
            'AudioQueueAllocateBuffer': [C.c_void_p, C.c_uint32, C.POINTER(BufferPointer)],
            'AudioQueueEnqueueBuffer': [C.c_void_p, BufferPointer, C.c_uint32, C.c_void_p],
            'AudioQueueSetParameter': [C.c_void_p, C.c_uint32, C.c_float],
            'AudioQueueStart': [C.c_void_p, C.c_void_p],
            'AudioQueuePause': [C.c_void_p],
            'AudioQueueStop': [C.c_void_p, C.c_bool],
            'AudioQueueDispose': [C.c_void_p, C.c_bool],
        }
        for name, arguments in signatures.items():
            function = getattr(self._lib, name)
            function.argtypes = arguments
            function.restype = C.c_int32

        # Keep this ctypes callback alive for the entire lifetime of the queue.
        # No locks are taken: disposing a queue may wait for this callback.
        @Callback
        def refill(_context, queue, buffer):
            if self._closed:
                return
            try:
                status = self._lib.AudioQueueEnqueueBuffer(queue, buffer, 0, None)
                if status and not self._closed:
                    self.error = 'AudioQueueEnqueueBuffer returned {}'.format(status)
            except Exception as exc:
                self.error = str(exc)

        self._callback = refill
        flags = (1 << 2) | (1 << 3)  # kLinearPCMFormatFlagIsSignedInteger | IsPacked
        if _audio_sys.byteorder == 'big':
            flags |= 1 << 1
        format_ = Format(48000.0, int.from_bytes(b'lpcm', 'big'), flags,
                         2, 1, 2, 1, 16, 0)
        self._buffers = []
        try:
            self._check(self._lib.AudioQueueNewOutput(
                C.byref(format_), self._callback, None, None, None, 0, C.byref(self._queue)),
                'AudioQueueNewOutput')
            pcm = _audio_pcm(frequency)
            for _ in range(3):
                buffer = BufferPointer()
                self._check(self._lib.AudioQueueAllocateBuffer(
                    self._queue, len(pcm), C.byref(buffer)), 'AudioQueueAllocateBuffer')
                self._buffers.append(buffer)
                C.memmove(buffer.contents.mAudioData, pcm, len(pcm))
                buffer.contents.mAudioDataByteSize = len(pcm)
                self._check(self._lib.AudioQueueEnqueueBuffer(
                    self._queue, buffer, 0, None), 'AudioQueueEnqueueBuffer')
            self.set_volume(volume)
        except Exception:
            self.close()
            raise

    @staticmethod
    def _check(status, operation):
        if status:
            raise OSError('{} returned {}'.format(operation, status))

    def set_active(self, active):
        if self._closed or bool(active) == self._started:
            return
        if active:
            self._check(self._lib.AudioQueueStart(self._queue, None), 'AudioQueueStart')
        else:
            # AudioQueuePause stops output now and preserves queued RAM buffers.
            # It does not wait for the waveform or loop to finish.
            self._check(self._lib.AudioQueuePause(self._queue), 'AudioQueuePause')
        self._started = bool(active)

    def set_volume(self, volume):
        if not self._closed:
            self._check(self._lib.AudioQueueSetParameter(self._queue, 1, volume),
                        'AudioQueueSetParameter')  # kAudioQueueParam_Volume

    def close(self):
        if self._closed:
            return
        self._closed = True
        if self._queue.value:
            # Mute before teardown. The immediate flag prevents draining audio.
            self._lib.AudioQueueSetParameter(self._queue, 1, 0.0)
            self._lib.AudioQueueStop(self._queue, True)
            status = self._lib.AudioQueueDispose(self._queue, True)
            if not status:
                self._queue = _audio_ctypes.c_void_p()
                self._buffers.clear()
            else:
                # If a broken driver refuses disposal, keep the C callback alive
                # rather than risking a call into a garbage-collected function.
                _audio_retained_backends.append(self)
        self._started = False


_audio_retained_backends = []


class _PygameMemoryAudio:
    def __init__(self, frequency, volume):
        _audio_os.environ.setdefault('PYGAME_HIDE_SUPPORT_PROMPT', '1')
        import pygame.mixer as mixer
        self._mixer = mixer
        self._owns_mixer = not bool(mixer.get_init())
        self._closed = False
        self._channel = None
        self.error = None
        try:
            if self._owns_mixer:
                mixer.init(frequency=48000, size=-16, channels=1, buffer=512)
            sample_rate, sample_format, channels = mixer.get_init()
            if sample_format != -16 or channels not in (1, 2):
                raise RuntimeError('pygame mixer must use signed 16-bit mono or stereo audio')
            self._sound = mixer.Sound(buffer=_audio_pcm(frequency, sample_rate, channels))
            self.set_volume(volume)
        except Exception:
            self.close()
            raise

    def set_active(self, active):
        if self._closed:
            return
        if active:
            if self._channel is None or not self._channel.get_busy():
                self._channel = self._sound.play(loops=-1)
                if self._channel is None:
                    raise RuntimeError('pygame has no free audio channel')
        elif self._channel is not None:
            self._channel.stop()
            self._channel = None

    def set_volume(self, volume):
        if not self._closed:
            self._sound.set_volume(volume)

    def close(self):
        if self._closed:
            return
        if self._channel is not None:
            self._channel.stop()
            self._channel = None
        self._closed = True
        if self._owns_mixer:
            self._mixer.quit()


class AudioEngine:
    """Non-blocking tone with RAM-only PCM, immediate pause and mute.

    Use set_active(running and sound_timer > 0) on each UI tick. Pass False on
    pause/reset/ROM change. set_volume(0) really silences and pauses playback.
    Call close() on application shutdown. It is safe to call it more than once.
    available and description explicitly report a missing/failed output device.
    """

    def __init__(self, frequency=440, volume=0.25):
        frequency = float(frequency)
        if not _audio_math.isfinite(frequency) or not 40 <= frequency <= 8000:
            raise ValueError('Audio frequency must be between 40 and 8000 Hz')
        self.frequency = frequency
        self.volume = _audio_level(volume)
        self.available = False
        self.description = 'Audio unavailable'
        self._backend = None
        self._active = False
        self._closed = False
        failures = []
        choices = []
        if _audio_sys.platform == 'darwin':
            choices.append((_MacMemoryAudio, 'Core Audio · RAM PCM'))
        choices.append((_PygameMemoryAudio, 'pygame · RAM PCM'))
        for backend_type, label in choices:
            try:
                self._backend = backend_type(frequency, self.volume)
                self.available = True
                self.description = label
                break
            except Exception as exc:
                failures.append('{}: {}'.format(backend_type.__name__, exc))
        self.error = '; '.join(failures) if failures else None
        if not self.available:
            self.description = 'Audio unavailable. macOS uses Core Audio; other systems need pygame installed.'
        _audio_atexit.register(self.close)

    def _failed(self, exc):
        self.error = str(exc)
        self.description = 'Audio unavailable · output device error'
        self.available = False
        backend, self._backend = self._backend, None
        if backend is not None:
            try:
                backend.close()
            except Exception:
                pass

    def set_active(self, active):
        self._active = bool(active)
        if self._closed or self._backend is None:
            return
        try:
            if self._backend.error:
                raise RuntimeError(self._backend.error)
            self._backend.set_active(self._active and self.volume > 0)
        except Exception as exc:
            self._failed(exc)

    def set_volume(self, volume):
        self.volume = _audio_level(volume)
        if self._closed or self._backend is None:
            return
        try:
            self._backend.set_volume(self.volume)
            self.set_active(self._active)
        except Exception as exc:
            self._failed(exc)

    def close(self):
        if self._closed:
            return
        self._closed = True
        _audio_atexit.unregister(self.close)
        self._active = False
        backend, self._backend = self._backend, None
        if backend is not None:
            try:
                backend.close()
            except Exception as exc:
                self.error = str(exc)
        self.available = False



# Original embedded animation ROM; assembled in RAM only.
DEMO_ROM = bytes.fromhex(
    "00ff600861066200f230d01a601661066201f230d01a602461066202f230d01a603261066203f230d01a6040"
    "61066204f230d01a604e61066205f230d01a605c61066206f230d01a606a61066207f230d01a600861146208"
    "f230d01a601661146209f230d01a60246114620af230d01a60326114620bf230d01a60406114620cf230d01a"
    "604e6114620df230d01a605c6114620ef230d01a606a6114620ff230d01a60386128a4b6d0106003f0186028"
    "f015f007300012b200c16006f015f007300012be00c16006f015f007300012ca00c16006f015f007300012d6"
    "00c16006f015f007300012e200c16006f015f007300012ee00fb6004f015f007300012fa00fb6004f015f007"
    "3000130600fb6004f015f0073000131200fb6004f015f0073000131e00fb6004f015f0073000132a00fb6004"
    "f015f0073000133600fb6004f015f0073000134200fb6004f015f0073000134e00fc6004f015f0073000135a"
    "00fc6004f015f0073000136600fc6004f015f0073000137200fc6004f015f0073000137e00fc6004f015f007"
    "3000138a00fc6004f015f0073000139600fc6004f015f007300013a200fc6004f015f007300013ae6028f015"
    "f007300013b800fe600361056200f229d015600a61056201f229d015601161056202f229d015601861056203"
    "f229d015601f61056204f229d015602661056205f229d015602d61056206f229d015603461056207f229d015"
    "6003610d6208f229d015600a610d6209f229d0156011610d620af229d0156018610d620bf229d015601f610d"
    "620cf229d0156026610d620df229d015602d610d620ef229d0156034610d620ff229d0156003f0186037f015"
    "f0073000146800c16006f015f0073000147400c16006f015f0073000148000c16006f015f0073000148c00c1"
    "6006f015f0073000149800c16006f015f007300014a4600ff015f007300014ae12003ffc40028001800187e1"
    "8421842187e1800183c18421800140023ffc06600c30"
)


class EmulatorApp:
    """A compact Tk UI with independent instruction and 60 Hz timer clocks."""
    BG = "#06142b"
    PANEL = "#0b2449"
    FG = "#67bbff"
    DIM = "#4086c2"
    BLACK = "#02050a"
    SCREEN = "#000c1c"
    PIXEL = "#3bacff"

    def __init__(self, root, rom_path=None):
        import tkinter as tk
        from tkinter import filedialog, messagebox
        self.tk, self.filedialog, self.messagebox = tk, filedialog, messagebox
        self.root = root
        root.title(TITLE)
        root.geometry("600x400")
        root.minsize(600, 400)
        root.maxsize(600, 400)
        root.resizable(False, False)
        root.configure(bg=self.BG)
        root.protocol("WM_DELETE_WINDOW", self.close)
        self.core = Chip8(Compatibility.schip())
        self.audio = AudioEngine()
        self.running = False
        self.closed = False
        self.loaded_name = "No ROM loaded"
        self.error = None
        self.speed = 700
        self.volume = 0.25
        self.muted = False
        self.profile = "SUPER-CHIP"
        self.last_time = time.perf_counter()
        self.cpu_credit = 0.0
        self.timer_credit = 0.0
        self.pulse_id = None
        self.settings_window = None
        self.help_window = None
        self.release_jobs = {}
        self.space_down = False
        self.status = tk.StringVar(value="READY  |  700 Hz  |  FILES OFF")
        self.name_var = tk.StringVar(value=self.loaded_name)
        self.sound_var = tk.StringVar(value="SOUND OFF")
        self._menus()
        self._widgets()
        self._bindings()
        self._set_running(False)
        self.root.after(0, self._pulse)
        if rom_path:
            self.root.after(40, lambda: self.load_path(rom_path))

    def _menu(self, parent):
        return self.tk.Menu(parent, tearoff=False, bg=self.BLACK, fg=self.FG,
                            activebackground=self.PANEL, activeforeground=self.FG,
                            selectcolor=self.FG, bd=0)

    def _menus(self):
        bar = self._menu(self.root)
        file = self._menu(bar)
        file.add_command(label="Load ROM…", command=self.choose_rom, accelerator="Ctrl/Cmd+O")
        file.add_command(label="Reset", command=self.reset, accelerator="Ctrl/Cmd+R")
        file.add_separator()
        file.add_command(label="Exit", command=self.close)
        bar.add_cascade(label="File", menu=file)
        game = self._menu(bar)
        game.add_command(label="Play / Pause", command=self.toggle_play, accelerator="Space")
        game.add_command(label="Reset game", command=self.reset)
        game.add_command(label="Built-in demo", command=self.load_demo)
        bar.add_cascade(label="Game", menu=game)
        settings = self._menu(bar)
        settings.add_command(label="Settings…", command=self.show_settings)
        bar.add_cascade(label="Settings", menu=settings)
        help_menu = self._menu(bar)
        help_menu.add_command(label="Controls & help", command=self.show_help, accelerator="F1")
        help_menu.add_command(label="About", command=self.show_about)
        bar.add_cascade(label="Help", menu=help_menu)
        self.root.configure(menu=bar)

    def _button(self, parent, text, command, **kwargs):
        return self.tk.Button(parent, text=text, command=command, bg=self.BLACK,
                              fg=self.FG, activebackground="#102c50", activeforeground="#98d5ff",
                              disabledforeground="#355573", relief="flat", bd=0,
                              highlightbackground="#234670", highlightcolor=self.FG,
                              highlightthickness=1, padx=10, pady=4, cursor="hand2", **kwargs)

    def _widgets(self):
        tk = self.tk
        top = tk.Frame(self.root, bg=self.BG)
        top.pack(fill="x", padx=10, pady=(7, 4))
        tk.Label(top, text="SUPERCHIP", fg=self.FG, bg=self.BG,
                 font=("TkDefaultFont", 11, "bold")).pack(side="left")
        tk.Label(top, text="0.1.0", fg=self.DIM, bg=self.BG).pack(side="left", padx=6)
        tk.Label(top, textvariable=self.name_var, fg=self.FG, bg=self.BG,
                 anchor="e").pack(side="right", fill="x", expand=True)
        tools = tk.Frame(self.root, bg=self.BG)
        tools.pack(fill="x", padx=10, pady=(0, 6))
        self._button(tools, "Load ROM", self.choose_rom).pack(side="left", padx=(0, 5))
        self.play_button = self._button(tools, "Play game", self.toggle_play)
        self.play_button.pack(side="left", padx=(0, 5))
        self.reset_button = self._button(tools, "Reset", self.reset)
        self.reset_button.pack(side="left", padx=(0, 5))
        self._button(tools, "Settings", self.show_settings).pack(side="left", padx=(0, 5))
        self._button(tools, "Help", self.show_help).pack(side="left")
        self._button(tools, "Demo", self.load_demo).pack(side="right")
        self.canvas = tk.Canvas(self.root, bg=self.SCREEN, bd=0,
                                highlightthickness=1, highlightbackground="#245086")
        self.canvas.pack(fill="both", expand=True, padx=10)
        self.pixels = [self.canvas.create_rectangle(0, 0, 0, 0, fill=self.PIXEL,
                                                     outline="", state="hidden") for _ in range(8192)]
        self.rendered = [-1] * 8192
        self.render_size = (64, 32)
        self.welcome_title = self.canvas.create_text(0, 0, text="SUPERCHIP",
                                                     fill=self.FG, font=("TkDefaultFont", 27, "bold"))
        self.welcome_sub = self.canvas.create_text(0, 0, text="Load CHIP-8 / SUPER-CHIP, or try Demo",
                                                   fill=self.DIM, font=("TkDefaultFont", 11))
        self.canvas.bind("<Configure>", self._resize)
        self.canvas.bind("<Button-1>", lambda _event: self.canvas.focus_set())
        bottom = tk.Frame(self.root, bg=self.BG)
        bottom.pack(fill="x", padx=10, pady=(5, 2))
        tk.Label(bottom, textvariable=self.status, fg=self.FG, bg=self.BG,
                 anchor="w", font=("TkDefaultFont", 9)).pack(side="left")
        tk.Label(bottom, textvariable=self.sound_var, fg=self.DIM, bg=self.BG,
                 font=("TkDefaultFont", 9)).pack(side="right")
        tk.Label(self.root, text="KEYPAD   1234 / QWER / ASDF / ZXCV     •     SPACE  pause",
                 fg=self.DIM, bg=self.BG, font=("TkDefaultFont", 9)).pack(pady=(0, 5))

    def _bindings(self):
        self.root.bind("<KeyPress>", self._key_press)
        self.root.bind("<KeyRelease>", self._key_release)
        self.root.bind("<FocusOut>", self._focus_out)
        for modifier in ("Control", "Command") if sys.platform == "darwin" else ("Control",):
            self.root.bind(f"<{modifier}-o>", lambda _e: self._shortcut(self.choose_rom))
            self.root.bind(f"<{modifier}-r>", lambda _e: self._shortcut(self.reset))
        self.root.bind("<F1>", lambda _e: self._shortcut(self.show_help))
        self.root.bind("<Escape>", lambda _e: self._shortcut(lambda: self._set_running(False)))

    @staticmethod
    def _shortcut(action):
        action()
        return "break"

    def _key_press(self, event):
        key = event.keysym.lower()
        if key in self.release_jobs:
            self.root.after_cancel(self.release_jobs.pop(key))
            return "break"  # X11 repeat synthesizes a release/press pair.
        if key == "space":
            if self.space_down:
                return "break"
            self.space_down = True
            self.toggle_play()
            return "break"
        if key in KEY_MAP and self.running and not (event.state & 0x0C):
            self.core.key_down(KEY_MAP[key])
            return "break"

    def _key_release(self, event):
        key = event.keysym.lower()
        if key in KEY_MAP or key == "space":
            def release():
                self.release_jobs.pop(key, None)
                if key == "space":
                    self.space_down = False
                else:
                    self.core.key_up(KEY_MAP[key])
            if key in self.release_jobs:
                self.root.after_cancel(self.release_jobs[key])
            self.release_jobs[key] = self.root.after_idle(release)
            return "break"

    def _clear_keys(self):
        for job in self.release_jobs.values():
            self.root.after_cancel(job)
        self.release_jobs.clear()
        self.core.release_keys()

    def _focus_out(self, _event):
        # The deferred check distinguishes focus moving inside our window.
        def check():
            if not self.closed:
                try:
                    focused = self.root.focus_get()
                except (KeyError, self.tk.TclError):
                    # Tk can report an internal native-menu clone that has no
                    # Python widget object. Treat it as temporary focus loss.
                    focused = None
                if focused is None or focused.winfo_toplevel() != self.root:
                    self.space_down = False
                    self._clear_keys()
                    self._set_running(False)
        self.root.after_idle(check)

    def _resize(self, event):
        width, height = self.core.width, self.core.height
        scale = max(1, min((event.width - 4) // width, (event.height - 4) // height))
        ox, oy = (event.width - width * scale) // 2, (event.height - height * scale) // 2
        for index, pixel in enumerate(self.pixels):
            if index < width * height:
                x, y = ox + index % width * scale, oy + index // width * scale
                self.canvas.coords(pixel, x, y, x + scale, y + scale)
            else:
                self.canvas.itemconfigure(pixel, state="hidden")
        self.canvas.coords(self.welcome_title, event.width // 2, event.height // 2 - 14)
        self.canvas.coords(self.welcome_sub, event.width // 2, event.height // 2 + 25)

    def _render(self):
        if not self.core.dirty:
            return
        if self.render_size != (self.core.width, self.core.height):
            from types import SimpleNamespace
            self.render_size = (self.core.width, self.core.height)
            self.rendered[:] = [-1] * 8192
            self._resize(SimpleNamespace(width=self.canvas.winfo_width(), height=self.canvas.winfo_height()))
        for index, value in enumerate(self.core.display):
            if value != self.rendered[index]:
                self.canvas.itemconfigure(self.pixels[index], state="normal" if value else "hidden")
                self.rendered[index] = value
        self.core.dirty = False

    def _set_running(self, running):
        self.running = bool(running and self.core.rom and not self.error and not self.core.halted)
        self.last_time = time.perf_counter()
        self.cpu_credit = 0.0
        self.timer_credit = 0.0
        self.audio.set_active(self.running and self.core.sound_timer > 0 and not self.muted)
        self.play_button.configure(text="Pause" if self.running else "Play game")
        self.reset_button.configure(state="normal" if self.core.rom else "disabled")
        if not self.running:
            self._clear_keys()
        self._update_status()

    def _update_status(self):
        state = "ERROR" if self.error else "FINISHED" if self.core.halted else "PLAYING" if self.running else "PAUSED" if self.core.rom else "READY"
        self.status.set(f"{state}  |  {self.core.width}x{self.core.height}  |  {self.speed} Hz  |  FILES OFF")
        sounding = self.running and self.core.sound_timer > 0
        self.sound_var.set("MUTED" if self.muted or self.volume == 0 else ("BUZZ" if sounding else "SOUND ON") if self.audio.available else "AUDIO UNAVAILABLE")

    def toggle_play(self):
        if self.settings_window is not None or self.help_window is not None:
            return
        if not self.core.rom:
            self.choose_rom()
        elif self.error or self.core.halted:
            self.reset()
        else:
            self._set_running(not self.running)
            self.canvas.focus_set()

    def choose_rom(self):
        was_running = self.running
        self._set_running(False)
        filename = self.filedialog.askopenfilename(parent=self.root, title="Load CHIP-8 / SUPER-CHIP ROM",
                     filetypes=(("CHIP-8 / SUPER-CHIP", "*.ch8 *.c8 *.sc8 *.sch8 *.rom"), ("All files", "*")))
        if filename:
            self.load_path(filename)
        else:
            self._set_running(was_running)

    def load_demo(self):
        if self.settings_window is not None or self.help_window is not None:
            return
        self._set_running(False)
        self.core.load_rom(DEMO_ROM)
        self.loaded_name = "Built-in SUPER-CHIP demo"
        self.name_var.set(self.loaded_name)
        self.error = None
        self.canvas.itemconfigure(self.welcome_title, state="hidden")
        self.canvas.itemconfigure(self.welcome_sub, state="hidden")
        self._render()
        self._set_running(True)
        self.canvas.focus_set()

    def load_path(self, filename):
        self._set_running(False)
        try:
            # Bounded, read-only load. Never trust the size of an arbitrary file.
            with open(filename, "rb") as stream:
                data = stream.read(3585)
            self.core.load_rom(data)
        except (OSError, ValueError, EmulationError) as exc:
            self.messagebox.showerror("ROM could not be loaded", str(exc), parent=self.root)
            return False
        self.loaded_name = Path(filename).name
        shown = self.loaded_name if len(self.loaded_name) <= 34 else self.loaded_name[:31] + "…"
        self.name_var.set(shown)
        self.error = None
        self.canvas.itemconfigure(self.welcome_title, state="hidden")
        self.canvas.itemconfigure(self.welcome_sub, state="hidden")
        self._render()
        self._set_running(False)
        self.canvas.focus_set()
        return True

    def reset(self):
        if not self.core.rom:
            return
        self._set_running(False)
        self.core.reset()
        self.error = None
        self._render()
        self._update_status()
        self.canvas.focus_set()

    def _pulse(self):
        if self.closed:
            return
        now = time.perf_counter()
        dt = min(now - self.last_time, 0.1)  # Don't catch up minutes after system sleep.
        self.last_time = now
        if self.running:
            # CPU and timers share wall time but keep separate frequencies.
            # Split into short slices so slow callbacks do not burst all draws
            # before advancing timers. Fx0A never prevents timer countdown.
            remaining = max(0.0, dt)
            try:
                while remaining > 1e-9:
                    part = min(remaining, 1.0 / 600.0)
                    remaining -= part
                    self.timer_credit += part * 60
                    ticks = int(self.timer_credit + 1e-9)
                    if ticks:
                        self.timer_credit -= ticks
                        self.core.tick_timers(ticks)
                    self.cpu_credit += part * self.speed
                    cycles = int(self.cpu_credit)
                    self.cpu_credit -= cycles
                    for _ in range(cycles):
                        if not self.core.step():
                            break  # Awaiting input/vblank consumes idle CPU cycles.
            except EmulationError as exc:
                self.error = str(exc)
                self._set_running(False)
                self._render()
                self.messagebox.showerror("Emulation stopped", str(exc) + "\n\nReset or load a different ROM.", parent=self.root)
            if self.core.halted:
                self._set_running(False)
            self._render()
        self.audio.set_active(self.running and self.core.sound_timer > 0 and not self.muted)
        self._update_status()
        self.pulse_id = self.root.after(4, self._pulse)

    def _dialog(self, title, size):
        win = self.tk.Toplevel(self.root)
        win.title(title)
        win.configure(bg=self.BG)
        win.geometry(size)
        win.resizable(False, False)
        win.transient(self.root)
        return win

    def show_settings(self):
        if self.settings_window is not None:
            self.settings_window.lift()
            return
        self._set_running(False)
        tk = self.tk
        win = self.settings_window = self._dialog("Settings · catsuperchipemu", "490x550")
        def dismiss():
            self.settings_window = None
            win.destroy()
            self.canvas.focus_set()
        win.protocol("WM_DELETE_WINDOW", dismiss)
        win.bind("<Escape>", lambda _e: dismiss())
        body = tk.Frame(win, bg=self.BG)
        body.pack(fill="both", expand=True, padx=18, pady=14)
        tk.Label(body, text="EMULATION & AUDIO", fg=self.FG, bg=self.BG,
                 font=("TkDefaultFont", 13, "bold")).pack(anchor="w")
        tk.Label(body, text="Changes are kept in memory for this session only.",
                 fg=self.DIM, bg=self.BG).pack(anchor="w", pady=(4, 10))
        tk.Label(body, text="CPU speed (instructions per second)", fg=self.FG, bg=self.BG).pack(anchor="w")
        speed = tk.IntVar(value=self.speed)
        scale_options = dict(orient="horizontal", bg=self.BG, fg=self.FG, troughcolor=self.BLACK,
                             activebackground=self.PANEL, highlightthickness=0, length=390)
        tk.Scale(body, from_=100, to=2000, resolution=50, variable=speed, **scale_options).pack(fill="x")
        tk.Label(body, text="Buzzer volume", fg=self.FG, bg=self.BG).pack(anchor="w", pady=(5, 0))
        volume = tk.IntVar(value=round(self.volume * 100))
        tk.Scale(body, from_=0, to=100, resolution=1, variable=volume, **scale_options).pack(fill="x")
        muted = tk.BooleanVar(value=self.muted)
        options = dict(bg=self.BG, fg=self.FG, activebackground=self.BG,
                       activeforeground=self.FG, selectcolor=self.BLACK, highlightthickness=0)
        tk.Checkbutton(body, text="Mute sound", variable=muted, **options).pack(anchor="w")
        tk.Label(body, text=self.audio.description, fg=self.DIM, bg=self.BG,
                 justify="left", wraplength=414).pack(anchor="w", pady=(2, 10))
        tk.Label(body, text="Compatibility profile", fg=self.FG, bg=self.BG).pack(anchor="w")
        profile = tk.StringVar(value=self.profile)
        modes = tk.Frame(body, bg=self.BG)
        modes.pack(anchor="w")
        for name in ("SUPER-CHIP", "CHIP-8 Modern", "Classic VIP"):
            tk.Radiobutton(modes, text=name, value=name, variable=profile, **options).pack(side="left")
        wrap = tk.BooleanVar(value=self.core.compatibility.draw_wrap)
        tk.Checkbutton(body, text="Wrap sprites at screen edges (instead of clipping)", variable=wrap, **options).pack(anchor="w")
        tk.Label(body, text="SUPER-CHIP: Vx shifts and jumps; preserve I/VF.\nCHIP-8 Modern: same, but uses V0 jumps.\nClassic VIP: Vy shifts, advance I, clear logic VF, 60 Hz draw.\nAll profiles wait for key release. Changes take effect immediately.",
                 fg=self.DIM, bg=self.BG, justify="left", wraplength=414).pack(anchor="w", pady=(4, 8))
        row = tk.Frame(body, bg=self.BG)
        row.pack(side="bottom", fill="x")
        def apply():
            self.speed = speed.get()
            self.volume = volume.get() / 100
            self.muted = muted.get()
            self.profile = profile.get()
            compatibility = (Compatibility.classic() if self.profile == "Classic VIP" else
                             Compatibility.schip() if self.profile == "SUPER-CHIP" else Compatibility())
            compatibility.draw_wrap = wrap.get()
            self.core.compatibility = compatibility
            self.core.draw_ready = True
            self.audio.set_volume(self.volume)
            self._update_status()
            dismiss()
        self._button(row, "Apply", apply).pack(side="right", padx=(5, 0))
        self._button(row, "Cancel", dismiss).pack(side="right")
        win.grab_set()
        win.focus_set()

    def show_help(self):
        if self.help_window is not None:
            self.help_window.lift()
            return
        self._set_running(False)
        win = self.help_window = self._dialog("Help · catsuperchipemu", "570x555")
        def dismiss():
            self.help_window = None
            win.destroy()
            self.canvas.focus_set()
        win.protocol("WM_DELETE_WINDOW", dismiss)
        win.bind("<Escape>", lambda _e: dismiss())
        text = (
            "LOAD → PLAY → ENJOY\n\n"
            "Load ROM opens a local .ch8 file. Play game starts it; Space pauses.\n"
            "Reset restarts the loaded ROM and leaves it paused.\n"
            "Ctrl/Cmd+O: load    Ctrl/Cmd+R: reset    F1: help    Esc: pause\n\n"
            "YOUR KEYBOARD        CHIP-8 KEYPAD\n"
            "  1 2 3 4               1 2 3 C\n"
            "  Q W E R               4 5 6 D\n"
            "  A S D F               7 8 9 E\n"
            "  Z X C V               A 0 B F\n\n"
            "Click the screen if game keys are not responding. Losing window\n"
            "focus pauses the game and releases all held keys. Some games\n"
            "wait until you release a key before continuing.\n\n"
            "Settings controls speed, volume/mute, sprite wrapping and\n"
            "CHIP-8 / SUPER-CHIP / Classic VIP profiles. Timers: 60 Hz.\n"
            "Sound is a synthesized buzzer. Audio availability is shown there.\n\n"
            "CHIP-8 64x32 + modern SUPER-CHIP 128x64; 4 KB RAM.\n"
            "16x16 sprites, scrolling, large font and 8 RAM-only RPL flags.\n"
            "Mode selection clears the screen. Scrolls use logical pixels.\n"
            "Historical HP48 half-pixel quirks and XO-CHIP are unsupported.\n"
            "RPL flags survive Reset, but clear when another ROM loads.\n"
            "FILES OFF: read-only ROMs; no saves/config/logs/audio files."
        )
        panel = self.tk.Frame(win, bg=self.BG)
        panel.pack(padx=14, pady=12, fill="both", expand=True)
        scrollbar = self.tk.Scrollbar(panel)
        scrollbar.pack(side="right", fill="y")
        area = self.tk.Text(panel, wrap="word", bg=self.BG, fg=self.FG,
                            relief="flat", font=("TkFixedFont", 10),
                            yscrollcommand=scrollbar.set, highlightthickness=0)
        area.pack(side="left", fill="both", expand=True)
        scrollbar.configure(command=area.yview)
        area.insert("1.0", text)
        area.configure(state="disabled")
        self._button(win, "Close", dismiss).pack(side="bottom", pady=(0, 12))
        win.grab_set()
        win.focus_set()

    def show_about(self):
        self._set_running(False)
        self.messagebox.showinfo("About catsuperchipemu", TITLE + "\n\nA blue/black CHIP-8 and modern SUPER-CHIP emulator.\nSynthesized audio • Files off • Original built-in demo\n\nIndependent project, inspired by compact emulator GUIs.\nNot affiliated with mGBA.", parent=self.root)

    def close(self):
        if self.closed:
            return
        self.closed = True
        self.running = False
        if self.pulse_id is not None:
            self.root.after_cancel(self.pulse_id)
        self._clear_keys()
        self.audio.close()
        self.root.destroy()


def main(argv=None):
    parser = argparse.ArgumentParser(description=TITLE, epilog="No files are written. Optional ROM is opened read-only.")
    parser.add_argument("rom", nargs="?", help="optional CHIP-8 / SUPER-CHIP ROM path")
    args = parser.parse_args(argv)
    try:
        import tkinter as tk
    except ImportError:
        print("This program needs Python with Tk support. Install a Python distribution that includes Tk.", file=sys.stderr)
        return 1
    try:
        root = tk.Tk()
    except tk.TclError as exc:
        print(f"Cannot open the GUI: {exc}\nRun from a graphical desktop with Python/Tk installed.", file=sys.stderr)
        return 1
    EmulatorApp(root, args.rom)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
