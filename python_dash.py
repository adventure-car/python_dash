#!/usr/bin/env python3
"""
PYTHON DASH - a Geometry Dash style auto-runner with a level editor, in pygame
===============================================================================
Home screen:  PLAY   BUILD LEVELS (editor)   SKINS   SONGS (opens the songs folder)
              SETTINGS   QUIT      - and SIGN IN / SIGN UP in the top-left corner

Accounts
--------
  Accounts only work when python_dash.py is run from a shared online folder (a folder
  that Google Drive, Dropbox, OneDrive or iCloud syncs and that everyone who plays
  shares).  The game uses the folder it is in - there's nothing to set up.  Accounts
  (passwords only as salted hashes) and their progress live there, so names are unique
  for everyone and progress follows you to any computer.  Run from anywhere else, you
  can still play as Guest.  Bonus: put a new version in the folder and everyone has it.

Main levels (AugmentedMagic account only)
-----------------------------------------
  Signed in as AugmentedMagic, a MAIN LEVELS button appears on the home screen.  It lists
  every main level - all the built-in ones (Neon Gauntlet, ...) plus any added through
  the main levels folder.  Rename them, change their difficulty, or hide built-ins.  To
  add a level, drop its .json into the folder (or onto that screen) and set it up.  The
  changes live in the shared online folder, so every player sees them.

Level select has four tabs (LEFT/RIGHT or click):
  Levels        the built-in levels
  Your Levels   levels you built in the editor        (~/.python_dash/levels/)
  Other Levels  level .json files from someone else   (~/.python_dash/other_levels/)
                - drag a .json onto the window to import it, or press O to open the folder
                - shown as "[Level Name] by [Author]" (the author's account name)
  All Levels    everything above

Requirements:  pip install pygame-ce     (plain pygame works too if it installs)
Run:           python python_dash.py

Playing
-------
  SPACE / UP / W / left mouse   the one-button action (jump, thrust, flip...)
  P  practice mode (respawn at last portal) / normal      H  hitboxes
  R  restart      TAB  settings      ESC  back
  1-9  warp to a section  (only if "Level warping" is enabled in Settings)
  Every game mode has a floor AND a ceiling.
  Coins: grab them and FINISH the level in normal mode to keep them.

Fullscreen:  click the button in the top-right corner of any menu or the editor, or use
F11, Alt/Option+Enter or Ctrl/Cmd+F from any screen (also in Settings).  The game is drawn
at 960x540 and scaled to fit, so you can also resize the window freely.

Settings (home screen, or TAB while playing)
--------------------------------------------
  Account             shows who's signed in (ENTER signs in / out)
  Default game mode   NORMAL or PRACTICE when a level starts
  Wave controls       CLICK = each click switches direction, HOLD = hold to go up
  Music               play the songs attached to levels
  Noclip, level warping, hitboxes, FPS counter and fullscreen.
  An attempt that uses noclip or warping is "assisted": it never counts toward
  your best %, coins or completion.  Practice mode and editor playtests never count.

Game modes
----------
  Cube    hold/tap to jump (auto-rejumps while held, like GD)
  Ship    hold to rise, release to fall
  Ball    tap to flip gravity (only while touching a surface)
  UFO     tap for a small mid-air hop
  Wave    tap to switch direction (or hold to rise - see Settings).  Dies on ramps too.
  Robot   tap to jump, HOLD to jump higher (variable height)
  Spider  tap to teleport to the opposite surface
  Swing   tap to flip gravity at any time (swing copter)
Extras (all trigger just by touching them - no button needed, in EVERY mode):
  yellow pad / yellow orb   bounce you up        blue pad / blue orb  slam you down
  gravity portals  flip gravity      speed portals  0.8x 1x 1.25x 1.5x 1.8x
  slopes           45-degree (1x1), gentle 1:2 (2 wide) and steep 2:1 (2 tall), facing any
                   way - run up / down them (deadly to the wave)
  spikes           pointing up, down, left or right
  mini wave portal the wave, but smaller and twice as steep

Level editor
------------
  The palette has tabs:  OBJECTS  SLOPES  PADS & ORBS  PORTALS  SPEED  TRIGGERS
  (TAB / Shift+TAB)
  Left click / drag   place            Right click / drag  erase
  1-8  tool in the tab's first row     Shift+1-8  second row
  V  select tool: drag an area, then
       Ctrl/Cmd+C copy   Ctrl/Cmd+X cut   Ctrl/Cmd+V paste (click where it goes)
       Ctrl/Cmd+D duplicate   DELETE remove   G put it in the current group
  DELETE / BACKSPACE with nothing selected deletes the object under the mouse.
  E  eraser       B / "EDIT BG"  edit the background (decoration) layer
  [ ]  change the current group (new objects go in it)  - or click GROUP
  SONGS  pick the level's song from your songs folder (SPACE previews it).  The
         SONGS button on the home screen opens that folder - drop .mp3 / .ogg / .wav
         files in it.  You can also drag a song onto the editor window.
         M previews the level's song from the screen position.
  Triggers fire when the player passes their column; click one to edit it:
    MOVE     moves a group (blocks, time, easing)
    REVEAL   makes a group appear (it starts hidden) - or hide it
    LIGHT    flicker on, flicker off, close circle, open circle
  TEXT  click a cell and type - text boxes can be in groups too.
  Mouse wheel, A/D or arrow keys scroll       Ctrl/Cmd+Z undo, Ctrl/Cmd+Y redo
  Ctrl/Cmd+S save    P playtest from the start    Shift+P / "PLAY HERE" from the screen
  The first 6 columns are a safe start zone.  Mode portals split the level into
  sections; the "START" button picks the first section's mode.
Levels are saved as JSON in ~/.python_dash/levels/ and show up in PLAY.  EXPORT puts a
copy on your Desktop that carries your account name and the level's song.

Adding built-in levels
----------------------
Write a builder function (see build_warm_up) and add a LevelDef to LEVELS.
Run  python verify_levels.py  to have a solver check every level is beatable
(it also accepts a path to a custom level .json file).
"""
import base64
import bisect
import copy
import hashlib
import hmac
import json
import math
import os
import random
import subprocess
import sys
import threading
import urllib.parse
import urllib.request
from collections import defaultdict, deque

import pygame

# --------------------------------------------------------------------------
# Constants
# --------------------------------------------------------------------------
W, H = 960, 540
FPS = 60
B = 40                      # block size in pixels
FLOOR = 440                 # y of the ground surface
CEIL = 40                   # y of the ceiling surface (corridor modes)
ROWS = (FLOOR - CEIL) // B  # 10 rows in a corridor
SPEED = 7.0                 # horizontal px per frame (all modes, 1x speed)
CAM_OFFSET = 260            # player's x position on screen
STEP_TOL = 7                # px of forgiveness when clipping block corners
BUFFER_FRAMES = 6           # input buffer for click-style modes
ORB_RADIUS = 36             # how close you must be to an orb to use it
DESC_MAX = 80                # longest level description
NAME_MAX = 28
SAFE_COLS = 6               # editor: columns at the start where nothing can be placed
MAX_COLS = 1500             # editor: maximum level length in blocks

# physics tuning ------------------------------------------------------------
CUBE_G, CUBE_JUMP, CUBE_MAXFALL = 1.1, 13.3, 20
ROBOT_G, ROBOT_V, ROBOT_HOLD, ROBOT_MAXFALL = 1.1, 8.0, 16, 18
BALL_G, BALL_MAXFALL = 1.4, 18
UFO_G, UFO_HOP, UFO_MAXFALL = 0.75, 9.5, 10
SHIP_UP, SHIP_DOWN, SHIP_MAX = 0.85, 0.55, 8
SPIDER_G, SPIDER_MAXFALL = 1.5, 18
SWING_A, SWING_MAX = 0.75, 8.5
PAD_V, ORB_V, DORB_V = 16.0, 12.5, 14.0
DPAD_V = 16.0                 # a down pad slams you toward the floor
SPEED_VALUES = (0.8, 1.0, 1.25, 1.5, 1.8)      # speed portal multipliers
SPEED_COLOR = {0.8: (255, 170, 60), 1.0: (80, 170, 255), 1.25: (90, 230, 120),
               1.5: (255, 90, 200), 1.8: (255, 80, 80)}

MODE_ORDER = ["cube", "ship", "ball", "ufo", "wave", "robot", "spider", "swing"]
# hitbox sizes (all even numbers so landing positions stay on whole pixels)
SIZE = {
    "cube": (36, 36), "ship": (40, 26), "ball": (36, 36), "ufo": (38, 28),
    "wave": (14, 14), "robot": (32, 40), "spider": (36, 32), "swing": (38, 28),
}
CEIL_MODES = set(MODE_ORDER)        # every mode has a ceiling now
FLIPPABLE = {"ship", "ufo", "robot", "spider", "swing"}   # sprite flips with gravity

BG = {
    "cube": (18, 36, 92), "ship": (70, 24, 90), "ball": (92, 34, 30),
    "ufo": (22, 70, 72), "wave": (20, 30, 110), "robot": (80, 62, 22),
    "spider": (62, 18, 52), "swing": (24, 82, 40), "miniwave": (26, 22, 96),
}
ACCENT = {
    "cube": (70, 200, 255), "ship": (230, 110, 255), "ball": (255, 130, 80),
    "ufo": (90, 255, 220), "wave": (110, 150, 255), "robot": (255, 210, 80),
    "spider": (255, 90, 190), "swing": (120, 255, 120), "miniwave": (170, 130, 255),
}
PORTAL_MODES = MODE_ORDER + ["miniwave"]     # "miniwave" = the wave, small and twice as steep
MINI_WAVE_SIZE = (10, 10)
DIFF_COLOR = {
    "TEST": (120, 200, 255), "EASY": (90, 230, 120), "NORMAL": (255, 220, 70),
    "HARD": (255, 140, 60), "INSANE": (255, 70, 90), "CUSTOM": (200, 160, 255),
    "OTHER": (120, 230, 200), "DEMON": (255, 40, 40),
}
PRIMARY = (90, 245, 120)
SECONDARY = (60, 200, 255)
INK = (10, 10, 20)

DATA_DIR = os.path.join(os.path.expanduser("~"), ".python_dash")
LEVEL_DIR = os.path.join(DATA_DIR, "levels")
SAVE_PATH = os.path.join(DATA_DIR, "save.json")              # guest progress + settings
ACCOUNTS_PATH = os.path.join(DATA_DIR, "accounts.json")   # names + password hashes
ACCOUNT_DIR = os.path.join(DATA_DIR, "accounts")          # one progress file per account
ACCOUNT_NAME_MIN, ACCOUNT_NAME_MAX, PASSWORD_MIN = 3, 16, 4
# --------------------------------------------------------------------------
# The shared online folder.  Accounts (and the main levels) only work when this game
# file is run from a folder that Google Drive, Dropbox, OneDrive or iCloud syncs: the
# game uses the folder it is sitting in, so nobody ever has to type a path.
# --------------------------------------------------------------------------
GAME_DIR = os.path.dirname(os.path.abspath(__file__))
ONLINE_MARKERS = ("google drive", "googledrive", "my drive", "shared drives", "dropbox",
                  "onedrive", "cloudstorage", "icloud", "mobile documents", "box sync", "pcloud")


def in_online_folder(path):
    p = path.replace("\\", "/").lower()
    return any(m in p for m in ONLINE_MARKERS)


SHARED_DIR = (os.environ.get("PYTHON_DASH_SHARED")          # (for testing)
              or (GAME_DIR if in_online_folder(GAME_DIR) else None))
MAIN_DIR = (os.path.join(SHARED_DIR, "PythonDashMainLevels") if SHARED_DIR
            else os.path.join(DATA_DIR, "main_levels"))     # levels promoted to main levels
MAIN_META = os.path.join(MAIN_DIR, "_main_levels.json")   # names, difficulties, hidden
ADMIN_ACCOUNTS = {"augmentedmagic"}                       # who can manage main levels
MAIN_DIFFICULTIES = ["TEST", "EASY", "NORMAL", "HARD", "INSANE", "DEMON"]
DIFF_ORDER = ["TEST", "EASY", "NORMAL", "HARD", "INSANE", "DEMON"]
OTHER_DIR = os.path.join(DATA_DIR, "downloaded_levels")  # levels made by someone else
OLD_OTHER_DIR = os.path.join(DATA_DIR, "other_levels")    # (its name before)
REPO = "adventure-car/python_dash"                         # online levels + music live here
REPO_BRANCH = "main"
OLD_SAVE_PATH = os.path.join(os.path.expanduser("~"), ".dash_test_course.json")
MUSIC_DIR = os.path.join(DATA_DIR, "music")          # songs attached to levels
MUSIC_EXTS = (".mp3", ".ogg", ".wav", ".flac", ".opus")

# object kinds -------------------------------------------------------------
# slopes: "ramp" = 1x1 (45 degrees), "gramp" = gentle 2 wide x 1 tall (slope 1/2),
# "sramp" = steep 1 wide x 2 tall (slope 2).  _tl/_tr = ceiling slopes, _bl/_br = floor.
RAMP_SIZES = {"ramp": (1, 1), "gramp": (2, 1), "sramp": (1, 2)}
RAMPS = tuple(p + "_" + d for p in RAMP_SIZES for d in ("tl", "tr", "bl", "br"))
FLOOR_RAMPS = {k for k in RAMPS if k.endswith(("_bl", "_br"))}   # solid BELOW the slope
SIDE_SPIKES = ("spike_l", "spike_r")                    # spikes pointing left / right
SOLID = {"block"} | set(RAMPS)
CELL_KINDS = ({"block", "spike", "pad", "dpad", "orb", "dorb", "coin"} | set(RAMPS)
              | set(SIDE_SPIKES))
BG_KINDS = {"block", "spike"} | set(RAMPS) | set(SIDE_SPIKES)  # background (decoration)
SPIKES = {"spike"} | set(SIDE_SPIKES)
LIGHT_EFFECTS = ("flicker_on", "flicker_off", "close_circle", "open_circle")
LIGHT_NAMES = {"flicker_on": "Flicker on", "flicker_off": "Flicker off",
               "close_circle": "Close circle", "open_circle": "Open circle"}
TEXT_MAX = 60
# colour slots for objects (main and background layer).  An object stores a slot
# number: 0 = automatic (the game mode's colour), 1-10 = the level's own palette,
# which can be edited in the editor (EDIT COLOUR) and is saved with the level.
DEFAULT_PALETTE = [(240, 240, 250), (255, 90, 90), (255, 160, 60), (255, 225, 80),
                   (100, 230, 120), (70, 220, 230), (80, 130, 255), (170, 100, 255),
                   (255, 120, 200), (60, 60, 80)]
COLOR_SLOTS = len(DEFAULT_PALETTE) + 1           # "auto" + 10 colours
BG_COLORS = [None] + DEFAULT_PALETTE             # (kept for older code paths)
COLORABLE = {"block", "spike"} | set(RAMPS) | set(SIDE_SPIKES)  # kinds that take a colour
THEMES = [("", "NORMAL"), ("underwater", "UNDERWATER"), ("ocean", "OCEAN"), ("city", "CITY"),
          ("crystal", "CRYSTAL"), ("backyard", "BACKYARD")]
GROUP_MAX = 999




# --------------------------------------------------------------------------
# Level objects
# --------------------------------------------------------------------------
class Obj:
    """A level object living in one grid cell.  For pads and orbs the `flip` flag
    means "invisible" (it still works, you just can't see it while playing).
    `group` (0 = none) lets move / reveal triggers act on it; ox/oy is how far a
    move trigger has pushed it (pixels) and `hidden` is set by reveal triggers."""
    __slots__ = ("kind", "col", "row", "flip", "up", "val", "rect", "base", "group",
                 "ox", "oy", "hidden", "color")

    def __init__(self, kind, col, row=0, flip=False, up=False, val=1.0, group=0, color=0):
        self.kind, self.col, self.row, self.flip, self.up = kind, col, row, flip, up
        self.val = val
        self.group = group
        self.color = color          # colour slot: 0 = auto, 1-10 = the level's palette
        self.ox = self.oy = 0.0
        self.hidden = False
        x = col * B
        y = FLOOR - (row + 1) * B
        if kind == "block":
            self.rect = pygame.Rect(x, y, B, B)
        elif kind in RAMPS:        # slopes can cover 2x1 or 1x2 cells (anchored bottom-left)
            w, h = ramp_size(kind)
            self.rect = pygame.Rect(x, y - (h - 1) * B, w * B, h * B)
        elif kind == "spike":      # forgiving, GD-style small hitbox
            self.rect = pygame.Rect(x + 13, y + (0 if flip else 14), 14, 26)
        elif kind == "spike_r":    # base on the left, point to the right
            self.rect = pygame.Rect(x, y + 13, 26, 14)
        elif kind == "spike_l":    # base on the right, point to the left
            self.rect = pygame.Rect(x + 14, y + 13, 26, 14)
        elif kind == "pad":        # sits on the bottom of its cell, bounces you up
            self.rect = pygame.Rect(x + 2, y + B - 10, B - 4, 10)
        elif kind == "dpad":       # sits on the top of its cell, slams you down
            self.rect = pygame.Rect(x + 2, y, B - 4, 10)
        elif kind in ("orb", "dorb"):
            self.rect = pygame.Rect(x + 6, y + 6, 28, 28)
        elif kind == "coin":
            self.rect = pygame.Rect(x + 6, y + 6, 28, 28)
        elif kind in ("grav", "speed"):       # full-height portals
            self.rect = pygame.Rect(x + 14, CEIL, 12, FLOOR - CEIL)
        else:
            raise ValueError(kind)
        self.base = self.rect

    def shift(self, ox, oy):
        self.ox, self.oy = ox, oy
        self.rect = self.base.move(int(round(ox)), int(round(oy)))


class TextObj:
    """A text box.  Never collides; can be moved / revealed through its group."""
    __slots__ = ("col", "row", "text", "group", "ox", "oy", "hidden")

    def __init__(self, col, row, text, group=0):
        self.col, self.row, self.text, self.group = col, row, text, group
        self.ox = self.oy = 0.0
        self.hidden = False

    def shift(self, ox, oy):
        self.ox, self.oy = ox, oy


def ramp_size(kind):
    """(width, height) in cells of a slope kind like "gramp_br"."""
    return RAMP_SIZES[kind.split("_")[0]]


def ramp_span(o, left, right):
    """Surface of a slope under/over the horizontal span [left, right]:
    returns (is_floor_ramp, y).  For floor slopes y is the HIGHEST point of the slope
    inside the span, for ceiling slopes the LOWEST.  Works for any width/height."""
    r = o.rect
    a = max(left, r.left)
    b = min(right, r.right)
    k = o.kind[-2:]
    s = r.h / r.w                        # rise per pixel
    if k == "br":                        # uphill  /
        return True, r.bottom - (b - r.left) * s
    if k == "bl":                        # downhill \
        return True, r.top + (a - r.left) * s
    if k == "tl":                        # ceiling, low on the left
        return False, r.bottom - (a - r.left) * s
    return False, r.top + (b - r.left) * s   # tr: ceiling, low on the right


def ramp_steepness(kind):
    w, h = ramp_size(kind)
    return h / w


def ramp_points(kind, x, y, w=B, h=None):
    """Polygon of a slope whose bounding box has its top-left corner at (x, y)."""
    h = w if h is None else h
    tl, tr, bl, br = (x, y), (x + w, y), (x, y + h), (x + w, y + h)
    return {"tl": [tl, tr, bl], "tr": [tl, tr, br],
            "bl": [tl, bl, br], "br": [tr, br, bl]}[kind[-2:]]


def spike_points(kind, x, y, flip=False):
    """Polygon of a spike in the cell whose top-left corner is (x, y)."""
    if kind == "spike_r":
        return [(x, y), (x + B, y + B / 2), (x, y + B)]
    if kind == "spike_l":
        return [(x + B, y), (x, y + B / 2), (x + B, y + B)]
    if flip:
        return [(x, y), (x + B / 2, y + B), (x + B, y)]
    return [(x, y + B), (x + B / 2, y), (x + B, y + B)]


def solid_hit(o, r):
    """(top_pen, bot_pen) if solid object o overlaps rect r, else None.
    top_pen = how far r must move up to clear it, bot_pen = how far down."""
    orc = o.rect
    if o.kind == "block":
        if not r.colliderect(orc):
            return None
        return r.bottom - orc.top, orc.bottom - r.top
    if r.right <= orc.left or r.left >= orc.right:
        return None
    floor, y = ramp_span(o, r.left, r.right)
    if floor:
        if r.bottom <= y or r.top >= orc.bottom:
            return None
        return r.bottom - y, orc.bottom - r.top
    if r.top >= y or r.bottom <= orc.top:
        return None
    return r.bottom - orc.top, y - r.top


def draw_dashed_rect(surface, rect, color, dash=5, gap=4, width=2):
    """Dashed outline - how the editor marks invisible objects."""
    x0, y0, x1, y1 = rect.left, rect.top, rect.right - 1, rect.bottom - 1
    for x in range(x0, x1, dash + gap):
        e = min(x + dash, x1)
        pygame.draw.line(surface, color, (x, y0), (e, y0), width)
        pygame.draw.line(surface, color, (x, y1), (e, y1), width)
    for y in range(y0, y1, dash + gap):
        e = min(y + dash, y1)
        pygame.draw.line(surface, color, (x0, y), (x0, e), width)
        pygame.draw.line(surface, color, (x1, y), (x1, e), width)


def _interp(pts, x):
    if x <= pts[0][0]:
        return pts[0][1]
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        if x <= x1:
            return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
    return pts[-1][1]


def clean_trigger(j):
    """Validate a trigger's settings (from a file or the editor).  None = invalid."""
    if not isinstance(j, dict):
        return None

    def num(k, d, lo, hi):
        try:
            v = float(j.get(k, d))
        except (TypeError, ValueError):
            v = d
        if v != v:            # NaN
            v = d
        return max(lo, min(hi, v))

    t = j.get("type")
    if t == "move":
        return {"type": "move", "group": int(num("group", 1, 1, GROUP_MAX)),
                "dx": round(num("dx", 0, -200, 200), 2), "dy": round(num("dy", 2, -20, 20), 2),
                "time": round(num("time", 0.5, 0, 10), 2), "ease": bool(j.get("ease", True))}
    if t == "reveal":
        return {"type": "reveal", "group": int(num("group", 1, 1, GROUP_MAX)),
                "show": bool(j.get("show", True))}
    if t == "light":
        e = j.get("effect")
        if e not in LIGHT_EFFECTS:
            return None
        return {"type": "light", "effect": e, "radius": round(num("radius", 3, 1, 12), 2),
                "time": round(num("time", 0.5, 0, 10), 2)}
    return None


def default_trigger(tool, group):
    """Fresh trigger settings for an editor tool like 'trig:move' or 'light:flicker_off'."""
    g = group or 1
    if tool == "trig:move":
        return clean_trigger({"type": "move", "group": g, "dx": 0, "dy": 2, "time": 0.5})
    if tool == "trig:reveal":
        return clean_trigger({"type": "reveal", "group": g, "show": True})
    return clean_trigger({"type": "light", "effect": tool.split(":")[1], "radius": 3,
                          "time": 0.5})


def ease(t):
    return t * t * (3 - 2 * t)


class LevelDef:
    def __init__(self, name, difficulty, blurb, builder):
        self.name, self.difficulty, self.blurb, self.builder = name, difficulty, blurb, builder
        self.description = blurb  # the real description (custom levels: what the author wrote)
        self.key = name          # key used in the save file
        self.path = None         # file path for custom levels
        self.title = name        # what the level list shows ("Name by Author" for imports)
        self.author = ""


class Light:
    """Lighting state for light triggers: darkness (flicker on / off) and a circle of
    light around the player (close circle / open circle)."""
    BIG = 760.0                  # a circle this big covers the whole screen

    def __init__(self):
        self.dark = 0.0          # 0 = lights on, 1 = lights off
        self.flick = 0           # frames of flickering left
        self.flick_to = 0.0
        self.radius = None       # None = no circle
        self.r_from = self.r_to = 0.0
        self.r_n = self.r_t = 0  # animation length / progress (frames)
        self.frame = 0

    def trigger(self, cfg, instant):
        e = cfg["effect"]
        n = int(round(cfg["time"] * FPS))
        if e in ("flicker_on", "flicker_off"):
            target = 1.0 if e == "flicker_off" else 0.0
            if instant or n <= 0:
                self.dark, self.flick = target, 0
            else:
                self.flick, self.flick_to = n, target
        else:
            start = self.radius if self.radius is not None else self.BIG
            target = cfg["radius"] * B if e == "close_circle" else self.BIG
            if instant or n <= 0:
                self.radius = target if e == "close_circle" else None
                self.r_n = 0
            else:
                self.radius = start
                self.r_from, self.r_to, self.r_n, self.r_t = start, target, n, 0

    def update(self):
        self.frame += 1
        if self.flick > 0:
            self.flick -= 1
            if self.flick == 0:
                self.dark = self.flick_to
        if self.r_n:
            self.r_t += 1
            u = ease(min(1.0, self.r_t / self.r_n))
            self.radius = self.r_from + (self.r_to - self.r_from) * u
            if self.r_t >= self.r_n:
                self.r_n = 0
                if self.r_to >= self.BIG:
                    self.radius = None

    def darkness(self):
        """Current darkness 0..1 (flickers randomly while a flicker trigger runs)."""
        if self.flick > 0:
            h = (self.frame // 3) * 2654435761 % 7
            return self.flick_to if h < 3 else 1.0 - self.flick_to
        return self.dark

    def active(self):
        return self.darkness() > 0.01 or self.radius is not None


class Level:
    def __init__(self, defn):
        self.defn = defn
        self.name = defn.name
        self.objs = []           # main layer objects (everything you can touch)
        self.bg_objs = []        # background layer (decoration only)
        self.texts = []          # TextObj
        self.triggers = []       # (col, row, settings)
        self.sections = []       # (mode, column of the portal that starts it)
        self.end_col = 0
        self.music = None        # full path of the level's song, if any
        self.theme = ""          # background theme ("" or "underwater")
        self.palette = list(DEFAULT_PALETTE)   # the level's 10 editable colours
        defn.builder(self)
        self.finalize()

    # ---- building helpers ------------------------------------------------
    def _add(self, o):
        self.objs.append(o)
        return o

    def block(self, col, row=0, w=1, h=1, group=0):
        for c in range(col, col + w):
            for r in range(row, row + h):
                self._add(Obj("block", c, r, group=group))

    def floor_pillar(self, col, h, w=2):
        self.block(col, 0, w, h)

    def ceil_pillar(self, col, h, w=2):
        self.block(col, ROWS - h, w, h)

    def spike(self, col, row=0, flip=False, w=1, group=0):
        for c in range(col, col + w):
            self._add(Obj("spike", c, row, flip=flip, group=group))

    def ceil_spike(self, col, w=1):
        self.spike(col, ROWS - 1, flip=True, w=w)

    def ramp(self, col, row, kind, group=0):
        self._add(Obj(kind, col, row, group=group))

    def coin(self, col, row, group=0):
        self._add(Obj("coin", col, row, group=group))

    def pad(self, col, row=0, hidden=False, group=0):
        self._add(Obj("pad", col, row, flip=hidden, group=group))

    def dpad(self, col, row=0, hidden=False, group=0):
        self._add(Obj("dpad", col, row, flip=hidden, group=group))

    def orb(self, col, row, hidden=False, group=0):
        self._add(Obj("orb", col, row, flip=hidden, group=group))

    def dorb(self, col, row, hidden=False, group=0):
        self._add(Obj("dorb", col, row, flip=hidden, group=group))

    def grav(self, col, up):
        self._add(Obj("grav", col, 0, up=up))

    def speed(self, col, val):
        self._add(Obj("speed", col, 0, val=val))

    def text(self, col, row, text, group=0):
        self.texts.append(TextObj(col, row, text, group))

    def trigger(self, col, row=ROWS - 1, **cfg):
        c = clean_trigger(cfg)
        if c:
            self.triggers.append((col, row, c))

    def deco(self, col, row, kind="block", flip=False, w=1, h=1, group=0, color=0):
        for c in range(col, col + w):
            for r in range(row, row + h):
                self.bg_objs.append(Obj(kind, c, r, flip=flip, group=group, color=color))

    # ---- indexing + runtime state (move / reveal / light triggers) ----------
    def finalize(self):
        trig = sorted(self.triggers, key=lambda t: (t[0], t[1]))
        self.move_groups = {c["group"] for _, _, c in trig if c["type"] == "move"}
        first = {}
        for _, _, c in trig:
            if c["type"] == "reveal":
                first.setdefault(c["group"], c["show"])
        self.start_hidden = {g for g, show in first.items() if show}
        self.trig_list = [(col * B, c) for col, _, c in trig]

        self.groups = defaultdict(list)
        self.cols = defaultdict(list)
        self.dyn = []
        self.bg_cols = defaultdict(list)
        self.bg_dyn = []
        for o in self.objs:
            if o.group:
                self.groups[o.group].append(o)
            if o.group in self.move_groups:
                self.dyn.append(o)
            else:
                self.cols[o.col].append(o)
        for o in self.bg_objs:
            if o.group:
                self.groups[o.group].append(o)
            if o.group in self.move_groups:
                self.bg_dyn.append(o)
            else:
                self.bg_cols[o.col].append(o)
        for t in self.texts:
            if t.group:
                self.groups[t.group].append(t)
        self.coins = sorted((o for o in self.objs if o.kind == "coin"),
                            key=lambda o: (o.col, o.row))
        self.starts_px = [c * B + B // 2 for _, c in self.sections]
        sp = sorted((o.col, o.val) for o in self.objs if o.kind == "speed")
        self._speed_x = [c * B + B // 2 for c, _ in sp]
        self._speed_v = [v for _, v in sp]
        self.reset_runtime(0)

    def reset_runtime(self, x):
        """Put every group back where it started, then instantly apply all triggers
        that are behind x (used whenever you (re)spawn)."""
        for g, objs in self.groups.items():
            hid = g in self.start_hidden
            for o in objs:
                o.shift(0.0, 0.0)
                o.hidden = hid
        self.goff = defaultdict(lambda: [0.0, 0.0])
        self.moves = []
        self.light = Light()
        self.next_trig = 0
        while self.next_trig < len(self.trig_list) and self.trig_list[self.next_trig][0] <= x:
            self.fire(self.trig_list[self.next_trig][1], True)
            self.next_trig += 1
        self._update_hidden()

    def _update_hidden(self):
        self.has_hidden = any(o.hidden for objs in self.groups.values() for o in objs)

    def _shift_group(self, g, dx, dy):
        off = self.goff[g]
        off[0] += dx
        off[1] += dy
        for o in self.groups.get(g, ()):
            o.shift(off[0], off[1])

    def fire(self, cfg, instant=False):
        t = cfg["type"]
        if t == "move":
            dx, dy = cfg["dx"] * B, -cfg["dy"] * B
            n = int(round(cfg["time"] * FPS))
            if instant or n <= 0:
                self._shift_group(cfg["group"], dx, dy)
            else:
                self.moves.append([cfg["group"], dx, dy, n, 0, cfg["ease"]])
        elif t == "reveal":
            for o in self.groups.get(cfg["group"], ()):
                o.hidden = not cfg["show"]
            if not instant:
                self._update_hidden()
        elif t == "light":
            self.light.trigger(cfg, instant)

    def update(self, x):
        """Advance triggers by one frame for a player at world x."""
        while self.next_trig < len(self.trig_list) and self.trig_list[self.next_trig][0] <= x:
            self.fire(self.trig_list[self.next_trig][1])
            self.next_trig += 1
        if self.moves:
            keep = []
            for m in self.moves:
                g, dx, dy, n, done, smooth = m
                f = ease if smooth else (lambda u: u)
                a, b = f(done / n), f((done + 1) / n)
                self._shift_group(g, dx * (b - a), dy * (b - a))
                m[4] = done + 1
                if m[4] < n:
                    keep.append(m)
            self.moves = keep
        self.light.update()

    def speed_at(self, x):
        """Speed multiplier in effect at world x (set by the last speed portal passed)."""
        i = bisect.bisect_right(self._speed_x, x) - 1
        return self._speed_v[i] if i >= 0 else 1.0

    def time_at(self, x):
        """Seconds it takes to run from the start to world x (for syncing music)."""
        return time_to_x(self._speed_x, self._speed_v, x)

    def near(self, x):
        c = int(x // B)
        out = []
        for cc in range(c - 2, c + 3):
            lst = self.cols.get(cc)
            if lst:
                out.extend(lst)
        if self.dyn:
            lo, hi = x - 3 * B, x + 3 * B
            out.extend(o for o in self.dyn if o.rect.right > lo and o.rect.left < hi)
        if self.has_hidden:
            out = [o for o in out if not o.hidden]
        return out


def time_to_x(speed_x, speed_v, x):
    pos, t, v = 3.0 * B, 0.0, 1.0
    for sx, sv in zip(speed_x, speed_v):
        if sx <= pos:
            v = sv
            continue
        if sx >= x:
            break
        t += (sx - pos) / (SPEED * v)
        pos, v = sx, sv
    t += max(0.0, x - pos) / (SPEED * v)
    return t / FPS


def music_path(name):
    """Full path of a song in the music folder, or None if it's missing."""
    if not name:
        return None
    p = os.path.join(MUSIC_DIR, os.path.basename(name))
    return p if os.path.isfile(p) else None


def list_songs():
    """Song files in the songs folder, sorted by name."""
    try:
        names = os.listdir(MUSIC_DIR)
    except OSError:
        return []
    return sorted((n for n in names if n.lower().endswith(MUSIC_EXTS)
                   and os.path.isfile(os.path.join(MUSIC_DIR, n))), key=str.lower)


def song_title(name):
    """'my-song-1a2b3c4d5e.mp3' -> 'my-song' (drops the tag added when a song is copied)."""
    base = os.path.splitext(name)[0]
    head, _, tail = base.rpartition("-")
    if head and len(tail) == 10 and all(ch in "0123456789abcdef" for ch in tail):
        return head
    return base


def store_music(src_path=None, raw=None, name_hint="song", ext=".mp3"):
    """Copy a song into the music folder (named by its content, so the same song is
    only stored once) and return its file name."""
    if raw is None:
        with open(src_path, "rb") as f:
            raw = f.read()
        name_hint, ext = os.path.splitext(os.path.basename(src_path))
    digest = hashlib.sha1(raw).hexdigest()[:10]
    name = "%s-%s%s" % (slugify(name_hint)[:30], digest, ext.lower())
    os.makedirs(MUSIC_DIR, exist_ok=True)
    dest = os.path.join(MUSIC_DIR, name)
    if not os.path.isfile(dest):
        with open(dest, "wb") as f:
            f.write(raw)
    return name


# --------------------------------------------------------------------------
# Editable level data (what the editor works on and saves to disk)
# --------------------------------------------------------------------------
class LevelData:
    def __init__(self, name="My Level"):
        self.name = name
        self.start_mode = "cube"
        self.cells = {}      # (col,row) -> (kind, flip, group, color)  main layer
        self.bg = {}         # (col,row) -> (kind, flip, group, color)  background layer
        self.theme = ""      # background theme: "" or "underwater"
        self.palette = list(DEFAULT_PALETTE)   # colour slots 1-10 (editable)
        self.texts = {}      # (col,row) -> (text, group)
        self.triggers = {}   # (col,row) -> settings dict (see clean_trigger)
        self.gravs = {}      # col -> up (True = flips gravity upward)
        self.portals = {}    # col -> mode
        self.speeds = {}     # col -> speed multiplier
        self.finish = None   # column of the finish line (None = automatic)
        self.description = ""   # shown in level select; saved in the level file
        self.author = ""     # username of whoever exported it
        self.music = ""      # file name in the music folder ("" = no song)
        self.path = None

    def snapshot(self):
        return copy.deepcopy((self.cells, self.bg, self.texts, self.triggers, self.gravs,
                              self.portals, self.speeds, self.finish, self.start_mode,
                              self.name, self.description, self.music, self.theme,
                              self.palette))

    def restore(self, snap):
        (self.cells, self.bg, self.texts, self.triggers, self.gravs, self.portals,
         self.speeds, self.finish, self.start_mode, self.name, self.description,
         self.music, self.theme, self.palette) = copy.deepcopy(snap)

    def last_col(self):
        cols = ([c for c, _ in self.cells] + [c for c, _ in self.bg]
                + [c for c, _ in self.texts] + [c for c, _ in self.triggers]
                + list(self.gravs) + list(self.portals) + list(self.speeds))
        return max(cols) if cols else 0

    def mode_list(self):
        return [self.start_mode] + [m for _, m in sorted(self.portals.items())]

    def object_count(self):
        return (len(self.cells) + len(self.bg) + len(self.texts) + len(self.triggers)
                + len(self.gravs) + len(self.portals) + len(self.speeds))

    def coin_count(self):
        return sum(1 for k, _, _ in self.cells.values() if k == "coin")

    def build(self, lv):
        lv.sections = [(self.start_mode, 0)] + [
            (m, c) for c, m in sorted(self.portals.items()) if c > 0]
        for (c, r), (kind, flip, grp, colr) in self.cells.items():
            lv._add(Obj(kind, c, r, flip=flip, group=grp, color=colr))
        lv.palette = [tuple(p) for p in self.palette]
        for (c, r), (kind, flip, grp, colr) in self.bg.items():
            lv.bg_objs.append(Obj(kind, c, r, flip=flip, group=grp, color=colr))
        lv.theme = self.theme
        for (c, r), (text, grp) in self.texts.items():
            lv.text(c, r, text, grp)
        for (c, r), cfg in self.triggers.items():
            lv.triggers.append((c, r, dict(cfg)))
        for c, up in self.gravs.items():
            lv.grav(c, up)
        for c, v in self.speeds.items():
            lv.speed(c, v)
        end = self.finish if self.finish is not None else max(self.last_col() + 12, 40)
        lv.end_col = max(end, lv.sections[-1][1] + 4)
        lv.music = music_path(self.music)

    def to_json(self, embed_music=False):
        j = {
            "name": self.name, "author": self.author, "description": self.description,
            "start_mode": self.start_mode, "finish": self.finish,
            "cells": [[c, r, k, bool(f)] + ([g, col] if col else [g] if g else [])
                      for (c, r), (k, f, g, col) in sorted(self.cells.items())],
            "gravs": [[c, bool(u)] for c, u in sorted(self.gravs.items())],
            "portals": [[c, m] for c, m in sorted(self.portals.items())],
            "speeds": [[c, v] for c, v in sorted(self.speeds.items())],
        }
        if self.bg:
            j["background"] = [[c, r, k, bool(f)] + ([g, col] if col else [g] if g else [])
                               for (c, r), (k, f, g, col) in sorted(self.bg.items())]
        if self.theme:
            j["theme"] = self.theme
        if [tuple(p) for p in self.palette] != DEFAULT_PALETTE:
            j["palette"] = [list(p) for p in self.palette]
        if self.texts:
            j["texts"] = [[c, r, t, g] for (c, r), (t, g) in sorted(self.texts.items())]
        if self.triggers:
            j["triggers"] = [[c, r, cfg] for (c, r), cfg in sorted(self.triggers.items())]
        if self.music:
            j["music"] = self.music
            path = music_path(self.music)
            if embed_music and path:          # exported files carry the song with them
                with open(path, "rb") as f:
                    j["music_data"] = base64.b64encode(f.read()).decode("ascii")
        return j

    @classmethod
    def from_json(cls, j):
        d = cls(str(j.get("name", "Untitled"))[:NAME_MAX])
        d.description = str(j.get("description", ""))[:DESC_MAX]
        d.author = str(j.get("author", "") or "")[:NAME_MAX]
        sm = j.get("start_mode", "cube")
        d.start_mode = sm if sm in MODE_ORDER else "cube"
        fin = j.get("finish")
        d.finish = int(fin) if isinstance(fin, int) else None

        def cells_from(rows, kinds, out, colored=False):
            for item in rows or []:
                try:
                    c, r, k, f = item[:4]
                    g = int(item[4]) if len(item) > 4 else 0
                    col = int(item[5]) if len(item) > 5 else 0
                    c, r = int(c), int(r)
                except (TypeError, ValueError):
                    continue
                if k in kinds and 0 <= r < ROWS and 0 <= c < MAX_COLS:
                    v = (k, bool(f), max(0, min(GROUP_MAX, g)))
                    if colored:
                        v += (col if 0 <= col < COLOR_SLOTS else 0,)
                    out[(c, r)] = v

        cells_from(j.get("cells"), CELL_KINDS, d.cells, colored=True)
        pal = j.get("palette")
        if isinstance(pal, list) and len(pal) == len(DEFAULT_PALETTE):
            try:
                d.palette = [tuple(max(0, min(255, int(v))) for v in p[:3]) for p in pal]
            except (TypeError, ValueError):
                d.palette = list(DEFAULT_PALETTE)
        cells_from(j.get("background"), BG_KINDS, d.bg, colored=True)
        d.theme = j.get("theme") if j.get("theme") in dict(THEMES) else ""
        for item in j.get("texts") or []:
            try:
                c, r, t, g = int(item[0]), int(item[1]), str(item[2]), int(item[3])
            except (TypeError, ValueError, IndexError):
                continue
            if 0 <= r < ROWS and 0 <= c < MAX_COLS and t:
                d.texts[(c, r)] = (t[:TEXT_MAX], max(0, min(GROUP_MAX, g)))
        for item in j.get("triggers") or []:
            try:
                c, r, cfg = int(item[0]), int(item[1]), clean_trigger(item[2])
            except (TypeError, ValueError, IndexError):
                continue
            if cfg and 0 <= r < ROWS and 0 <= c < MAX_COLS:
                d.triggers[(c, r)] = cfg
        for c, u in j.get("gravs", []):
            if 0 <= int(c) < MAX_COLS:
                d.gravs[int(c)] = bool(u)
        for c, m in j.get("portals", []):
            if m in PORTAL_MODES and 0 < int(c) < MAX_COLS:
                d.portals[int(c)] = m
        for c, v in j.get("speeds", []):
            near = min(SPEED_VALUES, key=lambda s: abs(s - float(v)))
            if abs(near - float(v)) < 0.01 and 0 <= int(c) < MAX_COLS:
                d.speeds[int(c)] = near
        music = str(j.get("music", "") or "")
        if j.get("music_data"):               # a shared level that carries its song
            try:
                raw = base64.b64decode(j["music_data"])
                ext = os.path.splitext(music)[1] or ".mp3"
                music = store_music(raw=raw, name_hint=d.name, ext=ext)
            except Exception:
                music = ""
        d.music = os.path.basename(music)
        return d


def level_to_data(level, name):
    """Turn a built Level into editable data (used to copy built-in levels)."""
    d = LevelData(name)
    d.description = str(getattr(level.defn, "description", ""))[:DESC_MAX]
    d.start_mode = level.sections[0][0]
    for o in level.objs:
        if o.kind == "grav":
            d.gravs[o.col] = o.up
        elif o.kind == "speed":
            d.speeds[o.col] = o.val
        else:
            d.cells[(o.col, o.row)] = (o.kind, o.flip, o.group, o.color)
    for o in level.bg_objs:
        d.bg[(o.col, o.row)] = (o.kind, o.flip, o.group, o.color)
    d.theme = level.theme
    d.palette = list(level.palette)
    for t in level.texts:
        d.texts[(t.col, t.row)] = (t.text, t.group)
    for c, r, cfg in level.triggers:
        d.triggers[(c, r)] = dict(cfg)
    for mode, col in level.sections[1:]:
        d.portals[col] = mode
    d.finish = level.end_col
    if level.music:
        d.music = os.path.basename(level.music)
    return d


def custom_def(data, origin="CUSTOM"):
    """origin: "CUSTOM" = built by you in the editor, "OTHER" = imported level file."""
    what = "made in the editor" if origin == "CUSTOM" else "downloaded level"
    blurb = data.description or "%d objects  -  %s" % (data.object_count(), what)
    ld = LevelDef(data.name, origin, blurb, lambda lv, d=data: data.build(lv))
    ld.description = data.description
    ld.path = data.path
    ld.author = data.author
    if origin == "OTHER" and data.author:
        ld.title = "%s by %s" % (data.name, data.author)
    prefix = "custom:" if origin == "CUSTOM" else "other:"
    ld.key = prefix + (os.path.basename(data.path) if data.path else "?")
    return ld


def load_custom_levels(directory=None):
    out = []
    directory = directory or LEVEL_DIR
    try:
        names = sorted(os.listdir(directory))
    except OSError:
        return out
    for fn in names:
        if not fn.endswith(".json") or fn.startswith("_"):     # "_..." = settings files
            continue
        path = os.path.join(directory, fn)
        try:
            with open(path) as f:
                d = LevelData.from_json(json.load(f))
            d.path = path
            out.append(d)
        except Exception:
            continue
    return out


def unique_level_path(name, directory=None):
    directory = directory or LEVEL_DIR
    base = slugify(name)
    path = os.path.join(directory, base + ".json")
    i = 2
    while os.path.exists(path):
        path = os.path.join(directory, "%s-%d.json" % (base, i))
        i += 1
    return path


def copy_name(name, taken):
    """'[Level Name] Copy' - or 'Copy 2', 'Copy 3'... if that name is already used."""
    cand = (name[:NAME_MAX - 5] + " Copy")
    n = 2
    while cand in taken:
        suffix = " Copy %d" % n
        cand = name[:NAME_MAX - len(suffix)] + suffix
        n += 1
    return cand


def slugify(name):
    s = "".join(ch.lower() if ch.isalnum() else "-" for ch in name).strip("-")
    while "--" in s:
        s = s.replace("--", "-")
    return s or "level"


# --------------------------------------------------------------------------
# Obstacle patterns.  Each takes (level, column, *args), places objects
# starting at `column` and returns how many columns it used (including the
# breathing room after it).
# --------------------------------------------------------------------------
# --- cube ---
def p_cube_spike(lv, c):
    lv.spike(c)
    return 9


def p_cube_double(lv, c):
    lv.spike(c, w=2)
    return 9


def p_cube_split(lv, c):
    lv.spike(c, w=2)
    lv.spike(c + 6)
    return 14


def p_cube_step(lv, c):
    lv.block(c, 0, 3, 1)
    return 10


def p_cube_stairs(lv, c):
    lv.block(c, 0, 2, 1)
    lv.block(c + 2, 0, 2, 2)
    lv.block(c + 4, 0, 2, 3)
    return 14


def p_cube_pad(lv, c):
    lv.pad(c)
    lv.block(c + 2, 0, 3, 2)
    return 12


def p_cube_orb(lv, c):
    lv.spike(c, w=5)
    lv.orb(c + 2, 1)
    return 13


def p_cube_orb2(lv, c):          # two orbs in a row over a long spike bed
    lv.spike(c, w=9)
    lv.orb(c + 2, 1)
    lv.orb(c + 6, 1)
    return 17


def p_cube_platform(lv, c):      # hop onto a long block, hop a spike on top
    lv.block(c, 0, 7, 1)
    lv.spike(c + 4, row=1)
    return 14


def p_cube_dorb(lv, c):          # a pad flings you up; the blue orb slams you back down
    lv.pad(c)                    # in time to land before the spikes
    lv.dorb(c + 2, 3)
    lv.spike(c + 5, w=3)
    return 14


def p_speed(lv, c, val):         # a speed portal (0.8, 1.0, 1.25, 1.5 or 1.8)
    lv.speed(c, val)
    return 7


# --- ship ---
def p_ship_gap(lv, c, fh, ch):
    if fh:
        lv.floor_pillar(c, fh)
    if ch:
        lv.ceil_pillar(c, ch)
    return 10


def p_ship_stairs(lv, c):
    lv.floor_pillar(c, 1)
    lv.floor_pillar(c + 4, 2)
    lv.floor_pillar(c + 8, 3)
    return 18


def p_ship_flip(lv, c):
    lv.grav(c, up=True)
    lv.spike(c + 6, w=4)
    lv.ceil_spike(c + 12, w=4)
    lv.grav(c + 20, up=False)
    return 28


# --- ball ---
def p_ball_floor(lv, c):
    lv.spike(c)
    return 9


def p_ball_ceil(lv, c):
    lv.ceil_spike(c)
    return 9


def p_ball_double(lv, c):
    lv.spike(c, w=2)
    return 9


def p_ball_pair(lv, c):
    lv.spike(c)
    lv.ceil_spike(c + 6)
    return 15


def p_ball_step(lv, c):
    lv.block(c, 0, 3, 1)
    return 10


def p_ball_cstep(lv, c):
    lv.ceil_pillar(c, 1, 3)
    return 10


# --- ufo ---
def p_ufo_floor(lv, c, h=3):
    lv.floor_pillar(c, h)
    return 11


def p_ufo_ceil(lv, c, h=4):
    lv.ceil_pillar(c, h)
    return 11


def p_ufo_gap(lv, c):
    lv.floor_pillar(c, 3)
    lv.ceil_pillar(c, 3)
    return 11


def p_ufo_spikes(lv, c):
    lv.spike(c, w=3)
    return 10


def p_ufo_flip(lv, c):
    lv.grav(c, up=True)
    lv.ceil_pillar(c + 8, 3)
    lv.floor_pillar(c + 14, 3)
    lv.grav(c + 18, up=False)
    return 26


# --- wave ---
WAVE_VARIANTS = {
    # (centre keypoints, gap keypoints) in rows, relative column
    "a": ([(0, 5), (12, 5), (28, 7.5), (38, 7.5), (56, 2.6), (66, 2.6), (72, 5)],
          [(0, 10), (12, 4.5), (64, 4.5), (72, 10)]),
    "b": ([(0, 5), (12, 5), (28, 2.6), (38, 2.6), (56, 7.5), (66, 7.5), (72, 5)],
          [(0, 10), (12, 4.5), (64, 4.5), (72, 10)]),
    "c": ([(0, 5), (12, 5), (22, 7.8), (32, 2.2), (42, 7.8), (52, 2.2), (60, 5), (72, 5)],
          [(0, 10), (12, 4.2), (60, 4.2), (72, 10)]),
}


def p_wave_tunnel(lv, c, variant="a"):
    centre, gap = WAVE_VARIANTS[variant]
    for k in range(0, 73):
        g_ = _interp(gap, k)
        c_ = _interp(centre, k)
        floor_h = int(math.floor(c_ - g_ / 2 + 1e-6))
        ceil_h = ROWS - int(math.ceil(c_ + g_ / 2 - 1e-6))
        if floor_h > 0:
            lv.block(c + k, 0, 1, floor_h)
        if ceil_h > 0:
            lv.block(c + k, ROWS - ceil_h, 1, ceil_h)
    return 80


def p_wave_zigzag(lv, c):
    lv.spike(c)
    lv.ceil_spike(c + 4)
    lv.spike(c + 8)
    lv.ceil_spike(c + 12)
    return 20


def p_wave_pillars(lv, c):
    lv.floor_pillar(c, 4)
    lv.ceil_pillar(c + 8, 4)
    lv.floor_pillar(c + 16, 4)
    lv.ceil_pillar(c + 24, 4)
    return 34


# --- robot ---
def p_robot_spike(lv, c):
    lv.spike(c)
    return 9


def p_robot_spikes(lv, c):
    lv.spike(c, w=3)
    return 10


def p_robot_tower(lv, c, h=2, w=3):
    lv.block(c, 0, w, h)
    return 10


def p_robot_stairs(lv, c):
    lv.block(c, 0, 2, 1)
    lv.block(c + 2, 0, 2, 2)
    lv.block(c + 4, 0, 2, 3)
    return 14


def p_robot_tower_spike(lv, c):
    lv.block(c, 0, 2, 3)
    lv.spike(c + 7, w=2)
    return 14


# --- spider ---
def p_spider_floor(lv, c):
    lv.spike(c)
    return 9


def p_spider_ceil(lv, c):
    lv.ceil_spike(c)
    return 9


def p_spider_block_floor(lv, c):
    lv.floor_pillar(c, 2)
    return 9


def p_spider_block_ceil(lv, c):
    lv.ceil_pillar(c, 2)
    return 9


def p_spider_pair(lv, c):
    lv.spike(c, w=2)
    lv.ceil_spike(c + 7, w=2)
    return 16


def p_spider_float(lv, c):
    lv.block(c, 4, 3, 1)
    return 10


# --- swing copter ---
def p_swing_pillars(lv, c, fh, ch):
    lv.floor_pillar(c, fh)
    lv.ceil_pillar(c, ch)
    return 11


def p_swing_spikes(lv, c):
    lv.spike(c, w=3)
    lv.ceil_spike(c + 6, w=3)
    return 15


def compose(lv, plan, lead=9, tail=6):
    """plan = [(mode, [(pattern_fn, *args), ...]), ...]"""
    col = 0
    lv.sections = []
    for mode, pats in plan:
        lv.sections.append((mode, col))
        c = col + lead
        for item in pats:
            fn, args = item[0], item[1:]
            c += fn(lv, c, *args)
        col = c + tail - 3
    lv.end_col = col + 3


# --------------------------------------------------------------------------
# The built-in levels
# --------------------------------------------------------------------------
def build_test_course(lv):
    """Every mode, hand-placed.  Columns are in blocks."""
    lv.sections = [
        ("cube", 0), ("ship", 78), ("ball", 148), ("ufo", 212),
        ("wave", 274), ("robot", 374), ("spider", 444), ("swing", 510),
        ("cube", 566),
    ]
    lv.end_col = 600

    # ===== CUBE (0-78): spikes, steps, a jump pad, a jump orb ===============
    lv.spike(14)
    lv.spike(22, w=2)
    lv.block(30, 0, 3, 1)             # step platform
    lv.pad(42)                        # yellow pad -> big jump
    lv.block(44, 0, 3, 2)             # tower you land on after the pad
    lv.spike(58, w=2)
    lv.spike(66, w=5)                 # 5-wide spike bed ...
    lv.orb(68, 1)                     # ... use the orb mid-air

    # ===== SHIP (78-148): pillars + gravity portals ==========================
    lv.floor_pillar(86, 4)
    lv.ceil_pillar(94, 4)
    lv.floor_pillar(102, 4)
    lv.ceil_pillar(102, 2)
    lv.grav(110, up=True)             # gravity flips upward
    lv.spike(116, w=4)
    lv.ceil_spike(122, w=4)
    lv.grav(130, up=False)            # back to normal
    lv.floor_pillar(134, 1)
    lv.floor_pillar(138, 2)
    lv.floor_pillar(142, 3)

    # ===== BALL (148-212): flip between floor and ceiling ====================
    lv.spike(160)
    lv.ceil_spike(170)
    lv.spike(178)
    lv.ceil_spike(184)
    lv.block(194, 0, 3, 1)            # step you can't roll over
    lv.spike(204, w=2)

    # ===== UFO (212-274): hop through gaps ===================================
    lv.floor_pillar(222, 3)
    lv.ceil_pillar(230, 4)
    lv.floor_pillar(238, 3)
    lv.ceil_pillar(238, 3)
    lv.spike(246, w=3)
    lv.grav(254, up=True)             # UFO now falls upward
    lv.ceil_pillar(262, 3)
    lv.floor_pillar(268, 3)
    lv.grav(272, up=False)

    # ===== WAVE (274-374): a winding tunnel then zig-zag spikes ===============
    centre = [(280, 5), (292, 5), (308, 7.5), (318, 7.5),
              (336, 2.6), (346, 2.6), (352, 5)]
    gap = [(280, 10), (292, 4.5), (344, 4.5), (352, 10)]
    for col in range(280, 353):
        g_ = _interp(gap, col)
        c_ = _interp(centre, col)
        floor_h = int(math.floor(c_ - g_ / 2 + 1e-6))
        ceil_h = ROWS - int(math.ceil(c_ + g_ / 2 - 1e-6))
        if floor_h > 0:
            lv.block(col, 0, 1, floor_h)
        if ceil_h > 0:
            lv.block(col, ROWS - ceil_h, 1, ceil_h)
    lv.spike(358)
    lv.ceil_spike(362)
    lv.spike(366)
    lv.ceil_spike(370)

    # ===== ROBOT (374-444): variable height jumps ============================
    lv.spike(382)
    lv.block(388, 0, 3, 2)
    lv.block(398, 0, 2, 3)
    lv.spike(408, w=2)
    lv.block(416, 0, 2, 1)            # staircase
    lv.block(418, 0, 2, 2)
    lv.block(420, 0, 2, 3)
    lv.spike(430, w=3)

    # ===== SPIDER (444-510): teleport between surfaces =======================
    lv.spike(452)
    lv.ceil_spike(460)
    lv.floor_pillar(468, 2)
    lv.ceil_pillar(476, 2)
    lv.spike(484, w=2)
    lv.ceil_spike(492, w=2)
    lv.block(500, 4, 3, 1)            # floating block: spider sticks to its underside

    # ===== SWING COPTER (510-566): flip gravity anywhere =====================
    lv.floor_pillar(518, 3)
    lv.ceil_pillar(518, 2)
    lv.floor_pillar(526, 2)
    lv.ceil_pillar(526, 3)
    lv.floor_pillar(534, 4)
    lv.ceil_pillar(534, 1)
    lv.floor_pillar(542, 1)
    lv.ceil_pillar(542, 4)
    lv.spike(550, w=3)
    lv.ceil_spike(556, w=3)

    # ===== final CUBE (566-600) ==============================================
    lv.spike(576)
    lv.spike(584, w=2)
    lv.block(592, 0, 2, 1)


def build_warm_up(lv):
    compose(lv, [
        ("cube", [(p_cube_spike,), (p_cube_double,), (p_cube_step,), (p_cube_split,),
                  (p_cube_pad,), (p_cube_spike,), (p_cube_orb,), (p_cube_double,)]),
        ("ship", [(p_ship_gap, 4, 0), (p_ship_gap, 0, 4), (p_ship_gap, 2, 2),
                  (p_ship_gap, 4, 0), (p_ship_stairs,), (p_ship_gap, 0, 4)]),
        ("cube", [(p_cube_stairs,), (p_cube_split,), (p_cube_orb,), (p_cube_step,),
                  (p_cube_double,)]),
    ])


def build_flip_side(lv):
    compose(lv, [
        ("cube", [(p_cube_spike,), (p_cube_double,), (p_cube_split,)]),
        ("ball", [(p_ball_floor,), (p_ball_ceil,), (p_ball_pair,), (p_ball_step,),
                  (p_ball_double,), (p_ball_cstep,), (p_ball_pair,), (p_ball_floor,)]),
        ("spider", [(p_spider_floor,), (p_spider_ceil,), (p_spider_block_floor,),
                    (p_spider_block_ceil,), (p_spider_pair,), (p_spider_float,),
                    (p_spider_pair,)]),
        ("swing", [(p_swing_pillars, 3, 2), (p_swing_pillars, 2, 3),
                   (p_swing_pillars, 4, 1), (p_swing_pillars, 1, 4),
                   (p_swing_spikes,)]),
        ("ball", [(p_ball_pair,), (p_ball_cstep,), (p_ball_floor,)]),
        ("cube", [(p_cube_double,)]),
    ])


def build_wave_runner(lv):
    compose(lv, [
        ("cube", [(p_cube_spike,), (p_cube_double,), (p_cube_step,)]),
        ("wave", [(p_wave_zigzag,), (p_wave_tunnel, "a"), (p_wave_pillars,)]),
        ("ship", [(p_ship_gap, 3, 3), (p_ship_gap, 4, 2)]),
        ("wave", [(p_wave_tunnel, "b"), (p_wave_zigzag,), (p_wave_tunnel, "a")]),
        ("cube", [(p_cube_split,)]),
    ])


def build_robot_factory(lv):
    compose(lv, [
        ("cube", [(p_cube_pad,), (p_cube_orb,), (p_cube_split,)]),
        ("robot", [(p_robot_spike,), (p_robot_tower, 2, 3), (p_robot_stairs,),
                   (p_robot_spikes,), (p_robot_tower_spike,), (p_robot_tower, 3, 2)]),
        ("spider", [(p_spider_floor,), (p_spider_block_floor,), (p_spider_pair,),
                    (p_spider_block_ceil,)]),
        ("robot", [(p_robot_tower_spike,), (p_robot_stairs,), (p_robot_spikes,),
                   (p_robot_tower, 3, 2)]),
        ("ball", [(p_ball_pair,), (p_ball_step,)]),
        ("cube", [(p_cube_orb2,), (p_cube_double,)]),
    ])


def build_turbo(lv):
    compose(lv, [
        ("cube", [(p_cube_spike,), (p_speed, 1.25), (p_cube_double,), (p_cube_step,),
                  (p_cube_orb,), (p_speed, 1.0), (p_cube_dorb,), (p_cube_double,),
                  (p_speed, 1.5), (p_cube_double,), (p_cube_step,), (p_speed, 1.0)]),
        ("ship", [(p_speed, 1.25), (p_ship_gap, 3, 3), (p_ship_gap, 4, 2),
                  (p_ship_gap, 2, 4), (p_ship_gap, 3, 3), (p_speed, 1.0)]),
        ("wave", [(p_speed, 1.5), (p_wave_zigzag,), (p_speed, 0.8), (p_wave_pillars,),
                  (p_speed, 1.0)]),
        ("ufo", [(p_speed, 1.25), (p_ufo_gap,), (p_ufo_floor,), (p_ufo_ceil,),
                 (p_speed, 1.0)]),
        ("cube", [(p_speed, 1.8), (p_cube_spike,), (p_cube_double,), (p_cube_step,),
                  (p_cube_spike,)]),
    ])


def build_sky_high(lv):
    compose(lv, [
        ("ship", [(p_ship_gap, 4, 2), (p_ship_gap, 2, 4), (p_ship_gap, 3, 3),
                  (p_ship_flip,), (p_ship_stairs,), (p_ship_gap, 4, 2)]),
        ("ufo", [(p_ufo_floor,), (p_ufo_ceil,), (p_ufo_gap,), (p_ufo_spikes,),
                 (p_ufo_flip,)]),
        ("wave", [(p_wave_tunnel, "a"), (p_wave_zigzag,), (p_wave_tunnel, "b"),
                  (p_wave_pillars,)]),
        ("ufo", [(p_ufo_gap,), (p_ufo_floor, 4), (p_ufo_ceil, 3)]),
        ("ship", [(p_ship_gap, 3, 3), (p_ship_gap, 4, 2), (p_ship_gap, 2, 4)]),
        ("cube", [(p_cube_double,)]),
    ])


def build_finale(lv):
    compose(lv, [
        ("cube", [(p_cube_split,), (p_cube_orb2,), (p_cube_pad,), (p_cube_platform,),
                  (p_cube_orb,)]),
        ("ship", [(p_ship_gap, 3, 3), (p_ship_gap, 4, 2), (p_ship_flip,),
                  (p_ship_gap, 2, 4)]),
        ("ball", [(p_ball_pair,), (p_ball_step,), (p_ball_cstep,), (p_ball_pair,)]),
        ("ufo", [(p_ufo_gap,), (p_ufo_flip,), (p_ufo_floor, 4)]),
        ("wave", [(p_wave_tunnel, "c"), (p_wave_zigzag,)]),
        ("robot", [(p_robot_tower, 3, 2), (p_robot_stairs,), (p_robot_spikes,),
                   (p_robot_tower_spike,), (p_robot_tower, 2, 3)]),
        ("spider", [(p_spider_pair,), (p_spider_block_floor,), (p_spider_block_ceil,),
                    (p_spider_float,), (p_spider_pair,)]),
        ("swing", [(p_swing_pillars, 3, 3), (p_swing_pillars, 2, 4),
                   (p_swing_pillars, 4, 2), (p_swing_spikes,)]),
        ("cube", [(p_cube_orb2,), (p_cube_split,)]),
    ])


# --------------------------------------------------------------------------
# Insane levels built with the newer objects: ramps, coins, triggers, text
# --------------------------------------------------------------------------
def boundary_heights(keys):
    """keys = [(column offset, height), ...]  ->  a height for every column boundary,
    moving at most 1 row per column (so ramps can join the steps)."""
    out = [keys[0][1]]
    for off, h in keys[1:]:
        while len(out) <= off:
            cur = out[-1]
            out.append(cur + (h > cur) - (h < cur))
    return out


def ramp_corridor(lv, c, floor_keys, ceil_keys, group=0):
    """Solid floor and ceiling (heights in rows) joined by 45-degree ramps.
    Ships and cubes can ride the slopes; the wave must not touch them."""
    fl = boundary_heights(floor_keys)
    ce = boundary_heights(ceil_keys)
    n = min(len(fl), len(ce)) - 1
    for i in range(n):
        a, b = fl[i], fl[i + 1]
        lo = min(a, b)
        if lo:
            lv.block(c + i, 0, 1, lo, group=group)
        if b > a:
            lv.ramp(c + i, a, "ramp_br", group=group)
        elif b < a:
            lv.ramp(c + i, b, "ramp_bl", group=group)
        a, b = ce[i], ce[i + 1]
        lo = min(a, b)
        if lo:
            lv.block(c + i, ROWS - lo, 1, lo, group=group)
        if b > a:
            lv.ramp(c + i, ROWS - a - 1, "ramp_tr", group=group)
        elif b < a:
            lv.ramp(c + i, ROWS - b - 1, "ramp_tl", group=group)
    return n


def gate(lv, c, floor, ceil, w=2, spikes=False):
    """A wall with a gap: `floor` rows from the bottom, `ceil` rows from the top.
    With spikes=True the gap is lined with spikes (their hitboxes are small)."""
    if floor:
        lv.block(c, 0, w, floor)
        if spikes:
            lv.spike(c, floor, w=w)
    if ceil:
        lv.block(c, ROWS - ceil, w, ceil)
        if spikes:
            lv.spike(c, ROWS - ceil - 1, flip=True, w=w)


def build_neon_gauntlet(lv):
    lv.sections = [("cube", 0), ("ship", 56), ("spider", 110), ("wave", 152),
                   ("cube", 208)]
    lv.end_col = 256
    lv.text(3, 6, "NEON GAUNTLET")
    lv.deco(0, 6, "ramp_br")
    lv.deco(1, 6, "block", w=1)

    # ===== CUBE at 1.25x: hops, a ramp hill, then running on the ceiling ======
    lv.speed(8, 1.25)
    lv.block(12, 0)
    lv.spike(13, w=2)
    lv.block(15, 0)
    lv.ramp(21, 0, "ramp_br")                 # a hill with a spike on top
    lv.block(22, 0, 3, 1)
    lv.ramp(25, 0, "ramp_bl")
    lv.spike(23, 1)
    lv.coin(23, 3)                            # coin 1: jump over the hilltop spike
    lv.spike(30, w=2)
    lv.grav(34, up=True)                      # now you run along the ceiling
    lv.spike(41, ROWS - 1, flip=True, w=2)
    lv.block(46, ROWS - 1, 3, 1)
    lv.spike(48, ROWS - 2, flip=True)
    lv.grav(52, up=False)
    lv.deco(36, 3, "block", w=12)

    # ===== SHIP: gates, then a spiked tunnel =================================
    gate(lv, 62, 5, 2)
    gate(lv, 70, 2, 5)
    gate(lv, 78, 4, 3)
    lv.block(84, 0, 10, 3)
    lv.spike(84, 3, w=10)
    lv.block(84, 8, 10, 2)
    lv.spike(84, 7, flip=True, w=10)
    lv.coin(89, 6)                            # coin 2: top of the tunnel
    gate(lv, 98, 6, 1)
    gate(lv, 105, 2, 4)

    # ===== SPIDER at 1x: alternating walls, then spikes on both sides =========
    lv.speed(110, 1.0)
    lv.block(116, 4, 1, 6)
    lv.block(121, 0, 1, 6)
    lv.block(126, 4, 1, 6)
    lv.block(131, 0, 1, 6)
    lv.spike(135, w=3)
    lv.spike(141, ROWS - 1, flip=True, w=3)
    lv.block(147, 5, 3, 1)

    # ===== WAVE through a sloped tunnel, in a circle of light =================
    lv.trigger(154, effect="close_circle", type="light", radius=6, time=1.0)
    c = 152
    ramp_corridor(lv, c,
                  [(0, 0), (8, 0), (12, 4), (15, 4), (19, 0), (21, 0), (25, 4), (28, 4),
                   (32, 0), (34, 0), (39, 5), (41, 5), (45, 1), (48, 1), (49, 0), (54, 0)],
                  [(0, 0), (6, 6), (8, 6), (12, 2), (15, 2), (19, 6), (21, 6), (25, 2),
                   (27, 2), (28, 3), (32, 7), (34, 7), (39, 2), (41, 2), (45, 6), (48, 6),
                   (54, 0)])
    lv.coin(c + 13, 6)                        # coin 3: the first flat bit of the tunnel
    lv.trigger(206, effect="open_circle", type="light", time=1.0)

    # ===== CUBE at 1.5x: a platform appears, a wall lifts out of the way ======
    lv.speed(210, 1.5)
    lv.trigger(212, type="reveal", group=2, show=True)
    lv.pad(219)
    lv.spike(221, w=9)
    lv.block(221, 1, 7, 1, group=2)
    lv.spike(225, 2, group=2)
    lv.block(240, 0, 1, 4, group=3)           # this wall...
    lv.trigger(230, type="move", group=3, dx=0, dy=4, time=0.4)   # ...moves up
    lv.spike(246, w=2)
    lv.text(251, 5, "GG!")


def build_inferno_circuit(lv):
    lv.sections = [("cube", 0), ("ufo", 20), ("ball", 66), ("swing", 106),
                   ("robot", 148), ("ship", 190)]
    lv.end_col = 246
    lv.text(3, 6, "INFERNO CIRCUIT")

    # ===== CUBE ==============================================================
    lv.spike(9, w=2)
    lv.spike(14, w=2)

    # ===== UFO: spiked gaps ==================================================
    gate(lv, 28, 2, 3, w=3, spikes=True)       # gap rows 3-5
    lv.coin(33, 5)                             # coin 1: between the gaps, up high
    gate(lv, 38, 4, 1, w=3, spikes=True)       # gap rows 5-7
    lv.spike(45, w=3)
    gate(lv, 51, 0, 5)                         # stay low
    lv.spike(52, w=1)
    gate(lv, 58, 3, 3, w=3)                    # gap rows 3-6

    # ===== BALL ==============================================================
    lv.spike(72)
    lv.spike(77, ROWS - 1, flip=True)
    lv.coin(80, 5)                             # coin 2: flip right through it
    lv.spike(82, w=2)
    lv.block(86, ROWS - 1, 7, 1)
    lv.spike(90, ROWS - 2, flip=True)
    lv.spike(94, w=2)
    lv.grav(98, up=True)
    lv.spike(100, w=2)
    lv.grav(103, up=False)

    # ===== SWING COPTER: gates with 3-row gaps =================================
    lv.trigger(106, type="light", effect="flicker_off", time=0.5)
    lv.trigger(112, type="light", effect="flicker_on", time=0.5)
    gate(lv, 112, 4, 3)                        # gap rows 4-6
    gate(lv, 119, 2, 5)                        # gap rows 2-4
    gate(lv, 126, 5, 2)                        # gap rows 5-7
    gate(lv, 133, 3, 4)                        # gap rows 3-5
    lv.spike(140, w=3)
    lv.spike(140, ROWS - 1, flip=True, w=3)

    # ===== ROBOT at 1.25x: high jumps, low ceilings ==========================
    lv.speed(148, 1.25)
    lv.spike(154, w=2)
    lv.block(164, 0, 2, 3)                     # hold for a big jump (plenty of run-up)
    lv.coin(164, 4)                            # coin 3: top of the tower
    lv.block(170, 6, 5, 4)                     # low ceiling - keep it small
    lv.spike(172, w=2)
    lv.block(181, 0, 3, 2)
    lv.spike(182, 2)

    # ===== SHIP at 1x: spiked corridor, then ride the ramps =====================
    lv.speed(190, 1.0)
    lv.block(196, 0, 13, 3)
    lv.spike(196, 3, w=13)
    lv.block(196, 8, 13, 2)
    lv.spike(196, 7, flip=True, w=13)
    ramp_corridor(lv, 212,
                  [(0, 0), (2, 0), (6, 4), (9, 4), (13, 7), (16, 7), (21, 2), (23, 2),
                   (25, 0), (30, 0)],
                  [(0, 0), (3, 3), (6, 3), (9, 3), (12, 0), (16, 0), (21, 5), (23, 5),
                   (30, 0)])
    lv.text(243, 5, "GG!")


def build_abyss_drift(lv):
    lv.sections = [("cube", 0), ("ship", 46), ("cube", 96), ("spider", 146),
                   ("swing", 186)]
    lv.end_col = 236
    lv.text(3, 6, "ABYSS DRIFT")

    # ===== CUBE at 1.5x: block hops ===========================================
    lv.speed(6, 1.5)
    lv.block(12, 0, 2, 1)
    lv.spike(14, w=2)
    lv.block(16, 0, 2, 1)
    lv.ramp(23, 0, "ramp_br")
    lv.block(24, 0, 2, 1)
    lv.ramp(26, 1, "ramp_br")
    lv.block(26, 0, 1, 1)
    lv.block(27, 0, 3, 2)
    lv.spike(30, w=4)
    lv.coin(31, 4)                            # coin 1: big jump off the stairs
    lv.spike(39, w=2)

    # ===== SHIP at 1.5x: up/down gravity, rising gates ========================
    gate(lv, 52, 4, 2)
    gate(lv, 59, 1, 5)
    lv.grav(64, up=True)
    gate(lv, 70, 5, 1)
    lv.coin(76, 3)                            # coin 2: dive low between the gates
    gate(lv, 80, 2, 4, spikes=True)
    lv.grav(86, up=False)
    gate(lv, 90, 3, 3)

    # ===== CUBE at 1x: flipping between floor and ceiling =====================
    lv.speed(96, 1.0)
    lv.spike(102, w=2)
    lv.grav(106, up=True)
    lv.spike(113, ROWS - 1, flip=True, w=2)
    lv.block(118, ROWS - 1, 2, 1)
    lv.grav(122, up=False)
    lv.spike(128, w=5)
    lv.orb(130, 1)
    lv.coin(131, 4)                           # coin 3: ride the orb up to it
    lv.pad(137)
    lv.dorb(139, 3)
    lv.spike(142, w=3)

    # ===== SPIDER at 1x =======================================================
    lv.block(152, 5, 1, 5)
    lv.block(157, 0, 1, 5)
    lv.block(162, 5, 1, 5)
    lv.spike(166, w=3)
    lv.spike(172, ROWS - 1, flip=True, w=3)
    lv.block(178, 0, 1, 5)
    lv.block(182, 5, 1, 5)

    # ===== SWING at 1.25x in the dark =========================================
    lv.speed(186, 1.25)
    lv.trigger(188, type="light", effect="close_circle", radius=7, time=0.8)
    gate(lv, 194, 4, 3)
    gate(lv, 201, 2, 5)
    gate(lv, 208, 5, 2)
    gate(lv, 215, 3, 4)
    lv.trigger(222, type="light", effect="open_circle", time=0.8)
    lv.spike(224, w=3)
    lv.spike(224, ROWS - 1, flip=True, w=3)
    lv.text(232, 5, "GG!")


def coral(lv, c, h, color):
    """A little background coral: a stack of blocks with a pointed top."""
    lv.deco(c, 0, "block", h=h, color=color)
    lv.deco(c - 1, 0, "ramp_br", color=color)
    lv.deco(c + 1, 0, "ramp_bl", color=color)
    lv.deco(c, h, "spike", color=color)


def build_axolotl_lagoon(lv):
    lv.theme = "underwater"
    lv.sections = [("cube", 0), ("ufo", 40), ("ship", 88), ("swing", 140), ("cube", 184)]
    lv.end_col = 228
    lv.text(3, 6, "AXOLOTL LAGOON")
    for i, c in enumerate(range(9, 226, 11)):          # coral along the sea floor
        coral(lv, c, 1 + (i * 7) % 3, (9, 4, 8, 3, 6)[i % 5])

    # ===== CUBE: a sandy hill ===================================================
    lv.spike(11)
    lv.spike(17, w=2)
    lv.ramp(23, 0, "ramp_br")
    lv.block(24, 0, 3, 1)
    lv.ramp(27, 0, "ramp_bl")
    lv.spike(25, 1)
    lv.coin(25, 3)                              # coin 1: over the hilltop spike
    lv.spike(32, w=2)

    # ===== UFO: swim through the rocks ==========================================
    gate(lv, 48, 2, 4)                          # gap rows 2-5
    gate(lv, 56, 4, 2)                          # gap rows 4-7
    lv.spike(62, w=3)
    gate(lv, 68, 2, 3, spikes=True)             # gap rows 3-5, spiky
    lv.coin(74, 7)                              # coin 2: up high between the rocks
    gate(lv, 78, 5, 1)                          # gap rows 5-8

    # ===== SHIP: a kelp tunnel you can ride ====================================
    gate(lv, 94, 4, 3)
    gate(lv, 101, 2, 4)
    ramp_corridor(lv, 108, [(0, 0), (3, 0), (6, 3), (9, 3), (12, 0), (16, 0)],
                  [(0, 0), (3, 3), (6, 3), (9, 3), (12, 6), (14, 6), (16, 0)])
    lv.coin(129, 7)                             # coin 3: hug the surface
    gate(lv, 130, 5, 2)                         # gap rows 5-7
    gate(lv, 136, 2, 5)                         # gap rows 2-4

    # ===== SWING: bob between the reefs ========================================
    gate(lv, 146, 4, 3)
    gate(lv, 153, 2, 5)
    gate(lv, 160, 5, 2)
    gate(lv, 167, 3, 4)
    lv.spike(174, w=3)
    lv.spike(174, ROWS - 1, flip=True, w=3)

    # ===== CUBE: bubble (orb) jumps home ========================================
    lv.spike(190, w=5)
    lv.orb(192, 1)
    lv.pad(200)
    lv.block(202, 0, 3, 2)
    lv.spike(210, w=2)
    lv.spike(216)
    lv.text(222, 5, "You found the axolotls!")


def build_dolphin_bay(lv):
    lv.theme = "ocean"
    lv.sections = [("cube", 0), ("wave", 34), ("ufo", 100), ("wave", 140), ("cube", 206)]
    lv.end_col = 238
    lv.text(3, 6, "DOLPHIN BAY")
    for i, c in enumerate(range(12, 232, 17)):          # rocks on the sea floor
        coral(lv, c, 1 + (i * 5) % 2, (7, 6, 1)[i % 3])

    # ===== CUBE ============================================================
    lv.spike(10)
    lv.spike(16, w=2)
    lv.coin(16, 2)                              # coin 1: jump through it over the spikes
    lv.block(22, 0, 3, 1)
    lv.spike(25, w=2)

    # ===== WAVE: a sloped channel, 4 rows wide ==============================
    ramp_corridor(lv, 40,
                  [(0, 0), (6, 0), (10, 4), (13, 4), (17, 0), (20, 0), (23, 3), (27, 3),
                   (30, 0), (33, 0), (37, 4), (40, 4), (44, 0), (50, 0)],
                  [(0, 0), (6, 6), (10, 2), (13, 2), (17, 6), (20, 6), (23, 3), (27, 3),
                   (30, 6), (33, 6), (37, 2), (40, 2), (44, 6), (46, 6), (50, 0)])
    lv.coin(51, 7)                              # coin 2: top of the first flat
    lv.spike(92)
    lv.ceil_spike(96)

    # ===== UFO =============================================================
    gate(lv, 108, 2, 4)                         # gap rows 2-5
    gate(lv, 116, 4, 2)                         # gap rows 4-7
    lv.spike(122, w=3)
    gate(lv, 128, 3, 3)                         # gap rows 3-6

    # ===== WAVE: the channel narrows to 3 rows ===============================
    ramp_corridor(lv, 146,
                  [(0, 0), (5, 0), (9, 4), (13, 4), (16, 1), (18, 1), (22, 5), (24, 5),
                   (28, 1), (30, 1), (31, 0), (36, 0)],
                  [(0, 0), (5, 5), (9, 1), (11, 1), (13, 3), (16, 6), (18, 6), (22, 2),
                   (24, 2), (28, 6), (30, 6), (36, 0)])
    lv.coin(169, 6)                             # coin 3: the narrowest flat
    lv.floor_pillar(188, 4)
    lv.ceil_pillar(195, 4)

    # ===== CUBE home =========================================================
    lv.spike(214)
    lv.block(220, 0, 2, 1)
    lv.spike(222, w=2)
    lv.text(233, 5, "Splash!")


def build_chopper_city(lv):
    lv.theme = "city"
    lv.sections = [("cube", 0), ("swing", 40), ("ship", 92), ("spider", 132),
                   ("swing", 170), ("cube", 226)]
    lv.end_col = 262
    lv.text(3, 6, "CHOPPER CITY")

    # ===== CUBE at 1.25x: over the rooftops ==================================
    lv.speed(6, 1.25)
    lv.block(12, 0)
    lv.spike(13, w=2)
    lv.block(15, 0)
    lv.block(19, 0)                             # step up onto a roof...
    lv.block(20, 0, 3, 2)
    lv.coin(21, 4)                              # coin 1: jump on the roof to grab it
    lv.spike(23, w=2)                           # ...then leap off it
    lv.spike(30, w=3)

    # ===== SWING: weave between the towers ===================================
    gate(lv, 46, 4, 3)                          # gap rows 4-6
    gate(lv, 53, 2, 5)                          # gap rows 2-4
    gate(lv, 60, 5, 2)                          # gap rows 5-7
    lv.coin(57, 7)                              # coin 2: fly high between towers
    gate(lv, 67, 3, 4)                          # gap rows 3-5
    gate(lv, 74, 2, 3, spikes=True)             # gap rows 3-5, spiky
    gate(lv, 81, 4, 1, spikes=True)             # gap rows 5-7, spiky

    # ===== SHIP: between skyscrapers ===========================================
    gate(lv, 98, 4, 3)
    gate(lv, 104, 1, 6)                         # gap rows 1-3
    gate(lv, 111, 5, 2)                         # gap rows 5-7
    lv.block(116, 0, 10, 2)                     # spiky street canyon
    lv.spike(116, 2, w=10)
    lv.block(116, 7, 10, 3)
    lv.spike(116, 6, flip=True, w=10)
    gate(lv, 128, 3, 4)

    # ===== SPIDER: scaffolding =================================================
    lv.block(138, 4, 1, 6)
    lv.block(143, 0, 1, 6)
    lv.block(148, 4, 1, 6)
    lv.block(153, 0, 1, 6)
    lv.spike(157, w=3)
    lv.spike(163, ROWS - 1, flip=True, w=3)

    # ===== SWING at 1.5x: rush hour ============================================
    lv.speed(170, 1.5)
    gate(lv, 178, 4, 3)
    gate(lv, 186, 2, 5)
    gate(lv, 194, 5, 2)
    lv.coin(191, 7)                             # coin 3: up by the rooftops
    gate(lv, 202, 3, 4)
    gate(lv, 210, 1, 6)
    gate(lv, 218, 4, 2)

    # ===== CUBE at 1.25x: touchdown =============================================
    lv.speed(226, 1.25)
    lv.spike(234, w=2)                          # room to land after the swing first
    lv.block(241, 0, 4, 1)                      # hop onto a rooftop, run off the end...
    lv.spike(250, w=2)                          # ...then clear these with room to spare
    lv.text(258, 5, "Touchdown!")


def build_crystal_caverns(lv):
    lv.theme = "crystal"
    lv.sections = [("cube", 0), ("spider", 34), ("ufo", 80), ("spider", 120),
                   ("ball", 170), ("cube", 214)]
    lv.end_col = 252
    lv.text(3, 6, "CRYSTAL CAVERNS")

    # ===== CUBE at 1.25x ===================================================
    lv.speed(6, 1.25)
    lv.spike(11, w=2)
    lv.spike(19, w=2)
    lv.spike(27, w=2)

    # ===== SPIDER at 1x: a crystal maze ======================================
    lv.speed(34, 1.0)
    lv.block(40, 4, 1, 6)                       # ceiling wall: stay on the floor
    lv.block(45, 0, 1, 6)                       # floor wall: be on the ceiling
    lv.block(50, 4, 1, 6)
    lv.coin(53, 0)                              # coin 1: wait until the last moment
    lv.block(55, 0, 1, 6)
    lv.spike(59, w=3)
    lv.spike(64, ROWS - 1, flip=True, w=3)
    lv.ramp(69, 0, "ramp_br")                   # a crystal hump to scuttle over
    lv.block(70, 0)
    lv.ramp(71, 0, "ramp_bl")
    lv.spike(70, ROWS - 1, flip=True)

    # ===== UFO: spiky gaps ===================================================
    gate(lv, 88, 2, 3, w=3, spikes=True)        # gap rows 3-5
    gate(lv, 96, 4, 1, w=3, spikes=True)        # gap rows 5-7
    gate(lv, 104, 1, 4, w=2)                    # gap rows 1-5
    gate(lv, 111, 3, 2, w=3, spikes=True)       # gap rows 4-6

    # ===== SPIDER at 1.25x: the deep caves ====================================
    lv.speed(120, 1.25)
    lv.block(126, 4, 1, 6)
    lv.block(131, 0, 1, 6)
    lv.block(136, 4, 1, 6)
    lv.block(141, 0, 1, 6)
    lv.block(146, 4, 1, 6)
    lv.spike(150, w=3)
    lv.spike(156, ROWS - 1, flip=True, w=3)
    lv.block(162, 3, 2, 4)                      # a floating crystal
    lv.coin(164, ROWS - 1)                      # coin 2: on the ceiling past it

    # ===== BALL at 1.25x =====================================================
    lv.spike(176)
    lv.spike(184, ROWS - 1, flip=True)
    lv.coin(188, 5)                             # coin 3: flip through it
    lv.spike(192, w=2)
    lv.spike(200, ROWS - 1, flip=True, w=2)
    lv.spike(208)

    # ===== CUBE at 1.25x: the way out =========================================
    lv.spike(222, w=2)
    lv.block(230, 0, 4, 1)
    lv.spike(239, w=2)
    lv.text(247, 5, "You escaped!")


def build_backyard_pups(lv):
    lv.theme = "backyard"
    lv.sections = [("cube", 0), ("robot", 34), ("ship", 84), ("robot", 124),
                   ("ufo", 176), ("cube", 212)]
    lv.end_col = 252
    lv.text(3, 6, "BACKYARD PUPS")

    # ===== CUBE at 1.25x ===================================================
    lv.speed(6, 1.25)
    lv.spike(11)
    lv.spike(19, w=2)
    lv.spike(27, w=2)

    # ===== ROBOT at 1x: over the garden furniture =============================
    lv.speed(34, 1.0)
    lv.block(41, 0, 2, 2)                       # a medium jump
    lv.spike(47, w=2)
    lv.block(57, 0, 2, 3)                       # hold for a big jump (plenty of run-up)
    lv.coin(57, 4)                              # coin 1: on top of the tall box
    lv.block(64, 6, 5, 4)                       # a low branch - keep the hop small
    lv.spike(65, w=2)
    lv.block(74, 0, 3, 1)
    lv.spike(75, 1)

    # ===== SHIP: over the hedges ==============================================
    gate(lv, 90, 4, 3)
    gate(lv, 97, 2, 5)
    gate(lv, 104, 2, 3, spikes=True)            # gap rows 3-5, spiky
    gate(lv, 111, 5, 2)
    lv.coin(115, 8)                             # coin 2: up by the tree tops

    # ===== ROBOT at 1.25x: the doghouse run ===================================
    lv.speed(124, 1.25)
    lv.spike(130, w=2)
    lv.block(141, 0, 2, 3)                      # big jump (plenty of run-up)
    lv.spike(149, w=2)
    lv.ramp(155, 0, "ramp_br")                  # the doghouse roof
    lv.block(156, 0)
    lv.ramp(157, 0, "ramp_bl")
    lv.coin(156, 3)                             # coin 3: leap off the roof
    lv.block(164, 6, 4, 4)                      # low branch
    lv.spike(165, w=2)
    lv.spike(171, w=2)

    # ===== UFO: chasing the ball ===============================================
    gate(lv, 184, 2, 3, w=3, spikes=True)       # gap rows 3-5
    gate(lv, 192, 4, 1, w=3, spikes=True)       # gap rows 5-7
    gate(lv, 200, 1, 4, w=2)                    # gap rows 1-5

    # ===== CUBE at 1.25x: home time ============================================
    lv.speed(212, 1.25)
    lv.spike(220, w=2)
    lv.spike(228, w=2)
    lv.spike(236, w=2)
    lv.text(247, 5, "Good dog!")


# --------------------------------------------------------------------------
# Demons.  TOP_DEMONS is the demon list, hardest first: TOP_DEMONS[0] is the
# "Top 1".  Beating whatever level is Top 1 at the time earns the Crown cube for
# good - it stays unlocked even if a new level takes the Top 1 spot later.
# --------------------------------------------------------------------------
VELOCITY_BATTLE = json.loads('{"name":"Velocity Battle","author":"AugmentedMagic","description":"","start_mode":"cube","finish":460,"cells":[[6,0,"block",false,1],[7,0,"block",false,2],[8,0,"spike",false,3],[9,0,"spike",false,4],[10,0,"spike",false,5],[11,0,"block",false,6],[12,0,"block",false,7],[13,0,"spike",false,8],[14,0,"spike",false,9],[15,0,"block",false,10],[20,9,"block",false],[21,9,"block",false],[22,9,"block",false],[23,8,"spike",true],[23,9,"block",false],[24,8,"spike",true],[24,9,"block",false],[25,8,"spike",true],[25,9,"block",false],[26,9,"block",false],[27,9,"block",false],[28,9,"block",false],[29,9,"block",false],[30,9,"block",false],[31,9,"block",false],[32,9,"block",false],[33,0,"spike",false],[33,9,"block",false],[34,0,"spike",false],[34,9,"block",false],[35,0,"spike",false],[35,9,"block",false],[36,0,"block",false],[36,9,"block",false],[37,9,"block",false],[38,1,"spike",true,11],[38,2,"block",false,11],[38,3,"block",false,11],[38,4,"block",false,11],[38,9,"block",false],[39,1,"spike",true,11],[39,2,"block",false,11],[39,3,"block",false,11],[39,4,"orb",false,11],[39,5,"block",false,11],[39,9,"block",false],[40,1,"spike",true,11],[40,2,"block",false,11],[40,3,"block",false,11],[40,4,"block",false,11],[40,5,"block",false,11],[40,9,"spike",true],[41,1,"spike",true,11],[41,2,"block",false,11],[41,3,"block",false,11],[41,4,"orb",false,11],[41,5,"block",false,11],[41,9,"spike",true],[42,1,"spike",true,11],[42,2,"block",false,11],[42,3,"block",false,11],[42,4,"block",false,11],[42,9,"spike",true],[43,9,"spike",true],[44,9,"block",false],[45,9,"block",false],[47,0,"spike",false],[47,9,"spike",true],[48,0,"spike",false],[48,9,"spike",true],[49,0,"spike",false],[49,9,"spike",true],[50,0,"spike",false],[50,9,"spike",true],[51,0,"spike",false],[51,9,"spike",true],[52,0,"spike",false],[52,9,"spike",true],[53,0,"spike",false],[53,9,"spike",true],[54,0,"spike",false],[54,9,"spike",true],[58,4,"block",false],[58,5,"block",false],[59,3,"block",false],[59,4,"block",false],[59,5,"block",false],[59,6,"block",false],[60,2,"block",false],[60,3,"block",false],[60,4,"block",false],[60,5,"block",false],[60,6,"block",false],[60,7,"block",false],[61,1,"block",false],[61,2,"block",false],[61,3,"block",false],[61,4,"block",false],[61,5,"block",false],[61,6,"block",false],[61,7,"block",false],[61,8,"block",false],[62,1,"block",false],[62,2,"block",false],[62,3,"block",false],[62,4,"block",false],[62,5,"block",false],[62,6,"block",false],[62,7,"block",false],[62,8,"block",false],[63,2,"block",false],[63,3,"block",false],[63,4,"block",false],[63,5,"block",false],[63,6,"block",false],[63,7,"block",false],[64,3,"block",false],[64,4,"block",false],[64,5,"block",false],[64,6,"block",false],[65,4,"block",false],[65,5,"block",false],[70,9,"block",false],[71,9,"block",false],[72,9,"block",false],[73,8,"spike",true],[73,9,"block",false],[74,8,"spike",true],[74,9,"block",false],[75,8,"spike",true],[75,9,"block",false],[76,9,"block",false],[77,7,"block",false],[77,8,"block",false],[77,9,"block",false],[78,7,"block",false],[78,8,"block",false],[78,9,"block",false],[79,7,"block",false],[79,8,"block",false],[79,9,"block",false],[80,0,"block",false],[80,1,"block",false],[80,2,"block",false],[80,3,"spike",false],[80,7,"block",false],[80,8,"block",false],[80,9,"block",false],[81,0,"block",false],[81,1,"block",false],[81,2,"block",false],[81,3,"spike",false],[81,7,"block",false],[81,8,"block",false],[81,9,"block",false],[82,0,"block",false],[82,1,"block",false],[82,2,"block",false],[82,7,"block",false],[82,8,"block",false],[82,9,"block",false],[83,0,"block",false],[83,1,"block",false],[83,2,"block",false],[83,7,"block",false],[83,8,"block",false],[83,9,"block",false],[84,0,"block",false],[84,1,"orb",false],[84,2,"block",false],[84,6,"spike",true],[84,7,"block",false],[84,8,"block",false],[84,9,"block",false],[85,0,"block",false],[85,1,"block",false],[85,2,"block",false],[85,6,"spike",true],[85,7,"block",false],[85,8,"block",false],[85,9,"block",false],[86,0,"block",false],[86,1,"block",false],[86,2,"block",false],[86,9,"block",false],[87,0,"block",false],[87,1,"orb",false],[87,2,"block",false],[87,9,"block",false],[88,0,"block",false],[88,1,"block",false],[88,2,"block",false],[88,9,"block",false],[89,0,"block",false],[89,1,"block",false],[89,2,"block",false],[89,3,"block",false],[89,4,"block",false],[89,5,"block",false],[89,9,"block",false],[90,9,"block",false],[91,9,"block",false],[92,1,"block",false],[92,2,"block",false],[92,3,"block",false],[92,4,"block",false],[92,5,"block",false],[92,6,"block",false],[92,7,"block",false],[92,8,"block",false],[92,9,"block",false],[93,9,"spike",true],[95,0,"spike",false],[96,0,"spike",false],[97,0,"spike",false],[100,1,"block",false],[100,2,"block",false],[100,3,"block",false],[100,4,"block",false],[100,5,"block",false],[100,6,"block",false],[100,7,"block",false],[100,8,"block",false],[100,9,"block",false],[103,0,"block",false],[103,1,"block",false],[103,2,"block",false],[103,3,"block",false],[103,4,"block",false],[103,5,"block",false],[103,6,"block",false],[103,7,"block",false],[103,8,"block",false],[106,1,"block",false],[106,2,"block",false],[106,3,"block",false],[106,4,"block",false],[106,5,"block",false],[106,6,"block",false],[106,7,"block",false],[106,8,"block",false],[106,9,"block",false],[107,9,"block",false],[108,9,"block",false],[109,9,"block",false],[110,0,"block",false],[110,1,"block",false],[110,2,"block",false],[110,3,"block",false],[110,4,"block",false],[110,5,"block",false],[110,6,"block",false],[110,7,"block",false],[110,9,"block",false],[111,7,"block",false],[111,9,"block",false],[112,9,"block",false],[113,1,"spike",true,11],[113,2,"block",false,11],[113,3,"block",false,11],[113,4,"block",false,11],[113,7,"block",false],[113,9,"block",false],[114,1,"spike",true,11],[114,2,"block",false,11],[114,3,"block",false,11],[114,4,"orb",false,11],[114,5,"block",false,11],[114,7,"block",false],[115,1,"spike",true,11],[115,2,"block",false,11],[115,3,"block",false,11],[115,4,"block",false,11],[115,5,"block",false,11],[115,7,"block",false],[115,9,"block",false],[116,1,"spike",true,11],[116,2,"block",false,11],[116,3,"block",false,11],[116,4,"orb",false,11],[116,5,"block",false,11],[116,9,"block",false],[117,1,"spike",true,11],[117,2,"block",false,11],[117,3,"block",false,11],[117,4,"block",false,11],[117,7,"block",false],[117,9,"block",false],[118,7,"block",false],[119,7,"block",false],[119,9,"block",false],[120,9,"block",false],[121,7,"block",false],[121,9,"block",false],[122,0,"coin",false],[122,7,"block",false],[123,0,"pad",false],[125,0,"block",false],[126,0,"block",false],[127,0,"block",false],[128,0,"block",false],[129,0,"block",false],[130,0,"block",false],[131,0,"block",false],[132,0,"spike",false],[133,0,"spike",false],[133,4,"spike",true,11],[133,5,"block",false,11],[133,6,"block",false,11],[133,7,"block",false,11],[134,0,"spike",false],[134,4,"spike",true,11],[134,5,"block",false,11],[134,6,"block",false,11],[134,7,"orb",false,11],[134,8,"block",false,11],[135,0,"spike",false],[135,4,"spike",true,11],[135,5,"block",false,11],[135,6,"block",false,11],[135,7,"block",false,11],[135,8,"block",false,11],[136,0,"spike",false],[136,4,"spike",true,11],[136,5,"block",false,11],[136,6,"block",false,11],[136,7,"orb",false,11],[136,8,"block",false,11],[137,0,"block",false],[137,4,"spike",true,11],[137,5,"block",false,11],[137,6,"block",false,11],[137,7,"block",false,11],[138,0,"block",false],[139,0,"block",false],[140,0,"block",false],[141,0,"spike",false],[142,0,"spike",false],[143,0,"spike",false],[144,0,"spike",false],[145,0,"spike",false],[146,0,"spike",false],[146,1,"orb",true],[147,0,"spike",false],[148,0,"spike",false],[149,0,"block",false],[149,1,"block",false],[150,0,"block",false],[150,1,"block",false],[151,0,"block",false],[151,1,"block",false],[151,9,"block",false],[152,0,"block",false],[152,1,"block",false],[152,9,"block",false],[153,0,"block",false],[153,1,"block",false],[153,2,"spike",false],[153,9,"block",false],[154,0,"block",false],[154,1,"block",false],[154,2,"spike",false],[154,8,"spike",true],[154,9,"block",false],[155,0,"block",false],[155,1,"block",false],[155,2,"spike",false],[155,8,"spike",true],[155,9,"block",false],[156,0,"block",false],[156,1,"block",false],[156,2,"spike",false],[156,7,"orb",true],[156,8,"spike",true],[156,9,"block",false],[157,0,"block",false],[157,1,"block",false],[157,8,"spike",true],[157,9,"block",false],[158,0,"block",false],[158,1,"block",false],[158,8,"spike",true],[158,9,"block",false],[159,0,"block",false],[159,1,"block",false],[159,9,"block",false],[160,9,"block",false],[170,8,"block",false],[170,9,"block",false],[171,8,"block",false],[171,9,"block",false],[180,0,"spike",false],[181,0,"spike",false],[182,0,"spike",false],[187,9,"spike",true],[188,9,"spike",true],[189,9,"spike",true],[190,9,"block",false],[200,0,"block",false],[200,1,"block",false],[200,2,"block",false],[200,3,"spike",false],[200,6,"spike",true],[200,7,"block",false],[200,8,"block",false],[200,9,"block",false],[201,0,"block",false],[201,1,"block",false],[201,2,"block",false],[201,3,"spike",false],[201,6,"spike",true],[201,7,"block",false],[201,8,"block",false],[201,9,"block",false],[202,0,"block",false],[202,1,"block",false],[202,2,"block",false],[202,3,"spike",false],[202,6,"spike",true],[202,7,"block",false],[202,8,"block",false],[202,9,"block",false],[203,0,"block",false],[203,1,"block",false],[203,2,"block",false],[203,3,"spike",false],[203,6,"spike",true],[203,7,"block",false],[203,8,"block",false],[203,9,"block",false],[208,9,"block",false],[209,9,"block",false],[210,9,"block",false],[214,3,"spike",true,11],[214,4,"block",false,11],[214,5,"block",false,11],[214,6,"block",false,11],[215,0,"spike",false],[215,3,"spike",true,11],[215,4,"block",false,11],[215,5,"block",false,11],[215,6,"orb",false,11],[215,7,"block",false,11],[216,0,"spike",false],[216,3,"spike",true,11],[216,4,"block",false,11],[216,5,"block",false,11],[216,6,"block",false,11],[216,7,"block",false,11],[217,0,"block",false],[217,3,"spike",true,11],[217,4,"block",false,11],[217,5,"block",false,11],[217,6,"orb",false,11],[217,7,"block",false,11],[218,3,"spike",true,11],[218,4,"block",false,11],[218,5,"block",false,11],[218,6,"block",false,11],[225,9,"spike",true],[226,9,"spike",true],[227,9,"block",false],[235,4,"block",false],[236,4,"block",false],[237,4,"block",false],[238,4,"block",false],[239,4,"block",false],[245,0,"block",false],[245,1,"spike",false],[245,8,"spike",true],[245,9,"block",false],[246,0,"block",false],[246,1,"spike",false],[246,8,"spike",true],[246,9,"block",false],[247,0,"block",false],[247,1,"spike",false],[247,8,"spike",true],[247,9,"block",false],[248,0,"block",false],[248,1,"spike",false],[248,8,"spike",true],[248,9,"block",false],[249,0,"block",false],[249,1,"block",false],[249,2,"block",false],[249,7,"block",false],[249,8,"block",false],[249,9,"block",false],[250,0,"block",false],[250,1,"block",false],[250,2,"block",false],[250,7,"block",false],[250,8,"block",false],[250,9,"block",false],[259,0,"spike",false],[260,0,"spike",false],[261,0,"spike",false],[262,0,"spike",false],[266,9,"block",false],[267,9,"block",false],[268,9,"block",false],[273,0,"block",false],[273,1,"block",false],[274,0,"block",false],[274,1,"block",false],[280,8,"block",false],[280,9,"block",false],[281,8,"block",false],[281,9,"block",false],[316,3,"spike",true,11],[316,4,"block",false,11],[316,5,"block",false,11],[316,6,"block",false,11],[317,3,"spike",true,11],[317,4,"block",false,11],[317,5,"block",false,11],[317,6,"orb",false,11],[317,7,"block",false,11],[318,3,"spike",true,11],[318,4,"block",false,11],[318,5,"block",false,11],[318,6,"block",false,11],[318,7,"block",false,11],[319,3,"spike",true,11],[319,4,"block",false,11],[319,5,"block",false,11],[319,6,"orb",false,11],[319,7,"block",false,11],[320,3,"spike",true,11],[320,4,"block",false,11],[320,5,"block",false,11],[320,6,"block",false,11],[341,0,"spike",false,12],[342,0,"block",false,12],[342,1,"spike",false,12],[342,9,"spike",true,12],[343,0,"block",false,12],[343,1,"block",false,12],[343,2,"spike",false,12],[343,8,"spike",true,12],[343,9,"block",false,12],[344,0,"block",false,12],[344,1,"block",false,12],[344,2,"block",false,12],[344,3,"spike",false,12],[344,7,"spike",true,12],[344,8,"block",false,12],[344,9,"block",false,12],[345,0,"block",false,12],[345,1,"block",false,12],[345,2,"block",false,12],[345,3,"block",false,12],[345,4,"spike",false,12],[345,6,"spike",true,12],[345,7,"block",false,12],[345,8,"block",false,12],[345,9,"block",false,12],[346,0,"block",false,12],[346,1,"block",false,12],[346,2,"block",false,12],[346,3,"spike",false,12],[346,7,"spike",true,12],[346,8,"block",false,12],[346,9,"block",false,12],[347,0,"block",false,12],[347,1,"block",false,12],[347,2,"spike",false,12],[347,8,"spike",true,12],[347,9,"block",false,12],[348,0,"block",false,12],[348,1,"spike",false,12],[348,9,"spike",true,12],[349,0,"spike",false,12],[349,8,"spike",true,12],[349,9,"block",false,12],[350,0,"block",false,12],[350,1,"spike",false,12],[350,7,"spike",true,12],[350,8,"block",false,12],[350,9,"block",false,12],[351,0,"block",false,12],[351,1,"block",false,12],[351,2,"spike",false,12],[351,6,"spike",true,12],[351,7,"block",false,12],[351,8,"block",false,12],[351,9,"block",false,12],[352,0,"block",false,12],[352,1,"block",false,12],[352,2,"block",false,12],[352,3,"spike",false,12],[352,5,"spike",true,12],[352,6,"block",false,12],[352,7,"block",false,12],[352,8,"block",false,12],[352,9,"block",false,12],[353,0,"block",false,12],[353,1,"block",false,12],[353,2,"spike",false,12],[353,6,"spike",true,12],[353,7,"block",false,12],[353,8,"block",false,12],[353,9,"block",false,12],[354,0,"block",false,12],[354,1,"spike",false,12],[354,7,"spike",true,12],[354,8,"block",false,12],[354,9,"block",false,12],[355,0,"spike",false,12],[355,8,"spike",true,12],[355,9,"block",false,12],[356,9,"spike",true,12],[363,4,"spike",true,11],[363,5,"block",false,11],[363,6,"block",false,11],[363,7,"block",false,11],[364,4,"spike",true,11],[364,5,"block",false,11],[364,6,"block",false,11],[364,7,"orb",false,11],[364,8,"block",false,11],[365,4,"spike",true,11],[365,5,"block",false,11],[365,6,"block",false,11],[365,7,"block",false,11],[365,8,"block",false,11],[366,4,"spike",true,11],[366,5,"block",false,11],[366,6,"block",false,11],[366,7,"orb",false,11],[366,8,"block",false,11],[367,4,"spike",true,11],[367,5,"block",false,11],[367,6,"block",false,11],[367,7,"block",false,11],[372,2,"spike",true,13],[372,3,"block",false,13],[372,4,"block",false,13],[372,5,"block",false,13],[372,6,"block",false,13],[372,7,"block",false,13],[372,8,"block",false,13],[372,9,"block",false,13],[373,2,"spike",true,13],[373,3,"block",false,13],[373,4,"block",false,13],[373,5,"block",false,13],[373,6,"block",false,13],[373,7,"block",false,13],[373,8,"block",false,13],[373,9,"block",false,13],[384,0,"block",false,14],[384,1,"block",false,14],[384,2,"block",false,14],[384,3,"block",false,14],[384,4,"block",false,14],[384,5,"block",false,14],[384,6,"block",false,14],[384,7,"spike",false,14],[385,0,"block",false,14],[385,1,"block",false,14],[385,2,"block",false,14],[385,3,"block",false,14],[385,4,"block",false,14],[385,5,"block",false,14],[385,6,"block",false,14],[385,7,"spike",false,14],[389,0,"block",false,15],[389,1,"spike",false,15],[389,5,"spike",true,15],[389,6,"block",false,15],[389,7,"block",false,15],[389,8,"block",false,15],[390,0,"block",false,15],[390,1,"spike",false,15],[390,5,"spike",true,15],[390,6,"block",false,15],[390,7,"block",false,15],[390,8,"orb",false,15],[390,9,"block",false,15],[391,0,"block",false,15],[391,1,"spike",false,15],[391,5,"spike",true,15],[391,6,"block",false,15],[391,7,"block",false,15],[391,8,"block",false,15],[391,9,"block",false,15],[392,0,"block",false,15],[392,1,"spike",false,15],[392,5,"spike",true,15],[392,6,"block",false,15],[392,7,"block",false,15],[392,8,"orb",false,15],[392,9,"block",false,15],[393,0,"block",false,15],[393,1,"spike",false,15],[393,5,"spike",true,15],[393,6,"block",false,15],[393,7,"block",false,15],[393,8,"block",false,15],[396,6,"block",false,16],[396,7,"spike",false,16],[397,6,"block",false,16],[397,7,"spike",false,16],[398,6,"block",false,16],[398,7,"spike",false,16],[399,6,"block",false,16],[399,7,"spike",false,16],[400,6,"block",false,16],[400,7,"spike",false,16],[403,0,"spike",false],[403,5,"spike",true,17],[403,6,"block",false,17],[403,7,"block",false,17],[403,8,"block",false,17],[404,0,"spike",false],[404,5,"spike",true,17],[404,6,"block",false,17],[404,7,"block",false,17],[404,8,"orb",false,17],[404,9,"block",false,17],[405,0,"spike",false],[405,5,"spike",true,17],[405,6,"block",false,17],[405,7,"block",false,17],[405,8,"block",false,17],[405,9,"block",false,17],[406,0,"spike",false],[406,5,"spike",true,17],[406,6,"block",false,17],[406,7,"block",false,17],[406,8,"orb",false,17],[406,9,"block",false,17],[407,0,"spike",false],[407,5,"spike",true,17],[407,6,"block",false,17],[407,7,"block",false,17],[407,8,"block",false,17],[411,0,"spike",false],[411,5,"spike",true,18],[411,6,"block",false,18],[411,7,"block",false,18],[411,8,"block",false,18],[412,0,"spike",false],[412,5,"spike",true,18],[412,6,"block",false,18],[412,7,"block",false,18],[412,8,"orb",false,18],[412,9,"block",false,18],[413,0,"spike",false],[413,5,"spike",true,18],[413,6,"block",false,18],[413,7,"block",false,18],[413,8,"block",false,18],[413,9,"block",false,18],[414,0,"spike",false],[414,5,"spike",true,18],[414,6,"block",false,18],[414,7,"block",false,18],[414,8,"orb",false,18],[414,9,"block",false,18],[415,0,"spike",false],[415,5,"spike",true,18],[415,6,"block",false,18],[415,7,"block",false,18],[415,8,"block",false,18],[419,0,"spike",false],[419,5,"spike",true,19],[419,6,"block",false,19],[419,7,"block",false,19],[419,8,"block",false,19],[420,0,"spike",false],[420,5,"spike",true,19],[420,6,"block",false,19],[420,7,"block",false,19],[420,8,"orb",false,19],[420,9,"block",false,19],[421,0,"spike",false],[421,5,"spike",true,19],[421,6,"block",false,19],[421,7,"block",false,19],[421,8,"block",false,19],[421,9,"block",false,19],[422,0,"spike",false],[422,5,"spike",true,19],[422,6,"block",false,19],[422,7,"block",false,19],[422,8,"orb",false,19],[422,9,"block",false,19],[423,0,"spike",false],[423,5,"spike",true,19],[423,6,"block",false,19],[423,7,"block",false,19],[423,8,"block",false,19],[437,4,"spike",true,11],[437,5,"block",false,11],[437,6,"block",false,11],[437,7,"block",false,11],[438,4,"spike",true,11],[438,5,"block",false,11],[438,6,"block",false,11],[438,7,"orb",false,11],[438,8,"block",false,11],[439,4,"spike",true,11],[439,5,"block",false,11],[439,6,"block",false,11],[439,7,"block",false,11],[439,8,"block",false,11],[440,4,"spike",true,11],[440,5,"block",false,11],[440,6,"block",false,11],[440,7,"orb",false,11],[440,8,"block",false,11],[441,4,"spike",true,11],[441,5,"block",false,11],[441,6,"block",false,11],[441,7,"block",false,11],[442,0,"spike",false],[443,0,"spike",false],[446,0,"spike",false],[447,0,"spike",false]],"gravs":[[28,true],[151,true],[160,false],[192,true]],"portals":[[47,"ship"],[77,"spider"],[123,"cube"],[191,"ship"],[230,"ship"],[251,"cube"],[303,"wave"],[358,"ship"],[425,"cube"]],"speeds":[[17,1.5],[77,1.0],[123,1.5],[142,1.5],[228,1.5],[303,1.0],[424,0.8]],"background":[[442,3,"block",false,20],[442,4,"block",false,20],[442,5,"block",false,20],[442,6,"block",false,20],[442,7,"block",false,20],[443,3,"block",false,20],[443,7,"block",false,20],[444,3,"block",false,20],[444,5,"block",false,20],[444,7,"block",false,20],[445,3,"block",false,20],[445,4,"block",false,20],[445,5,"block",false,20],[445,7,"block",false,20],[447,3,"block",false,20],[447,4,"block",false,20],[447,5,"block",false,20],[447,6,"block",false,20],[447,7,"block",false,20],[448,3,"block",false,20],[448,7,"block",false,20],[449,3,"block",false,20],[449,5,"block",false,20],[449,7,"block",false,20],[450,3,"block",false,20],[450,4,"block",false,20],[450,5,"block",false,20],[450,7,"block",false,20]],"texts":[[38,6,"I See You!",11],[114,6,"There is no escape!",11],[133,9,"You\'re Stuck in here with me.",11],[216,8,"That\'s It",11],[316,8,"You\'re Not Leaving Alive",11],[363,9,"What? How did you Survive?",11],[437,9,"I give up. You win, for now.",11]],"triggers":[[8,3,{"type":"move","group":1,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[9,3,{"type":"move","group":2,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[10,3,{"type":"move","group":3,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[11,3,{"type":"move","group":4,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[12,3,{"type":"move","group":5,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[13,3,{"type":"move","group":6,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[14,3,{"type":"move","group":7,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[15,3,{"type":"move","group":8,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[16,3,{"type":"move","group":9,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[17,3,{"type":"move","group":10,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[36,4,{"type":"reveal","group":11,"show":true}],[44,5,{"type":"reveal","group":11,"show":false}],[111,4,{"type":"reveal","group":11,"show":true}],[119,4,{"type":"reveal","group":11,"show":false}],[131,7,{"type":"reveal","group":11,"show":true}],[139,8,{"type":"reveal","group":11,"show":false}],[212,6,{"type":"reveal","group":11,"show":true}],[220,7,{"type":"reveal","group":11,"show":false}],[304,2,{"type":"reveal","group":12,"show":false}],[314,6,{"type":"reveal","group":11,"show":true}],[322,7,{"type":"reveal","group":11,"show":false}],[331,3,{"type":"reveal","group":12,"show":true}],[353,4,{"type":"reveal","group":13,"show":false}],[353,5,{"type":"reveal","group":14,"show":false}],[361,7,{"type":"reveal","group":11,"show":true}],[369,8,{"type":"reveal","group":11,"show":false}],[370,2,{"type":"reveal","group":13,"show":true}],[373,0,{"type":"move","group":13,"dx":0.0,"dy":-2.5,"time":0.3,"ease":true}],[379,5,{"type":"move","group":15,"dx":0.0,"dy":6.0,"time":2.0,"ease":true}],[381,4,{"type":"reveal","group":14,"show":true}],[385,9,{"type":"move","group":14,"dx":0.0,"dy":2.5,"time":0.2,"ease":true}],[391,3,{"type":"move","group":16,"dx":0.0,"dy":-6.0,"time":2.0,"ease":true}],[404,1,{"type":"move","group":17,"dx":0.0,"dy":-7.0,"time":1.0,"ease":true}],[408,2,{"type":"move","group":17,"dx":0.0,"dy":7.0,"time":3.0,"ease":true}],[413,1,{"type":"move","group":18,"dx":0.0,"dy":-7.0,"time":1.0,"ease":true}],[417,2,{"type":"move","group":18,"dx":0.0,"dy":7.0,"time":3.0,"ease":true}],[421,1,{"type":"move","group":19,"dx":0.0,"dy":-7.0,"time":1.0,"ease":true}],[425,2,{"type":"move","group":19,"dx":0.0,"dy":7.0,"time":3.0,"ease":true}],[426,3,{"type":"reveal","group":20,"show":false}],[430,7,{"type":"reveal","group":11,"show":true}],[435,4,{"type":"move","group":11,"dx":0.0,"dy":8.0,"time":2.5,"ease":true}],[439,2,{"type":"reveal","group":20,"show":true}]]}')


def build_velocity_battle(lv):
    LevelData.from_json(VELOCITY_BATTLE).build(lv)


VELOCITY_FINISH = json.loads('{"name":"Velocity Finish","author":"AugmentedMagic","description":"","start_mode":"cube","finish":null,"cells":[[6,0,"block",false,1],[7,0,"block",false,2],[8,0,"spike",false,3],[9,0,"spike",false,4],[10,0,"spike",false,5],[11,0,"block",false,6],[12,0,"block",false,7],[13,0,"spike",false,8],[14,0,"spike",false,9],[15,0,"block",false,10],[20,9,"block",false],[21,9,"block",false],[22,9,"block",false],[23,8,"spike",true],[23,9,"block",false],[24,8,"spike",true],[24,9,"block",false],[25,8,"spike",true],[25,9,"block",false],[26,9,"block",false],[27,9,"block",false],[28,9,"block",false],[29,9,"block",false],[30,9,"block",false],[31,9,"block",false],[32,9,"block",false],[33,0,"spike",false],[33,9,"block",false],[34,0,"spike",false],[34,9,"block",false],[35,0,"spike",false],[35,9,"block",false],[36,0,"block",false],[36,9,"block",false],[37,9,"block",false],[38,1,"spike",true,11],[38,2,"block",false,11],[38,3,"block",false,11],[38,4,"block",false,11],[38,9,"block",false],[39,1,"spike",true,11],[39,2,"block",false,11],[39,3,"block",false,11],[39,4,"orb",false,11],[39,5,"block",false,11],[39,9,"block",false],[40,1,"spike",true,11],[40,2,"block",false,11],[40,3,"block",false,11],[40,4,"block",false,11],[40,5,"block",false,11],[40,9,"spike",true],[41,1,"spike",true,11],[41,2,"block",false,11],[41,3,"block",false,11],[41,4,"orb",false,11],[41,5,"block",false,11],[41,9,"spike",true],[42,1,"spike",true,11],[42,2,"block",false,11],[42,3,"block",false,11],[42,4,"block",false,11],[42,9,"spike",true],[43,9,"spike",true],[44,9,"block",false],[45,9,"block",false],[47,0,"spike",false],[47,9,"spike",true],[48,0,"spike",false],[48,9,"spike",true],[49,0,"spike",false],[49,9,"spike",true],[50,0,"spike",false],[50,9,"spike",true],[51,0,"spike",false],[51,9,"spike",true],[52,0,"spike",false],[52,9,"spike",true],[53,0,"spike",false],[53,9,"spike",true],[54,0,"spike",false],[54,9,"spike",true],[58,4,"block",false],[58,5,"block",false],[59,3,"block",false],[59,4,"block",false],[59,5,"block",false],[59,6,"block",false],[60,2,"block",false],[60,3,"block",false],[60,4,"block",false],[60,5,"block",false],[60,6,"block",false],[60,7,"block",false],[61,1,"block",false],[61,2,"block",false],[61,3,"block",false],[61,4,"block",false],[61,5,"block",false],[61,6,"block",false],[61,7,"block",false],[61,8,"block",false],[62,1,"block",false],[62,2,"block",false],[62,3,"block",false],[62,4,"block",false],[62,5,"block",false],[62,6,"block",false],[62,7,"block",false],[62,8,"block",false],[63,2,"block",false],[63,3,"block",false],[63,4,"block",false],[63,5,"block",false],[63,6,"block",false],[63,7,"block",false],[64,3,"block",false],[64,4,"block",false],[64,5,"block",false],[64,6,"block",false],[65,4,"block",false],[65,5,"block",false],[70,9,"block",false],[71,9,"block",false],[72,9,"block",false],[73,8,"spike",true],[73,9,"block",false],[74,8,"spike",true],[74,9,"block",false],[75,8,"spike",true],[75,9,"block",false],[76,9,"block",false],[77,7,"block",false],[77,8,"block",false],[77,9,"block",false],[78,7,"block",false],[78,8,"block",false],[78,9,"block",false],[79,7,"block",false],[79,8,"block",false],[79,9,"block",false],[80,0,"block",false],[80,1,"block",false],[80,2,"block",false],[80,3,"spike",false],[80,7,"block",false],[80,8,"block",false],[80,9,"block",false],[81,0,"block",false],[81,1,"block",false],[81,2,"block",false],[81,3,"spike",false],[81,7,"block",false],[81,8,"block",false],[81,9,"block",false],[82,0,"block",false],[82,1,"block",false],[82,2,"block",false],[82,7,"block",false],[82,8,"block",false],[82,9,"block",false],[83,0,"block",false],[83,1,"block",false],[83,2,"block",false],[83,7,"block",false],[83,8,"block",false],[83,9,"block",false],[84,0,"block",false],[84,1,"orb",false],[84,2,"block",false],[84,6,"spike",true],[84,7,"block",false],[84,8,"block",false],[84,9,"block",false],[85,0,"block",false],[85,1,"block",false],[85,2,"block",false],[85,6,"spike",true],[85,7,"block",false],[85,8,"block",false],[85,9,"block",false],[86,0,"block",false],[86,1,"block",false],[86,2,"block",false],[86,9,"block",false],[87,0,"block",false],[87,1,"orb",false],[87,2,"block",false],[87,9,"block",false],[88,0,"block",false],[88,1,"block",false],[88,2,"block",false],[88,9,"block",false],[89,0,"block",false],[89,1,"block",false],[89,2,"block",false],[89,3,"block",false],[89,4,"block",false],[89,5,"block",false],[89,9,"block",false],[90,9,"block",false],[91,9,"block",false],[92,1,"block",false],[92,2,"block",false],[92,3,"block",false],[92,4,"block",false],[92,5,"block",false],[92,6,"block",false],[92,7,"block",false],[92,8,"block",false],[92,9,"block",false],[93,9,"spike",true],[95,0,"spike",false],[96,0,"spike",false],[97,0,"spike",false],[100,1,"block",false],[100,2,"block",false],[100,3,"block",false],[100,4,"block",false],[100,5,"block",false],[100,6,"block",false],[100,7,"block",false],[100,8,"block",false],[100,9,"block",false],[103,0,"block",false],[103,1,"block",false],[103,2,"block",false],[103,3,"block",false],[103,4,"block",false],[103,5,"block",false],[103,6,"block",false],[103,7,"block",false],[103,8,"block",false],[106,1,"block",false],[106,2,"block",false],[106,3,"block",false],[106,4,"block",false],[106,5,"block",false],[106,6,"block",false],[106,7,"block",false],[106,8,"block",false],[106,9,"block",false],[107,9,"block",false],[108,9,"block",false],[109,9,"block",false],[110,0,"block",false],[110,1,"block",false],[110,2,"block",false],[110,3,"block",false],[110,4,"block",false],[110,5,"block",false],[110,6,"block",false],[110,7,"block",false],[110,9,"block",false],[111,7,"block",false],[111,9,"block",false],[112,9,"block",false],[113,1,"spike",true,11],[113,2,"block",false,11],[113,3,"block",false,11],[113,4,"block",false,11],[113,7,"block",false],[113,9,"block",false],[114,1,"spike",true,11],[114,2,"block",false,11],[114,3,"block",false,11],[114,4,"orb",false,11],[114,5,"block",false,11],[114,7,"block",false],[115,1,"spike",true,11],[115,2,"block",false,11],[115,3,"block",false,11],[115,4,"block",false,11],[115,5,"block",false,11],[115,7,"block",false],[115,9,"block",false],[116,1,"spike",true,11],[116,2,"block",false,11],[116,3,"block",false,11],[116,4,"orb",false,11],[116,5,"block",false,11],[116,9,"block",false],[117,1,"spike",true,11],[117,2,"block",false,11],[117,3,"block",false,11],[117,4,"block",false,11],[117,7,"block",false],[117,9,"block",false],[118,7,"block",false],[119,7,"block",false],[119,9,"block",false],[120,9,"block",false],[121,7,"block",false],[121,9,"block",false],[122,0,"coin",false],[122,7,"block",false],[123,0,"pad",false],[125,0,"block",false],[126,0,"block",false],[127,0,"block",false],[128,0,"block",false],[129,0,"block",false],[130,0,"block",false],[131,0,"block",false],[132,0,"spike",false],[133,0,"spike",false],[133,4,"spike",true,11],[133,5,"block",false,11],[133,6,"block",false,11],[133,7,"block",false,11],[134,0,"spike",false],[134,4,"spike",true,11],[134,5,"block",false,11],[134,6,"block",false,11],[134,7,"orb",false,11],[134,8,"block",false,11],[135,0,"spike",false],[135,4,"spike",true,11],[135,5,"block",false,11],[135,6,"block",false,11],[135,7,"block",false,11],[135,8,"block",false,11],[136,0,"spike",false],[136,4,"spike",true,11],[136,5,"block",false,11],[136,6,"block",false,11],[136,7,"orb",false,11],[136,8,"block",false,11],[137,0,"block",false],[137,4,"spike",true,11],[137,5,"block",false,11],[137,6,"block",false,11],[137,7,"block",false,11],[138,0,"block",false],[139,0,"block",false],[140,0,"block",false],[141,0,"spike",false],[142,0,"spike",false],[143,0,"spike",false],[144,0,"spike",false],[145,0,"spike",false],[146,0,"spike",false],[146,1,"orb",true],[147,0,"spike",false],[148,0,"spike",false],[149,0,"block",false],[149,1,"block",false],[150,0,"block",false],[150,1,"block",false],[151,0,"block",false],[151,1,"block",false],[151,9,"block",false],[152,0,"block",false],[152,1,"block",false],[152,9,"block",false],[153,0,"block",false],[153,1,"block",false],[153,2,"spike",false],[153,9,"block",false],[154,0,"block",false],[154,1,"block",false],[154,2,"spike",false],[154,8,"spike",true],[154,9,"block",false],[155,0,"block",false],[155,1,"block",false],[155,2,"spike",false],[155,8,"spike",true],[155,9,"block",false],[156,0,"block",false],[156,1,"block",false],[156,2,"spike",false],[156,7,"orb",true],[156,8,"spike",true],[156,9,"block",false],[157,0,"block",false],[157,1,"block",false],[157,8,"spike",true],[157,9,"block",false],[158,0,"block",false],[158,1,"block",false],[158,8,"spike",true],[158,9,"block",false],[159,0,"block",false],[159,1,"block",false],[159,9,"block",false],[160,9,"block",false],[170,8,"block",false],[170,9,"block",false],[171,8,"block",false],[171,9,"block",false],[180,0,"spike",false],[181,0,"spike",false],[182,0,"spike",false],[187,9,"spike",true],[188,9,"spike",true],[189,9,"spike",true],[190,9,"block",false],[200,0,"block",false],[200,1,"block",false],[200,2,"block",false],[200,3,"spike",false],[200,6,"spike",true],[200,7,"block",false],[200,8,"block",false],[200,9,"block",false],[201,0,"block",false],[201,1,"block",false],[201,2,"block",false],[201,3,"spike",false],[201,6,"spike",true],[201,7,"block",false],[201,8,"block",false],[201,9,"block",false],[202,0,"block",false],[202,1,"block",false],[202,2,"block",false],[202,3,"spike",false],[202,6,"spike",true],[202,7,"block",false],[202,8,"block",false],[202,9,"block",false],[203,0,"block",false],[203,1,"block",false],[203,2,"block",false],[203,3,"spike",false],[203,6,"spike",true],[203,7,"block",false],[203,8,"block",false],[203,9,"block",false],[208,9,"block",false],[209,9,"block",false],[210,9,"block",false],[214,3,"spike",true,11],[214,4,"block",false,11],[214,5,"block",false,11],[214,6,"block",false,11],[215,0,"spike",false],[215,3,"spike",true,11],[215,4,"block",false,11],[215,5,"block",false,11],[215,6,"orb",false,11],[215,7,"block",false,11],[216,0,"spike",false],[216,3,"spike",true,11],[216,4,"block",false,11],[216,5,"block",false,11],[216,6,"block",false,11],[216,7,"block",false,11],[217,0,"block",false],[217,3,"spike",true,11],[217,4,"block",false,11],[217,5,"block",false,11],[217,6,"orb",false,11],[217,7,"block",false,11],[218,3,"spike",true,11],[218,4,"block",false,11],[218,5,"block",false,11],[218,6,"block",false,11],[225,9,"spike",true],[226,9,"spike",true],[227,9,"block",false],[235,4,"block",false],[236,4,"block",false],[237,4,"block",false],[238,4,"block",false],[239,4,"block",false],[245,0,"block",false],[245,1,"spike",false],[245,8,"spike",true],[245,9,"block",false],[246,0,"block",false],[246,1,"spike",false],[246,8,"spike",true],[246,9,"block",false],[247,0,"block",false],[247,1,"spike",false],[247,8,"spike",true],[247,9,"block",false],[248,0,"block",false],[248,1,"spike",false],[248,8,"spike",true],[248,9,"block",false],[249,0,"block",false],[249,1,"block",false],[249,2,"block",false],[249,7,"block",false],[249,8,"block",false],[249,9,"block",false],[250,0,"block",false],[250,1,"block",false],[250,2,"block",false],[250,7,"block",false],[250,8,"block",false],[250,9,"block",false],[259,0,"spike",false],[260,0,"spike",false],[261,0,"spike",false],[262,0,"spike",false],[266,9,"block",false],[267,9,"block",false],[268,9,"block",false],[273,0,"block",false],[273,1,"block",false],[274,0,"block",false],[274,1,"block",false],[280,8,"block",false],[280,9,"block",false],[281,8,"block",false],[281,9,"block",false],[316,3,"spike",true,11],[316,4,"block",false,11],[316,5,"block",false,11],[316,6,"block",false,11],[317,3,"spike",true,11],[317,4,"block",false,11],[317,5,"block",false,11],[317,6,"orb",false,11],[317,7,"block",false,11],[318,3,"spike",true,11],[318,4,"block",false,11],[318,5,"block",false,11],[318,6,"block",false,11],[318,7,"block",false,11],[319,3,"spike",true,11],[319,4,"block",false,11],[319,5,"block",false,11],[319,6,"orb",false,11],[319,7,"block",false,11],[320,3,"spike",true,11],[320,4,"block",false,11],[320,5,"block",false,11],[320,6,"block",false,11],[341,0,"spike",false,12],[342,0,"block",false,12],[342,1,"spike",false,12],[342,9,"spike",true,12],[343,0,"block",false,12],[343,1,"block",false,12],[343,2,"spike",false,12],[343,8,"spike",true,12],[343,9,"block",false,12],[344,0,"block",false,12],[344,1,"block",false,12],[344,2,"block",false,12],[344,3,"spike",false,12],[344,7,"spike",true,12],[344,8,"block",false,12],[344,9,"block",false,12],[345,0,"block",false,12],[345,1,"block",false,12],[345,2,"block",false,12],[345,3,"block",false,12],[345,4,"spike",false,12],[345,6,"spike",true,12],[345,7,"block",false,12],[345,8,"block",false,12],[345,9,"block",false,12],[346,0,"block",false,12],[346,1,"block",false,12],[346,2,"block",false,12],[346,3,"spike",false,12],[346,7,"spike",true,12],[346,8,"block",false,12],[346,9,"block",false,12],[347,0,"block",false,12],[347,1,"block",false,12],[347,2,"spike",false,12],[347,8,"spike",true,12],[347,9,"block",false,12],[348,0,"block",false,12],[348,1,"spike",false,12],[348,9,"spike",true,12],[349,0,"spike",false,12],[349,8,"spike",true,12],[349,9,"block",false,12],[350,0,"block",false,12],[350,1,"spike",false,12],[350,7,"spike",true,12],[350,8,"block",false,12],[350,9,"block",false,12],[351,0,"block",false,12],[351,1,"block",false,12],[351,2,"spike",false,12],[351,6,"spike",true,12],[351,7,"block",false,12],[351,8,"block",false,12],[351,9,"block",false,12],[352,0,"block",false,12],[352,1,"block",false,12],[352,2,"block",false,12],[352,3,"spike",false,12],[352,5,"spike",true,12],[352,6,"block",false,12],[352,7,"block",false,12],[352,8,"block",false,12],[352,9,"block",false,12],[353,0,"block",false,12],[353,1,"block",false,12],[353,2,"spike",false,12],[353,6,"spike",true,12],[353,7,"block",false,12],[353,8,"block",false,12],[353,9,"block",false,12],[354,0,"block",false,12],[354,1,"spike",false,12],[354,7,"spike",true,12],[354,8,"block",false,12],[354,9,"block",false,12],[355,0,"spike",false,12],[355,8,"spike",true,12],[355,9,"block",false,12],[356,9,"spike",true,12],[363,4,"spike",true,11],[363,5,"block",false,11],[363,6,"block",false,11],[363,7,"block",false,11],[364,4,"spike",true,11],[364,5,"block",false,11],[364,6,"block",false,11],[364,7,"orb",false,11],[364,8,"block",false,11],[365,4,"spike",true,11],[365,5,"block",false,11],[365,6,"block",false,11],[365,7,"block",false,11],[365,8,"block",false,11],[366,4,"spike",true,11],[366,5,"block",false,11],[366,6,"block",false,11],[366,7,"orb",false,11],[366,8,"block",false,11],[367,4,"spike",true,11],[367,5,"block",false,11],[367,6,"block",false,11],[367,7,"block",false,11],[372,2,"spike",true,13],[372,3,"block",false,13],[372,4,"block",false,13],[372,5,"block",false,13],[372,6,"block",false,13],[372,7,"block",false,13],[372,8,"block",false,13],[372,9,"block",false,13],[373,2,"spike",true,13],[373,3,"block",false,13],[373,4,"block",false,13],[373,5,"block",false,13],[373,6,"block",false,13],[373,7,"block",false,13],[373,8,"block",false,13],[373,9,"block",false,13],[384,0,"block",false,14],[384,1,"block",false,14],[384,2,"block",false,14],[384,3,"block",false,14],[384,4,"block",false,14],[384,5,"block",false,14],[384,6,"block",false,14],[384,7,"spike",false,14],[385,0,"block",false,14],[385,1,"block",false,14],[385,2,"block",false,14],[385,3,"block",false,14],[385,4,"block",false,14],[385,5,"block",false,14],[385,6,"block",false,14],[385,7,"spike",false,14],[389,0,"block",false,15],[389,1,"spike",false,15],[389,5,"spike",true,15],[389,6,"block",false,15],[389,7,"block",false,15],[389,8,"block",false,15],[390,0,"block",false,15],[390,1,"spike",false,15],[390,5,"spike",true,15],[390,6,"block",false,15],[390,7,"block",false,15],[390,8,"orb",false,15],[390,9,"block",false,15],[391,0,"block",false,15],[391,1,"spike",false,15],[391,5,"spike",true,15],[391,6,"block",false,15],[391,7,"block",false,15],[391,8,"block",false,15],[391,9,"block",false,15],[392,0,"block",false,15],[392,1,"spike",false,15],[392,5,"spike",true,15],[392,6,"block",false,15],[392,7,"block",false,15],[392,8,"orb",false,15],[392,9,"block",false,15],[393,0,"block",false,15],[393,1,"spike",false,15],[393,5,"spike",true,15],[393,6,"block",false,15],[393,7,"block",false,15],[393,8,"block",false,15],[396,6,"block",false,16],[396,7,"spike",false,16],[397,6,"block",false,16],[397,7,"spike",false,16],[398,6,"block",false,16],[398,7,"spike",false,16],[399,6,"block",false,16],[399,7,"spike",false,16],[400,6,"block",false,16],[400,7,"spike",false,16],[403,0,"spike",false],[403,5,"spike",true,17],[403,6,"block",false,17],[403,7,"block",false,17],[403,8,"block",false,17],[404,0,"spike",false],[404,5,"spike",true,17],[404,6,"block",false,17],[404,7,"block",false,17],[404,8,"orb",false,17],[404,9,"block",false,17],[405,0,"spike",false],[405,5,"spike",true,17],[405,6,"block",false,17],[405,7,"block",false,17],[405,8,"block",false,17],[405,9,"block",false,17],[406,0,"spike",false],[406,5,"spike",true,17],[406,6,"block",false,17],[406,7,"block",false,17],[406,8,"orb",false,17],[406,9,"block",false,17],[407,0,"spike",false],[407,5,"spike",true,17],[407,6,"block",false,17],[407,7,"block",false,17],[407,8,"block",false,17],[411,0,"spike",false],[411,5,"spike",true,18],[411,6,"block",false,18],[411,7,"block",false,18],[411,8,"block",false,18],[412,0,"spike",false],[412,5,"spike",true,18],[412,6,"block",false,18],[412,7,"block",false,18],[412,8,"orb",false,18],[412,9,"block",false,18],[413,0,"spike",false],[413,5,"spike",true,18],[413,6,"block",false,18],[413,7,"block",false,18],[413,8,"block",false,18],[413,9,"block",false,18],[414,0,"spike",false],[414,5,"spike",true,18],[414,6,"block",false,18],[414,7,"block",false,18],[414,8,"orb",false,18],[414,9,"block",false,18],[415,0,"spike",false],[415,5,"spike",true,18],[415,6,"block",false,18],[415,7,"block",false,18],[415,8,"block",false,18],[419,0,"spike",false],[419,5,"spike",true,19],[419,6,"block",false,19],[419,7,"block",false,19],[419,8,"block",false,19],[420,0,"spike",false],[420,5,"spike",true,19],[420,6,"block",false,19],[420,7,"block",false,19],[420,8,"orb",false,19],[420,9,"block",false,19],[421,0,"spike",false],[421,5,"spike",true,19],[421,6,"block",false,19],[421,7,"block",false,19],[421,8,"block",false,19],[421,9,"block",false,19],[422,0,"spike",false],[422,5,"spike",true,19],[422,6,"block",false,19],[422,7,"block",false,19],[422,8,"orb",false,19],[422,9,"block",false,19],[423,0,"spike",false],[423,5,"spike",true,19],[423,6,"block",false,19],[423,7,"block",false,19],[423,8,"block",false,19],[437,4,"spike",true,12],[437,5,"block",false,12],[437,6,"block",false,12],[437,7,"block",false,12],[438,4,"spike",true,12],[438,5,"block",false,12],[438,6,"block",false,12],[438,7,"orb",false,12],[438,8,"block",false,12],[439,4,"spike",true,12],[439,5,"block",false,12],[439,6,"block",false,12],[439,7,"block",false,12],[439,8,"block",false,12],[440,4,"spike",true,12],[440,5,"block",false,12],[440,6,"block",false,12],[440,7,"orb",false,12],[440,8,"block",false,12],[441,4,"spike",true,12],[441,5,"block",false,12],[441,6,"block",false,12],[441,7,"block",false,12],[457,0,"ramp_br",false,11],[457,3,"ramp_tl",false,11],[457,4,"block",false,11],[457,5,"block",false,11],[457,6,"block",false,11],[457,7,"block",false,11],[457,8,"block",false,11],[457,9,"block",false,11],[458,0,"block",false,11],[458,1,"ramp_br",false,11],[458,4,"ramp_tl",false,11],[458,5,"block",false,11],[458,6,"block",false,11],[458,7,"block",false,11],[458,8,"block",false,11],[458,9,"block",false,11],[459,0,"block",false,11],[459,1,"block",false,11],[459,2,"ramp_br",false,11],[459,5,"ramp_tl",false,11],[459,6,"block",false,11],[459,7,"block",false,11],[459,8,"block",false,11],[459,9,"block",false,11],[460,0,"block",false,11],[460,1,"block",false,11],[460,2,"block",false,11],[460,3,"ramp_br",false,11],[460,6,"ramp_tl",false,11],[460,7,"block",false,11],[460,8,"block",false,11],[460,9,"block",false,11],[461,0,"block",false,11],[461,1,"block",false,11],[461,2,"block",false,11],[461,3,"block",false,11],[461,4,"ramp_br",false,11],[461,7,"ramp_tl",false,11],[461,8,"block",false,11],[461,9,"block",false,11],[462,0,"block",false,11],[462,1,"block",false,11],[462,2,"block",false,11],[462,3,"block",false,11],[462,4,"block",false,11],[462,5,"ramp_br",false,11],[462,8,"ramp_tl",false,11],[462,9,"block",false,11],[463,0,"block",false,11],[463,1,"block",false,11],[463,2,"block",false,11],[463,3,"block",false,11],[463,4,"block",false,11],[463,5,"block",false,11],[463,6,"ramp_br",false,11],[463,9,"ramp_tl",false,11],[464,0,"block",false,11],[464,1,"block",false,11],[464,2,"block",false,11],[464,3,"block",false,11],[464,4,"block",false,11],[464,5,"block",false,11],[464,6,"ramp_bl",false,11],[464,9,"ramp_tr",false,11],[465,0,"block",false,11],[465,1,"block",false,11],[465,2,"block",false,11],[465,3,"block",false,11],[465,4,"block",false,11],[465,5,"ramp_bl",false,11],[465,8,"ramp_tr",false,11],[465,9,"block",false,11],[466,0,"block",false,11],[466,1,"block",false,11],[466,2,"block",false,11],[466,3,"block",false,11],[466,4,"ramp_bl",false,11],[466,7,"ramp_tr",false,11],[466,8,"block",false,11],[466,9,"block",false,11],[467,0,"block",false,11],[467,1,"block",false,11],[467,2,"block",false,11],[467,3,"ramp_bl",false,11],[467,6,"ramp_tr",false,11],[467,7,"block",false,11],[467,8,"block",false,11],[467,9,"block",false,11],[468,0,"block",false,11],[468,1,"block",false,11],[468,2,"ramp_bl",false,11],[468,5,"ramp_tr",false,11],[468,6,"block",false,11],[468,7,"block",false,11],[468,8,"block",false,11],[468,9,"block",false,11],[469,0,"block",false,11],[469,1,"ramp_bl",false,11],[469,4,"ramp_tr",false,11],[469,5,"block",false,11],[469,6,"block",false,11],[469,7,"block",false,11],[469,8,"block",false,11],[469,9,"block",false,11],[470,0,"ramp_bl",false,11],[470,3,"ramp_tr",false,11],[470,4,"block",false,11],[470,5,"block",false,11],[470,6,"block",false,11],[470,7,"block",false,11],[470,8,"block",false,11],[470,9,"block",false,11],[471,0,"ramp_br",false,11],[471,3,"ramp_tl",false,11],[471,4,"block",false,11],[471,5,"block",false,11],[471,6,"block",false,11],[471,7,"block",false,11],[471,8,"block",false,11],[471,9,"block",false,11],[472,0,"block",false,11],[472,1,"ramp_br",false,11],[472,4,"ramp_tl",false,11],[472,5,"block",false,11],[472,6,"block",false,11],[472,7,"block",false,11],[472,8,"block",false,11],[472,9,"block",false,11],[473,0,"block",false,11],[473,1,"block",false,11],[473,2,"ramp_br",false,11],[473,5,"ramp_tl",false,11],[473,6,"block",false,11],[473,7,"block",false,11],[473,8,"block",false,11],[473,9,"block",false,11],[474,0,"block",false,11],[474,1,"block",false,11],[474,2,"block",false,11],[474,3,"ramp_br",false,11],[474,6,"ramp_tl",false,11],[474,7,"block",false,11],[474,8,"block",false,11],[474,9,"block",false,11],[475,0,"block",false,11],[475,1,"block",false,11],[475,2,"block",false,11],[475,3,"block",false,11],[475,4,"ramp_br",false,11],[475,7,"ramp_tl",false,11],[475,8,"block",false,11],[475,9,"block",false,11],[476,0,"block",false,11],[476,1,"block",false,11],[476,2,"block",false,11],[476,3,"block",false,11],[476,4,"block",false,11],[476,5,"ramp_br",false,11],[476,8,"ramp_tl",false,11],[476,9,"block",false,11],[477,0,"block",false,11],[477,1,"block",false,11],[477,2,"block",false,11],[477,3,"block",false,11],[477,4,"block",false,11],[477,5,"block",false,11],[477,6,"ramp_br",false,11],[477,9,"ramp_tl",false,11],[478,0,"block",false,11],[478,1,"block",false,11],[478,2,"block",false,11],[478,3,"block",false,11],[478,4,"block",false,11],[478,5,"block",false,11],[478,6,"ramp_bl",false,11],[478,9,"ramp_tr",false,11],[479,0,"block",false,11],[479,1,"block",false,11],[479,2,"block",false,11],[479,3,"block",false,11],[479,4,"block",false,11],[479,5,"ramp_bl",false,11],[479,8,"ramp_tr",false,11],[479,9,"block",false,11],[480,0,"block",false,11],[480,1,"block",false,11],[480,2,"block",false,11],[480,3,"block",false,11],[480,4,"ramp_bl",false,11],[480,7,"ramp_tr",false,11],[480,8,"block",false,11],[480,9,"block",false,11],[481,0,"block",false,11],[481,1,"block",false,11],[481,2,"block",false,11],[481,3,"ramp_bl",false,11],[481,6,"ramp_tr",false,11],[481,7,"block",false,11],[481,8,"block",false,11],[481,9,"block",false,11],[482,0,"block",false,11],[482,1,"block",false,11],[482,2,"ramp_bl",false,11],[482,5,"ramp_tr",false,11],[482,6,"block",false,11],[482,7,"block",false,11],[482,8,"block",false,11],[482,9,"block",false,11],[483,0,"block",false,11],[483,1,"ramp_bl",false,11],[483,4,"ramp_tr",false,11],[483,5,"block",false,11],[483,6,"block",false,11],[483,7,"block",false,11],[483,8,"block",false,11],[483,9,"block",false,11],[484,0,"ramp_bl",false,11],[484,3,"ramp_tr",false,11],[484,4,"block",false,11],[484,5,"block",false,11],[484,6,"block",false,11],[484,7,"block",false,11],[484,8,"block",false,11],[484,9,"block",false,11],[485,0,"ramp_br",false,11],[485,3,"ramp_tl",false,11],[485,4,"block",false,11],[485,5,"block",false,11],[485,6,"block",false,11],[485,7,"block",false,11],[485,8,"block",false,11],[485,9,"block",false,11],[486,0,"block",false,11],[486,1,"ramp_br",false,11],[486,4,"ramp_tl",false,11],[486,5,"block",false,11],[486,6,"block",false,11],[486,7,"block",false,11],[486,8,"block",false,11],[486,9,"block",false,11],[487,0,"block",false,11],[487,1,"block",false,11],[487,2,"ramp_br",false,11],[487,5,"ramp_tl",false,11],[487,6,"block",false,11],[487,7,"block",false,11],[487,8,"block",false,11],[487,9,"block",false,11],[488,0,"block",false,11],[488,1,"block",false,11],[488,2,"block",false,11],[488,3,"ramp_br",false,11],[488,6,"ramp_tl",false,11],[488,7,"block",false,11],[488,8,"block",false,11],[488,9,"block",false,11],[489,0,"block",false,11],[489,1,"block",false,11],[489,2,"block",false,11],[489,3,"block",false,11],[489,4,"ramp_br",false,11],[489,7,"ramp_tl",false,11],[489,8,"block",false,11],[489,9,"block",false,11],[490,0,"block",false,11],[490,1,"block",false,11],[490,2,"block",false,11],[490,3,"block",false,11],[490,4,"block",false,11],[490,5,"ramp_br",false,11],[490,8,"ramp_tl",false,11],[490,9,"block",false,11],[491,0,"block",false,11],[491,1,"block",false,11],[491,2,"block",false,11],[491,3,"block",false,11],[491,4,"block",false,11],[491,5,"block",false,11],[491,6,"ramp_br",false,11],[491,9,"ramp_tl",false,11],[492,0,"block",false,11],[492,1,"block",false,11],[492,2,"block",false,11],[492,3,"block",false,11],[492,4,"block",false,11],[492,5,"block",false,11],[492,6,"ramp_bl",false,11],[492,9,"ramp_tr",false,11],[493,0,"block",false,11],[493,1,"block",false,11],[493,2,"block",false,11],[493,3,"block",false,11],[493,4,"block",false,11],[493,5,"ramp_bl",false,11],[493,8,"ramp_tr",false,11],[493,9,"block",false,11],[494,0,"block",false,11],[494,1,"block",false,11],[494,2,"block",false,11],[494,3,"block",false,11],[494,4,"ramp_bl",false,11],[494,7,"ramp_tr",false,11],[494,8,"block",false,11],[494,9,"block",false,11],[495,0,"block",false,11],[495,1,"block",false,11],[495,2,"block",false,11],[495,3,"ramp_bl",false,11],[495,6,"ramp_tr",false,11],[495,7,"block",false,11],[495,8,"block",false,11],[495,9,"block",false,11],[496,0,"block",false,11],[496,1,"block",false,11],[496,2,"ramp_bl",false,11],[496,5,"ramp_tr",false,11],[496,6,"block",false,11],[496,7,"block",false,11],[496,8,"block",false,11],[496,9,"block",false,11],[497,0,"block",false,11],[497,1,"ramp_bl",false,11],[497,4,"ramp_tr",false,11],[497,5,"block",false,11],[497,6,"block",false,11],[497,7,"block",false,11],[497,8,"block",false,11],[497,9,"block",false,11],[498,0,"ramp_bl",false,11],[498,3,"ramp_tr",false,11],[498,4,"block",false,11],[498,5,"block",false,11],[498,6,"block",false,11],[498,7,"block",false,11],[498,8,"block",false,11],[498,9,"block",false,11],[505,4,"spike",true,13],[505,5,"block",false,13],[505,6,"block",false,13],[505,7,"block",false,13],[506,4,"spike",true,13],[506,5,"block",false,13],[506,6,"block",false,13],[506,7,"orb",false,13],[506,8,"block",false,13],[507,4,"spike",true,13],[507,5,"block",false,13],[507,6,"block",false,13],[507,7,"block",false,13],[507,8,"block",false,13],[508,4,"spike",true,13],[508,5,"block",false,13],[508,6,"block",false,13],[508,7,"orb",false,13],[508,8,"block",false,13],[509,4,"spike",true,13],[509,5,"block",false,13],[509,6,"block",false,13],[509,7,"block",false,13],[580,0,"ramp_br",false,0,2],[581,0,"block",false,0,2],[581,1,"ramp_br",false,0,2],[582,0,"block",false,0,2],[582,1,"block",false,0,2],[582,2,"ramp_br",false,0,2],[583,0,"block",false,0,2],[583,1,"block",false,0,2],[583,2,"block",false,0,2],[583,3,"ramp_br",false,0,2],[584,0,"block",false,0,2],[584,1,"block",false,0,2],[584,2,"block",false,0,2],[584,3,"block",false,0,2],[584,4,"ramp_br",false,0,2],[585,0,"block",false,0,2],[585,1,"block",false,0,2],[585,2,"block",false,0,2],[585,3,"block",false,0,2],[585,4,"block",false,0,2],[585,5,"ramp_br",false,0,2],[586,0,"block",false,0,1],[586,1,"block",false,0,1],[586,2,"block",false,0,1],[586,3,"block",false,0,1],[586,4,"block",false,0,1],[586,5,"block",false,0,2],[586,6,"ramp_br",false,0,2],[587,0,"block",false,0,1],[587,1,"block",false,0,2],[587,2,"block",false,0,2],[587,3,"block",false,0,2],[587,4,"block",false,0,1],[587,5,"block",false,0,2],[587,6,"block",false,0,2],[587,7,"ramp_br",false,0,2],[588,0,"block",false,0,1],[588,1,"block",false,0,1],[588,2,"block",false,0,1],[588,3,"block",false,0,2],[588,4,"block",false,0,1],[588,5,"block",false,0,2],[588,6,"block",false,0,2],[588,7,"ramp_bl",false,0,2],[589,0,"block",false,0,2],[589,1,"block",false,0,2],[589,2,"block",false,0,2],[589,3,"block",false,0,2],[589,4,"block",false,0,2],[589,5,"block",false,0,2],[589,6,"ramp_bl",false,0,2],[589,9,"ramp_tr",false,0,2],[590,0,"block",false,0,2],[590,1,"block",false,0,2],[590,2,"block",false,0,2],[590,3,"block",false,0,2],[590,4,"block",false,0,2],[590,5,"ramp_bl",false,0,2],[590,8,"ramp_tr",false,0,2],[590,9,"block",false,0,2],[591,0,"block",false,0,2],[591,1,"block",false,0,2],[591,2,"block",false,0,2],[591,3,"block",false,0,2],[591,4,"ramp_bl",false,0,2],[591,7,"ramp_tr",false,0,2],[591,8,"block",false,0,2],[591,9,"block",false,0,2],[592,0,"block",false,0,2],[592,1,"block",false,0,2],[592,2,"block",false,0,2],[592,3,"ramp_bl",false,0,2],[592,6,"ramp_tr",false,0,2],[592,7,"block",false,0,2],[592,8,"block",false,0,2],[592,9,"block",false,0,2],[593,0,"block",false,0,2],[593,1,"block",false,0,2],[593,2,"ramp_bl",false,0,2],[593,5,"ramp_tr",false,0,2],[593,6,"block",false,0,2],[593,7,"block",false,0,2],[593,8,"block",false,0,2],[593,9,"block",false,0,2],[594,0,"block",false,0,2],[594,1,"ramp_bl",false,0,2],[594,4,"ramp_tr",false,0,2],[594,5,"block",false,0,2],[594,6,"block",false,0,2],[594,7,"block",false,0,2],[594,8,"block",false,0,2],[594,9,"block",false,0,2],[595,0,"ramp_bl",false,0,2],[595,3,"ramp_tr",false,0,2],[595,4,"block",false,0,2],[595,5,"block",false,0,1],[595,6,"block",false,0,2],[595,7,"block",false,0,2],[595,8,"block",false,0,2],[595,9,"block",false,0,1],[596,2,"ramp_tr",false,0,2],[596,3,"block",false,0,2],[596,4,"block",false,0,2],[596,5,"block",false,0,1],[596,6,"block",false,0,1],[596,7,"block",false,0,1],[596,8,"block",false,0,1],[596,9,"block",false,0,1],[597,2,"ramp_tl",false,0,2],[597,3,"block",false,0,2],[597,4,"block",false,0,2],[597,5,"block",false,0,1],[597,6,"block",false,0,2],[597,7,"block",false,0,2],[597,8,"block",false,0,2],[597,9,"block",false,0,1],[598,0,"ramp_br",false,0,2],[598,3,"ramp_tl",false,0,2],[598,4,"block",false,0,2],[598,5,"block",false,0,2],[598,6,"block",false,0,2],[598,7,"block",false,0,2],[598,8,"block",false,0,2],[598,9,"block",false,0,2],[599,0,"block",false,0,2],[599,1,"ramp_br",false,0,2],[599,4,"ramp_tl",false,0,2],[599,5,"block",false,0,2],[599,6,"block",false,0,2],[599,7,"block",false,0,2],[599,8,"block",false,0,2],[599,9,"block",false,0,2],[600,0,"block",false,0,2],[600,1,"block",false,0,2],[600,2,"ramp_br",false,0,2],[600,5,"ramp_tl",false,0,2],[600,6,"block",false,0,2],[600,7,"block",false,0,2],[600,8,"block",false,0,2],[600,9,"block",false,0,2],[601,0,"block",false,0,2],[601,1,"block",false,0,2],[601,2,"block",false,0,2],[601,3,"ramp_br",false,0,2],[601,6,"ramp_tl",false,0,2],[601,7,"block",false,0,2],[601,8,"block",false,0,2],[601,9,"block",false,0,2],[602,0,"block",false,0,2],[602,1,"block",false,0,2],[602,2,"block",false,0,2],[602,3,"block",false,0,2],[602,4,"ramp_br",false,0,2],[602,7,"ramp_tl",false,0,2],[602,8,"block",false,0,2],[602,9,"block",false,0,2],[603,0,"block",false,0,2],[603,1,"block",false,0,2],[603,2,"block",false,0,2],[603,3,"block",false,0,2],[603,4,"block",false,0,2],[603,5,"ramp_br",false,0,2],[603,8,"ramp_tl",false,0,2],[603,9,"block",false,0,2],[604,0,"block",false,0,2],[604,1,"block",false,0,1],[604,2,"block",false,0,1],[604,3,"block",false,0,1],[604,4,"block",false,0,1],[604,5,"block",false,0,2],[604,6,"ramp_br",false,0,2],[604,9,"ramp_tl",false,0,2],[605,0,"block",false,0,1],[605,1,"block",false,0,1],[605,2,"block",false,0,1],[605,3,"block",false,0,2],[605,4,"block",false,0,2],[605,5,"block",false,0,2],[605,6,"block",false,0,2],[605,7,"ramp_br",false,0,2],[606,0,"block",false,0,2],[606,1,"block",false,0,1],[606,2,"block",false,0,1],[606,3,"block",false,0,1],[606,4,"block",false,0,1],[606,5,"block",false,0,2],[606,6,"block",false,0,2],[606,7,"ramp_bl",false,0,2],[607,0,"block",false,0,2],[607,1,"block",false,0,2],[607,2,"block",false,0,2],[607,3,"block",false,0,2],[607,4,"block",false,0,2],[607,5,"block",false,0,2],[607,6,"ramp_bl",false,0,2],[607,9,"ramp_tr",false,0,2],[608,0,"block",false,0,2],[608,1,"block",false,0,2],[608,2,"block",false,0,2],[608,3,"block",false,0,2],[608,4,"block",false,0,2],[608,5,"ramp_bl",false,0,2],[608,8,"ramp_tr",false,0,2],[608,9,"block",false,0,2],[609,0,"block",false,0,2],[609,1,"block",false,0,2],[609,2,"block",false,0,2],[609,3,"block",false,0,2],[609,4,"ramp_bl",false,0,2],[609,7,"ramp_tr",false,0,2],[609,8,"block",false,0,2],[609,9,"block",false,0,2],[610,0,"block",false,0,2],[610,1,"block",false,0,2],[610,2,"block",false,0,2],[610,3,"ramp_bl",false,0,2],[610,6,"ramp_tr",false,0,2],[610,7,"block",false,0,2],[610,8,"block",false,0,2],[610,9,"block",false,0,2],[611,0,"block",false,0,2],[611,1,"block",false,0,2],[611,2,"ramp_bl",false,0,2],[611,5,"ramp_tr",false,0,2],[611,6,"block",false,0,2],[611,7,"block",false,0,2],[611,8,"block",false,0,2],[611,9,"block",false,0,2],[612,0,"block",false,0,2],[612,1,"ramp_bl",false,0,2],[612,4,"ramp_tr",false,0,2],[612,5,"block",false,0,2],[612,6,"block",false,0,2],[612,7,"block",false,0,2],[612,8,"block",false,0,2],[612,9,"block",false,0,2],[613,0,"ramp_bl",false,0,2],[613,3,"ramp_tr",false,0,2],[613,4,"block",false,0,1],[613,5,"block",false,0,1],[613,6,"block",false,0,1],[613,7,"block",false,0,1],[613,8,"block",false,0,1],[613,9,"block",false,0,2],[614,2,"ramp_tr",false,0,2],[614,3,"block",false,0,2],[614,4,"block",false,0,1],[614,5,"block",false,0,2],[614,6,"block",false,0,1],[614,7,"block",false,0,2],[614,8,"block",false,0,1],[614,9,"block",false,0,2],[615,2,"ramp_tl",false,0,2],[615,3,"block",false,0,2],[615,4,"block",false,0,1],[615,5,"block",false,0,2],[615,6,"block",false,0,2],[615,7,"block",false,0,2],[615,8,"block",false,0,1],[615,9,"block",false,0,2],[616,0,"ramp_br",false,0,2],[616,3,"ramp_tl",false,0,2],[616,4,"block",false,0,2],[616,5,"block",false,0,2],[616,6,"block",false,0,2],[616,7,"block",false,0,2],[616,8,"block",false,0,2],[616,9,"block",false,0,2],[617,0,"block",false,0,2],[617,1,"ramp_br",false,0,2],[617,4,"ramp_tl",false,0,2],[617,5,"block",false,0,2],[617,6,"block",false,0,2],[617,7,"block",false,0,2],[617,8,"block",false,0,2],[617,9,"block",false,0,2],[618,0,"block",false,0,2],[618,1,"block",false,0,2],[618,2,"ramp_br",false,0,2],[618,5,"ramp_tl",false,0,2],[618,6,"block",false,0,2],[618,7,"block",false,0,2],[618,8,"block",false,0,2],[618,9,"block",false,0,2],[619,0,"block",false,0,2],[619,1,"block",false,0,2],[619,2,"block",false,0,2],[619,3,"ramp_br",false,0,2],[619,6,"ramp_tl",false,0,2],[619,7,"block",false,0,2],[619,8,"block",false,0,2],[619,9,"block",false,0,2],[620,0,"block",false,0,2],[620,1,"block",false,0,2],[620,2,"block",false,0,2],[620,3,"block",false,0,2],[620,4,"ramp_br",false,0,2],[620,7,"ramp_tl",false,0,2],[620,8,"block",false,0,2],[620,9,"block",false,0,2],[621,0,"block",false,0,2],[621,1,"block",false,0,2],[621,2,"block",false,0,2],[621,3,"block",false,0,2],[621,4,"block",false,0,2],[621,5,"ramp_br",false,0,2],[621,8,"ramp_tl",false,0,2],[621,9,"block",false,0,2],[622,0,"block",false,0,1],[622,1,"block",false,0,1],[622,2,"block",false,0,1],[622,3,"block",false,0,1],[622,4,"block",false,0,1],[622,5,"block",false,0,2],[622,6,"ramp_br",false,0,2],[622,9,"ramp_tl",false,0,2],[623,0,"block",false,0,1],[623,1,"block",false,0,2],[623,2,"block",false,0,2],[623,3,"block",false,0,2],[623,4,"block",false,0,2],[623,5,"block",false,0,2],[623,6,"block",false,0,2],[623,7,"ramp_br",false,0,2],[624,0,"block",false,0,1],[624,1,"block",false,0,1],[624,2,"block",false,0,1],[624,3,"block",false,0,1],[624,4,"block",false,0,1],[624,5,"block",false,0,2],[624,6,"block",false,0,2],[624,7,"ramp_bl",false,0,2],[625,0,"block",false,0,2],[625,1,"block",false,0,2],[625,2,"block",false,0,2],[625,3,"block",false,0,2],[625,4,"block",false,0,2],[625,5,"block",false,0,2],[625,6,"ramp_bl",false,0,2],[625,9,"ramp_tr",false,0,2],[626,0,"block",false,0,2],[626,1,"block",false,0,2],[626,2,"block",false,0,2],[626,3,"block",false,0,2],[626,4,"block",false,0,2],[626,5,"ramp_bl",false,0,2],[626,8,"ramp_tr",false,0,2],[626,9,"block",false,0,2],[627,0,"block",false,0,2],[627,1,"block",false,0,2],[627,2,"block",false,0,2],[627,3,"block",false,0,2],[627,4,"ramp_bl",false,0,2],[627,7,"ramp_tr",false,0,2],[627,8,"block",false,0,2],[627,9,"block",false,0,2],[628,0,"block",false,0,2],[628,1,"block",false,0,2],[628,2,"block",false,0,2],[628,3,"ramp_bl",false,0,2],[628,6,"ramp_tr",false,0,2],[628,7,"block",false,0,2],[628,8,"block",false,0,2],[628,9,"block",false,0,2],[629,0,"block",false,0,2],[629,1,"block",false,0,2],[629,2,"ramp_bl",false,0,2],[629,5,"ramp_tr",false,0,2],[629,6,"block",false,0,2],[629,7,"block",false,0,2],[629,8,"block",false,0,2],[629,9,"block",false,0,2],[630,0,"block",false,0,2],[630,1,"ramp_bl",false,0,2],[630,4,"ramp_tr",false,0,2],[630,5,"block",false,0,2],[630,6,"block",false,0,2],[630,7,"block",false,0,2],[630,8,"block",false,0,2],[630,9,"block",false,0,2],[631,0,"ramp_bl",false,0,2],[631,3,"ramp_tr",false,0,2],[631,4,"block",false,0,1],[631,5,"block",false,0,1],[631,6,"block",false,0,1],[631,7,"block",false,0,1],[631,8,"block",false,0,1],[631,9,"block",false,0,2],[632,2,"ramp_tr",false,0,2],[632,3,"block",false,0,2],[632,4,"block",false,0,2],[632,5,"block",false,0,2],[632,6,"block",false,0,1],[632,7,"block",false,0,2],[632,8,"block",false,0,1],[632,9,"block",false,0,2],[633,2,"ramp_tl",false,0,2],[633,3,"block",false,0,2],[633,4,"block",false,0,2],[633,5,"block",false,0,2],[633,6,"block",false,0,1],[633,7,"block",false,0,1],[633,8,"block",false,0,1],[633,9,"block",false,0,2],[634,0,"ramp_br",false,0,2],[634,3,"ramp_tl",false,0,2],[634,4,"block",false,0,2],[634,5,"block",false,0,2],[634,6,"block",false,0,2],[634,7,"block",false,0,2],[634,8,"block",false,0,2],[634,9,"block",false,0,2],[635,0,"block",false,0,2],[635,1,"ramp_br",false,0,2],[635,4,"ramp_tl",false,0,2],[635,5,"block",false,0,2],[635,6,"block",false,0,2],[635,7,"block",false,0,2],[635,8,"block",false,0,2],[635,9,"block",false,0,2],[636,0,"block",false,0,2],[636,1,"block",false,0,2],[636,2,"ramp_br",false,0,2],[636,5,"ramp_tl",false,0,2],[636,6,"block",false,0,2],[636,7,"block",false,0,2],[636,8,"block",false,0,2],[636,9,"block",false,0,2],[637,0,"block",false,0,2],[637,1,"block",false,0,2],[637,2,"ramp_bl",false,0,2],[637,5,"ramp_tr",false,0,2],[637,6,"block",false,0,2],[637,7,"block",false,0,2],[637,8,"block",false,0,2],[637,9,"block",false,0,2],[638,0,"block",false,0,2],[638,1,"ramp_bl",false,0,2],[638,4,"ramp_tr",false,0,2],[638,5,"block",false,0,2],[638,6,"block",false,0,2],[638,7,"block",false,0,2],[638,8,"block",false,0,2],[638,9,"block",false,0,2],[639,0,"ramp_bl",false,0,2],[639,3,"ramp_tr",false,0,2],[639,4,"block",false,0,2],[639,5,"block",false,0,2],[639,6,"block",false,0,2],[639,7,"block",false,0,2],[639,8,"block",false,0,2],[639,9,"block",false,0,2],[640,2,"ramp_tr",false,0,2],[640,3,"block",false,0,2],[640,4,"block",false,0,2],[640,5,"block",false,0,2],[640,6,"block",false,0,2],[640,7,"block",false,0,2],[640,8,"block",false,0,2],[640,9,"block",false,0,2],[641,2,"ramp_tl",false,0,2],[641,3,"block",false,0,2],[641,4,"block",false,0,2],[641,5,"block",false,0,2],[641,6,"block",false,0,2],[641,7,"block",false,0,2],[641,8,"block",false,0,2],[641,9,"block",false,0,2],[642,0,"ramp_br",false,0,2],[642,3,"ramp_tl",false,0,2],[642,4,"block",false,0,2],[642,5,"block",false,0,2],[642,6,"block",false,0,2],[642,7,"block",false,0,2],[642,8,"block",false,0,2],[642,9,"block",false,0,2],[643,0,"block",false,0,2],[643,1,"ramp_br",false,0,2],[643,4,"ramp_tl",false,0,2],[643,5,"block",false,0,2],[643,6,"block",false,0,2],[643,7,"block",false,0,2],[643,8,"block",false,0,2],[643,9,"block",false,0,2],[644,0,"block",false,0,2],[644,1,"block",false,0,2],[644,2,"ramp_br",false,0,2],[644,5,"ramp_tl",false,0,2],[644,6,"block",false,0,2],[644,7,"block",false,0,2],[644,8,"block",false,0,2],[644,9,"block",false,0,2],[645,0,"block",false,0,2],[645,1,"block",false,0,2],[645,2,"ramp_bl",false,0,2],[645,5,"ramp_tr",false,0,2],[645,6,"block",false,0,2],[645,7,"block",false,0,2],[645,8,"block",false,0,2],[645,9,"block",false,0,2],[646,0,"block",false,0,2],[646,1,"ramp_bl",false,0,2],[646,4,"ramp_tr",false,0,2],[646,5,"block",false,0,2],[646,6,"block",false,0,2],[646,7,"block",false,0,2],[646,8,"block",false,0,2],[646,9,"block",false,0,2],[647,0,"ramp_bl",false,0,2],[647,3,"ramp_tr",false,0,2],[647,4,"block",false,0,2],[647,5,"block",false,0,2],[647,6,"block",false,0,2],[647,7,"block",false,0,2],[647,8,"block",false,0,2],[647,9,"block",false,0,2],[648,2,"ramp_tr",false,0,2],[648,3,"block",false,0,2],[648,4,"block",false,0,2],[648,5,"block",false,0,2],[648,6,"block",false,0,2],[648,7,"block",false,0,2],[648,8,"block",false,0,2],[648,9,"block",false,0,2],[649,2,"ramp_tl",false,0,2],[649,3,"block",false,0,2],[649,4,"block",false,0,2],[649,5,"block",false,0,2],[649,6,"block",false,0,2],[649,7,"block",false,0,2],[649,8,"block",false,0,2],[649,9,"block",false,0,2],[650,0,"ramp_br",false,0,2],[650,3,"ramp_tl",false,0,2],[650,4,"block",false,0,2],[650,5,"block",false,0,2],[650,6,"block",false,0,2],[650,7,"block",false,0,2],[650,8,"block",false,0,2],[650,9,"block",false,0,2],[651,0,"block",false,0,2],[651,1,"ramp_br",false,0,2],[651,4,"ramp_tl",false,0,2],[651,5,"block",false,0,2],[651,6,"block",false,0,2],[651,7,"block",false,0,2],[651,8,"block",false,0,2],[651,9,"block",false,0,2],[652,0,"block",false,0,2],[652,1,"block",false,0,2],[652,2,"ramp_br",false,0,2],[652,5,"ramp_tl",false,0,2],[652,6,"block",false,0,2],[652,7,"block",false,0,2],[652,8,"block",false,0,2],[652,9,"block",false,0,2],[653,0,"block",false,0,2],[653,1,"block",false,0,2],[653,2,"ramp_bl",false,0,2],[653,5,"ramp_tr",false,0,2],[653,6,"block",false,0,2],[653,7,"block",false,0,2],[653,8,"block",false,0,2],[653,9,"block",false,0,2],[654,0,"block",false,0,2],[654,1,"ramp_bl",false,0,2],[654,4,"ramp_tr",false,0,2],[654,5,"block",false,0,2],[654,6,"block",false,0,2],[654,7,"block",false,0,2],[654,8,"block",false,0,2],[654,9,"block",false,0,2],[655,0,"ramp_bl",false,0,2],[655,3,"ramp_tr",false,0,2],[655,4,"block",false,0,2],[655,5,"block",false,0,2],[655,6,"block",false,0,2],[655,7,"block",false,0,2],[655,8,"block",false,0,2],[655,9,"block",false,0,2],[656,2,"ramp_tr",false,0,2],[656,3,"block",false,0,2],[656,4,"block",false,0,2],[656,5,"block",false,0,2],[656,6,"block",false,0,2],[656,7,"block",false,0,2],[656,8,"block",false,0,2],[656,9,"block",false,0,2],[657,2,"ramp_tl",false,0,2],[657,3,"block",false,0,2],[657,4,"block",false,0,2],[657,5,"block",false,0,2],[657,6,"block",false,0,2],[657,7,"block",false,0,2],[657,8,"block",false,0,2],[657,9,"block",false,0,2],[658,0,"ramp_br",false,0,2],[658,3,"ramp_tl",false,0,2],[658,4,"block",false,0,2],[658,5,"block",false,0,2],[658,6,"block",false,0,2],[658,7,"block",false,0,2],[658,8,"block",false,0,2],[658,9,"block",false,0,2],[659,0,"block",false,0,2],[659,1,"ramp_br",false,0,2],[659,4,"ramp_tl",false,0,2],[659,5,"block",false,0,2],[659,6,"block",false,0,2],[659,7,"block",false,0,2],[659,8,"block",false,0,2],[659,9,"block",false,0,2],[660,0,"block",false,0,2],[660,1,"block",false,0,2],[660,2,"ramp_br",false,0,2],[660,5,"ramp_tl",false,0,2],[660,6,"block",false,0,2],[660,7,"block",false,0,2],[660,8,"block",false,0,2],[660,9,"block",false,0,2],[661,0,"block",false,0,2],[661,1,"block",false,0,2],[661,2,"block",false,0,2],[661,3,"ramp_br",false,0,2],[661,6,"ramp_tl",false,0,2],[661,7,"block",false,0,2],[661,8,"block",false,0,2],[661,9,"block",false,0,2],[662,0,"block",false,0,2],[662,1,"block",false,0,2],[662,2,"block",false,0,2],[662,3,"block",false,0,2],[662,4,"ramp_br",false,0,2],[662,7,"ramp_tl",false,0,2],[662,8,"block",false,0,2],[662,9,"block",false,0,2],[663,0,"block",false,0,2],[663,1,"block",false,0,2],[663,2,"block",false,0,2],[663,3,"block",false,0,2],[663,4,"block",false,0,2],[663,5,"ramp_br",false,0,2],[663,8,"ramp_tl",false,0,2],[663,9,"block",false,0,2],[664,0,"block",false,0,2],[664,1,"block",false,0,2],[664,2,"block",false,0,2],[664,3,"block",false,0,2],[664,4,"block",false,0,2],[664,5,"block",false,0,2],[664,6,"ramp_br",false,0,2],[664,9,"ramp_tl",false,0,2],[665,0,"block",false,0,2],[665,1,"block",false,0,2],[665,2,"block",false,0,2],[665,3,"block",false,0,2],[665,4,"block",false,0,2],[665,5,"block",false,0,2],[665,6,"block",false,0,2],[665,7,"ramp_br",false,0,2],[666,0,"block",false,0,2],[666,1,"block",false,0,2],[666,2,"block",false,0,2],[666,3,"block",false,0,2],[666,4,"block",false,0,2],[666,5,"block",false,0,2],[666,6,"block",false,0,2],[666,7,"ramp_bl",false,0,2],[667,0,"block",false,0,2],[667,1,"block",false,0,2],[667,2,"block",false,0,2],[667,3,"block",false,0,2],[667,4,"block",false,0,2],[667,5,"block",false,0,2],[667,6,"ramp_bl",false,0,2],[667,9,"ramp_tr",false,0,2],[668,0,"block",false,0,2],[668,1,"block",false,0,2],[668,2,"block",false,0,2],[668,3,"block",false,0,2],[668,4,"block",false,0,2],[668,5,"ramp_bl",false,0,2],[668,8,"ramp_tr",false,0,2],[668,9,"block",false,0,2],[669,0,"block",false,0,2],[669,1,"block",false,0,2],[669,2,"block",false,0,2],[669,3,"block",false,0,2],[669,4,"block",false,0,2],[669,5,"ramp_br",false,0,2],[669,8,"ramp_tl",false,0,2],[669,9,"block",false,0,2],[670,0,"block",false,0,2],[670,1,"block",false,0,2],[670,2,"block",false,0,2],[670,3,"block",false,0,2],[670,4,"block",false,0,2],[670,5,"block",false,0,2],[670,6,"ramp_br",false,0,2],[670,9,"ramp_tl",false,0,2],[671,0,"block",false,0,2],[671,1,"block",false,0,2],[671,2,"block",false,0,2],[671,3,"block",false,0,2],[671,4,"block",false,0,2],[671,5,"block",false,0,2],[671,6,"block",false,0,2],[671,7,"ramp_br",false,0,2],[672,0,"block",false,0,2],[672,1,"block",false,0,2],[672,2,"block",false,0,2],[672,3,"block",false,0,2],[672,4,"block",false,0,2],[672,5,"block",false,0,2],[672,6,"block",false,0,2],[672,7,"ramp_bl",false,0,2],[673,0,"block",false,0,2],[673,1,"block",false,0,2],[673,2,"block",false,0,2],[673,3,"block",false,0,2],[673,4,"block",false,0,2],[673,5,"block",false,0,2],[673,6,"ramp_bl",false,0,2],[673,9,"ramp_tr",false,0,2],[674,0,"block",false,0,2],[674,1,"block",false,0,2],[674,2,"block",false,0,2],[674,3,"block",false,0,2],[674,4,"block",false,0,2],[674,5,"ramp_bl",false,0,2],[674,8,"ramp_tr",false,0,2],[674,9,"block",false,0,2],[675,0,"block",false,0,2],[675,1,"block",false,0,2],[675,2,"block",false,0,2],[675,3,"block",false,0,2],[675,4,"block",false,0,2],[675,5,"ramp_br",false,0,2],[675,8,"ramp_tl",false,0,2],[675,9,"block",false,0,2],[676,0,"block",false,0,2],[676,1,"block",false,0,2],[676,2,"block",false,0,2],[676,3,"block",false,0,2],[676,4,"block",false,0,2],[676,5,"block",false,0,2],[676,6,"ramp_br",false,0,2],[676,9,"ramp_tl",false,0,2],[677,0,"block",false,0,2],[677,1,"block",false,0,2],[677,2,"block",false,0,2],[677,3,"block",false,0,2],[677,4,"block",false,0,2],[677,5,"block",false,0,2],[677,6,"block",false,0,2],[677,7,"ramp_br",false,0,2],[678,0,"block",false,0,2],[678,1,"block",false,0,2],[678,2,"block",false,0,2],[678,3,"block",false,0,2],[678,4,"block",false,0,2],[678,5,"block",false,0,2],[678,6,"block",false,0,2],[678,7,"ramp_bl",false,0,2],[679,0,"block",false,0,2],[679,1,"block",false,0,2],[679,2,"block",false,0,2],[679,3,"block",false,0,2],[679,4,"block",false,0,2],[679,5,"block",false,0,2],[679,6,"ramp_bl",false,0,2],[679,9,"ramp_tr",false,0,2],[680,0,"block",false,0,2],[680,1,"block",false,0,2],[680,2,"block",false,0,2],[680,3,"block",false,0,2],[680,4,"block",false,0,2],[680,5,"ramp_bl",false,0,2],[680,8,"ramp_tr",false,0,2],[680,9,"block",false,0,2],[681,0,"block",false,0,2],[681,1,"block",false,0,2],[681,2,"block",false,0,2],[681,3,"block",false,0,2],[681,4,"block",false,0,2],[681,5,"ramp_br",false,0,2],[681,8,"ramp_tl",false,0,2],[681,9,"block",false,0,2],[682,0,"block",false,0,2],[682,1,"block",false,0,2],[682,2,"block",false,0,2],[682,3,"block",false,0,2],[682,4,"block",false,0,2],[682,5,"block",false,0,2],[682,6,"ramp_br",false,0,2],[682,9,"ramp_tl",false,0,2],[683,0,"block",false,0,2],[683,1,"block",false,0,2],[683,2,"block",false,0,2],[683,3,"block",false,0,2],[683,4,"block",false,0,2],[683,5,"block",false,0,2],[683,6,"block",false,0,2],[683,7,"ramp_br",false,0,2],[684,0,"block",false,0,2],[684,1,"block",false,0,2],[684,2,"block",false,0,2],[684,3,"block",false,0,2],[684,4,"block",false,0,2],[684,5,"block",false,0,2],[684,6,"block",false,0,2],[684,7,"ramp_bl",false,0,2],[685,0,"block",false,0,2],[685,1,"block",false,0,2],[685,2,"block",false,0,2],[685,3,"block",false,0,2],[685,4,"block",false,0,2],[685,5,"block",false,0,2],[685,6,"ramp_bl",false,0,2],[685,9,"ramp_tr",false,0,2],[686,0,"block",false,0,2],[686,1,"block",false,0,2],[686,2,"block",false,0,2],[686,3,"block",false,0,2],[686,4,"block",false,0,2],[686,5,"ramp_bl",false,0,2],[686,8,"ramp_tr",false,0,2],[686,9,"block",false,0,2],[687,0,"block",false,0,2],[687,1,"block",false,0,2],[687,2,"block",false,0,2],[687,3,"block",false,0,2],[687,4,"ramp_bl",false,0,2],[687,7,"ramp_tr",false,0,2],[687,8,"block",false,0,2],[687,9,"block",false,0,2],[688,0,"block",false,0,2],[688,1,"block",false,0,2],[688,2,"block",false,0,2],[688,3,"ramp_bl",false,0,2],[688,6,"ramp_tr",false,0,2],[688,7,"block",false,0,2],[688,8,"block",false,0,2],[688,9,"block",false,0,2],[689,0,"block",false,0,2],[689,1,"block",false,0,2],[689,2,"ramp_bl",false,0,2],[689,5,"ramp_tr",false,0,2],[689,6,"block",false,0,2],[689,7,"block",false,0,2],[689,8,"block",false,0,2],[689,9,"block",false,0,2],[690,0,"block",false,0,2],[690,1,"ramp_bl",false,0,2],[690,4,"ramp_tr",false,0,2],[690,5,"block",false,0,2],[690,6,"block",false,0,2],[690,7,"block",false,0,2],[690,8,"block",false,0,2],[690,9,"block",false,0,2],[691,0,"ramp_bl",false,0,2],[691,3,"ramp_tr",false,0,2],[691,4,"block",false,0,2],[691,5,"block",false,0,2],[691,6,"block",false,0,2],[691,7,"block",false,0,2],[691,8,"block",false,0,2],[691,9,"block",false,0,2],[692,2,"ramp_tr",false,0,2],[692,3,"block",false,0,2],[692,4,"block",false,0,2],[692,5,"block",false,0,2],[692,6,"block",false,0,2],[692,7,"block",false,0,2],[692,8,"block",false,0,2],[692,9,"block",false,0,2],[693,2,"ramp_tl",false,0,2],[693,3,"block",false,0,2],[693,4,"block",false,0,2],[693,5,"block",false,0,2],[693,6,"block",false,0,2],[693,7,"block",false,0,2],[693,8,"block",false,0,2],[693,9,"block",false,0,2],[694,0,"ramp_br",false,0,2],[694,3,"ramp_tl",false,0,2],[694,4,"block",false,0,2],[694,5,"block",false,0,2],[694,6,"block",false,0,2],[694,7,"block",false,0,2],[694,8,"block",false,0,2],[694,9,"block",false,0,2],[695,0,"block",false,0,2],[695,1,"ramp_br",false,0,2],[695,4,"ramp_tl",false,0,2],[695,5,"block",false,0,2],[695,6,"block",false,0,2],[695,7,"block",false,0,2],[695,8,"block",false,0,2],[695,9,"block",false,0,2],[696,0,"block",false,0,2],[696,1,"block",false,0,2],[696,2,"ramp_br",false,0,2],[696,5,"ramp_tl",false,0,2],[696,6,"block",false,0,2],[696,7,"block",false,0,2],[696,8,"block",false,0,2],[696,9,"block",false,0,2],[697,0,"block",false,0,2],[697,1,"block",false,0,2],[697,2,"ramp_bl",false,0,2],[697,5,"ramp_tr",false,0,2],[697,6,"block",false,0,2],[697,7,"block",false,0,2],[697,8,"block",false,0,2],[697,9,"block",false,0,2],[698,0,"block",false,0,2],[698,1,"ramp_bl",false,0,2],[698,4,"ramp_tr",false,0,2],[698,5,"block",false,0,2],[698,6,"block",false,0,2],[698,7,"block",false,0,2],[698,8,"block",false,0,2],[698,9,"block",false,0,2],[699,0,"ramp_bl",false,0,2],[699,3,"ramp_tr",false,0,2],[699,4,"block",false,0,2],[699,5,"block",false,0,2],[699,6,"block",false,0,2],[699,7,"block",false,0,2],[699,8,"block",false,0,2],[699,9,"block",false,0,2],[700,2,"ramp_tr",false,0,2],[700,3,"block",false,0,2],[700,4,"block",false,0,2],[700,5,"block",false,0,2],[700,6,"block",false,0,2],[700,7,"block",false,0,2],[700,8,"block",false,0,2],[700,9,"block",false,0,2],[701,2,"ramp_tl",false,0,2],[701,3,"block",false,0,2],[701,4,"block",false,0,2],[701,5,"block",false,0,2],[701,6,"block",false,0,2],[701,7,"block",false,0,2],[701,8,"block",false,0,2],[701,9,"block",false,0,2],[702,0,"ramp_br",false,0,2],[702,3,"ramp_tl",false,0,2],[702,4,"block",false,0,2],[702,5,"block",false,0,2],[702,6,"block",false,0,2],[702,7,"block",false,0,2],[702,8,"block",false,0,2],[702,9,"block",false,0,2],[703,0,"block",false,0,2],[703,1,"ramp_br",false,0,2],[703,4,"ramp_tl",false,0,2],[703,5,"block",false,0,2],[703,6,"block",false,0,2],[703,7,"block",false,0,2],[703,8,"block",false,0,2],[703,9,"block",false,0,2],[704,0,"block",false,0,2],[704,1,"block",false,0,2],[704,2,"ramp_br",false,0,2],[704,5,"ramp_tl",false,0,2],[704,6,"block",false,0,2],[704,7,"block",false,0,2],[704,8,"block",false,0,2],[704,9,"block",false,0,2],[705,0,"block",false,0,2],[705,1,"block",false,0,2],[705,2,"ramp_bl",false,0,2],[705,5,"ramp_tr",false,37,2],[705,6,"block",false,0,2],[705,7,"block",false,0,2],[705,8,"block",false,0,2],[705,9,"block",false,0,2],[706,0,"block",false,0,2],[706,1,"ramp_bl",false,0,2],[706,4,"ramp_tr",false,37,2],[706,5,"block",false,37,2],[706,6,"block",false,0,2],[706,7,"block",false,0,2],[706,8,"block",false,0,2],[706,9,"block",false,0,2],[707,0,"ramp_bl",false,0,2],[707,3,"ramp_tr",false,0,2],[707,4,"block",false,37,2],[707,5,"block",false,37,2],[707,6,"block",false,0,2],[707,7,"block",false,0,2],[707,8,"block",false,0,2],[707,9,"block",false,0,2],[708,2,"ramp_tr",false,0,2],[708,3,"block",false,0,2],[708,4,"block",false,37,2],[708,5,"block",false,37,2],[708,6,"block",false,0,2],[708,7,"block",false,0,2],[708,8,"block",false,0,2],[708,9,"block",false,0,2],[709,2,"ramp_tl",false,0,2],[709,3,"block",false,0,2],[709,4,"block",false,37,2],[709,5,"block",false,37,2],[709,6,"block",false,0,2],[709,7,"block",false,0,2],[709,8,"block",false,0,2],[709,9,"block",false,0,2],[710,0,"ramp_br",false,0,2],[710,3,"ramp_tl",false,0,2],[710,4,"block",false,37,2],[710,5,"block",false,37,2],[710,6,"block",false,0,2],[710,7,"block",false,0,2],[710,8,"block",false,0,2],[710,9,"block",false,0,2],[711,0,"block",false,0,2],[711,1,"ramp_br",false,0,2],[711,4,"ramp_tl",false,37,2],[711,5,"block",false,37,2],[711,6,"block",false,0,2],[711,7,"block",false,0,2],[711,8,"block",false,0,2],[711,9,"block",false,0,2],[712,0,"block",false,0,2],[712,1,"block",false,0,2],[712,2,"ramp_br",false,0,2],[712,5,"ramp_tl",false,37,2],[712,6,"block",false,0,2],[712,7,"block",false,0,2],[712,8,"block",false,0,2],[712,9,"block",false,0,2],[713,0,"block",false,0,2],[713,1,"block",false,0,2],[713,2,"block",false,0,2],[713,5,"coin",false,38],[713,6,"block",false,0,2],[713,7,"block",false,0,2],[713,8,"block",false,0,2],[713,9,"block",false,0,2],[714,0,"block",false,0,2],[714,1,"block",false,0,2],[714,2,"block",false,0,2],[714,6,"block",false,0,2],[714,7,"block",false,0,2],[714,8,"block",false,0,2],[714,9,"block",false,0,2],[715,0,"block",false,0,2],[715,1,"block",false,0,2],[715,2,"block",false,0,2],[715,6,"block",false,0,2],[715,7,"block",false,0,2],[715,8,"block",false,0,2],[715,9,"block",false,0,2],[716,0,"block",false,0,2],[716,1,"block",false,0,2],[716,2,"block",false,0,2],[716,6,"block",false,0,2],[716,7,"block",false,0,2],[716,8,"block",false,0,2],[716,9,"block",false,0,2],[717,0,"block",false,0,2],[717,1,"block",false,0,2],[717,2,"block",false,0,2],[717,6,"block",false,0,2],[717,7,"block",false,0,2],[717,8,"block",false,0,2],[717,9,"block",false,0,2],[718,0,"block",false,0,2],[718,1,"block",false,0,2],[718,2,"block",false,0,2],[718,6,"block",false,0,2],[718,7,"block",false,0,2],[718,8,"block",false,0,2],[718,9,"block",false,0,2],[719,0,"block",false,0,2],[719,1,"block",false,0,2],[719,2,"block",false,0,2],[719,6,"block",false,0,2],[719,7,"block",false,0,2],[719,8,"block",false,0,2],[719,9,"block",false,0,2],[720,0,"block",false,0,2],[720,1,"block",false,0,2],[720,2,"ramp_bl",false,0,2],[720,6,"ramp_tl",false,0,2],[720,7,"block",false,0,2],[720,8,"block",false,0,2],[720,9,"block",false,0,2],[721,0,"block",false,0,2],[721,1,"block",false,0,2],[721,7,"block",false,0,2],[721,8,"block",false,0,2],[721,9,"block",false,0,2],[722,0,"block",false,0,2],[722,1,"ramp_bl",false,0,2],[722,7,"ramp_tl",false,0,2],[722,8,"block",false,0,2],[722,9,"block",false,0,2],[723,0,"block",false,0,2],[723,8,"block",false,0,2],[723,9,"block",false,0,2],[724,0,"ramp_bl",false,0,2],[724,8,"block",false,0,2],[724,9,"block",false,0,2],[725,8,"ramp_tl",false,0,2],[725,9,"block",false,0,2],[726,9,"block",false,0,2],[727,9,"block",false,0,2],[728,0,"spike",false,0,2],[728,9,"ramp_tl",false,0,2],[729,0,"spike",false,0,2],[729,9,"spike",true,0,2],[730,0,"spike",false,0,2],[730,9,"spike",true,0,2],[731,0,"spike",false,0,2],[731,9,"spike",true,0,2],[732,0,"block",false,0,2],[732,1,"spike",false,0,2],[732,8,"spike",true,0,2],[732,9,"block",false,0,2],[733,0,"block",false,0,2],[733,1,"spike",false,0,2],[733,8,"spike",true,0,2],[733,9,"block",false,0,2],[734,0,"block",false,0,2],[734,1,"spike",false,0,2],[734,8,"spike",true,0,2],[734,9,"block",false,0,2],[735,0,"block",false,0,2],[735,1,"spike",false,0,2],[735,8,"spike",true,0,2],[735,9,"block",false,0,2],[736,0,"block",false,0,2],[736,1,"block",false,0,2],[736,2,"spike",false,0,2],[736,7,"spike",true,0,2],[736,8,"block",false,0,2],[736,9,"block",false,0,2],[737,0,"block",false,0,2],[737,1,"block",false,0,2],[737,2,"spike",false,0,2],[737,7,"spike",true,0,2],[737,8,"block",false,0,2],[737,9,"block",false,0,2],[738,0,"block",false,0,2],[738,1,"block",false,0,2],[738,2,"spike",false,0,2],[738,7,"spike",true,0,2],[738,8,"block",false,0,2],[738,9,"block",false,0,2],[739,0,"block",false,0,2],[739,1,"block",false,0,2],[739,2,"spike",false,0,2],[739,7,"spike",true,0,2],[739,8,"block",false,0,2],[739,9,"block",false,0,2],[740,0,"block",false,0,2],[740,1,"block",false,0,2],[740,2,"block",false,0,2],[740,3,"spike",false,0,2],[740,6,"spike",true,0,2],[740,7,"block",false,0,2],[740,8,"block",false,0,2],[740,9,"block",false,0,2],[741,0,"block",false,0,2],[741,1,"block",false,0,2],[741,2,"block",false,0,2],[741,3,"spike",false,0,2],[741,6,"spike",true,0,2],[741,7,"block",false,0,2],[741,8,"block",false,0,2],[741,9,"block",false,0,2],[742,0,"block",false,0,2],[742,1,"block",false,0,2],[742,2,"block",false,0,2],[742,3,"spike",false,0,2],[742,6,"spike",true,0,2],[742,7,"block",false,0,2],[742,8,"block",false,0,2],[742,9,"block",false,0,2],[743,0,"block",false,0,2],[743,1,"block",false,0,2],[743,2,"block",false,0,2],[743,3,"spike",false,0,2],[743,6,"spike",true,0,2],[743,7,"block",false,0,2],[743,8,"block",false,0,2],[743,9,"block",false,0,2],[744,0,"block",false,0,2],[744,1,"block",false,0,2],[744,2,"block",false,0,2],[744,3,"spike",false,0,2],[744,6,"spike",true,0,2],[744,7,"block",false,0,2],[744,8,"block",false,0,2],[744,9,"block",false,0,2],[745,0,"block",false,0,2],[745,1,"block",false,0,2],[745,2,"block",false,0,2],[745,3,"spike",false,0,2],[745,6,"spike",true,0,2],[745,7,"block",false,0,2],[745,8,"block",false,0,2],[745,9,"block",false,0,2],[746,0,"block",false,0,2],[746,1,"block",false,0,2],[746,2,"block",false,0,2],[746,3,"spike",false,0,2],[746,6,"spike",true,0,2],[746,7,"block",false,0,2],[746,8,"block",false,0,2],[746,9,"block",false,0,2],[747,0,"block",false,0,2],[747,1,"block",false,0,2],[747,2,"block",false,0,2],[747,3,"spike",false,0,2],[747,6,"spike",true,0,2],[747,7,"block",false,0,2],[747,8,"block",false,0,2],[747,9,"block",false,0,2]],"gravs":[[28,true],[151,true],[160,false],[192,true]],"portals":[[47,"ship"],[77,"spider"],[123,"cube"],[191,"ship"],[230,"ship"],[251,"cube"],[303,"wave"],[358,"ship"],[425,"cube"],[451,"wave"],[728,"ship"]],"speeds":[[17,1.5],[77,1.0],[123,1.5],[142,1.5],[228,1.5],[303,1.0],[424,0.8],[452,1.8],[499,1.0]],"texts":[[38,6,"I See You!",11],[114,6,"There is no escape!",11],[133,9,"You\'re Stuck in here with me.",11],[216,8,"That\'s It",11],[316,8,"You\'re Not Leaving Alive",11],[363,9,"What? How did you Survive?",11],[437,9,"I\'m not going easy on you anymore",12],[505,9,"You really wont die",13],[536,5,"Give",13],[556,5,"up",13]],"triggers":[[8,3,{"type":"move","group":1,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[9,3,{"type":"move","group":2,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[10,3,{"type":"move","group":3,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[11,3,{"type":"move","group":4,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[12,3,{"type":"move","group":5,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[13,3,{"type":"move","group":6,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[14,3,{"type":"move","group":7,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[15,3,{"type":"move","group":8,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[16,3,{"type":"move","group":9,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[17,3,{"type":"move","group":10,"dx":0.0,"dy":14.0,"time":1.0,"ease":true}],[36,4,{"type":"reveal","group":11,"show":true}],[44,5,{"type":"reveal","group":11,"show":false}],[111,4,{"type":"reveal","group":11,"show":true}],[119,4,{"type":"reveal","group":11,"show":false}],[131,7,{"type":"reveal","group":11,"show":true}],[139,8,{"type":"reveal","group":11,"show":false}],[212,6,{"type":"reveal","group":11,"show":true}],[220,7,{"type":"reveal","group":11,"show":false}],[304,2,{"type":"reveal","group":12,"show":false}],[314,6,{"type":"reveal","group":11,"show":true}],[322,7,{"type":"reveal","group":11,"show":false}],[331,3,{"type":"reveal","group":12,"show":true}],[353,4,{"type":"reveal","group":13,"show":false}],[353,5,{"type":"reveal","group":14,"show":false}],[361,7,{"type":"reveal","group":11,"show":true}],[369,8,{"type":"reveal","group":11,"show":false}],[370,2,{"type":"reveal","group":13,"show":true}],[373,0,{"type":"move","group":13,"dx":0.0,"dy":-2.5,"time":0.3,"ease":true}],[379,5,{"type":"move","group":15,"dx":0.0,"dy":6.0,"time":2.0,"ease":true}],[381,4,{"type":"reveal","group":14,"show":true}],[385,9,{"type":"move","group":14,"dx":0.0,"dy":2.5,"time":0.2,"ease":true}],[391,3,{"type":"move","group":16,"dx":0.0,"dy":-6.0,"time":2.0,"ease":true}],[404,1,{"type":"move","group":17,"dx":0.0,"dy":-7.0,"time":1.0,"ease":true}],[408,2,{"type":"move","group":17,"dx":0.0,"dy":7.0,"time":3.0,"ease":true}],[413,1,{"type":"move","group":18,"dx":0.0,"dy":-7.0,"time":1.0,"ease":true}],[417,2,{"type":"move","group":18,"dx":0.0,"dy":7.0,"time":3.0,"ease":true}],[421,1,{"type":"move","group":19,"dx":0.0,"dy":-7.0,"time":1.0,"ease":true}],[425,2,{"type":"move","group":19,"dx":0.0,"dy":7.0,"time":3.0,"ease":true}],[426,3,{"type":"reveal","group":20,"show":false}],[430,7,{"type":"reveal","group":11,"show":true}],[435,4,{"type":"move","group":12,"dx":0.0,"dy":8.0,"time":2.5,"ease":true}],[439,2,{"type":"reveal","group":20,"show":true}],[443,2,{"type":"move","group":12,"dx":0.0,"dy":12.0,"time":0.5,"ease":true}],[502,5,{"type":"reveal","group":13,"show":true}],[514,5,{"type":"reveal","group":13,"show":false}],[518,4,{"type":"light","effect":"flicker_off","radius":3.0,"time":0.5}],[528,4,{"type":"light","effect":"flicker_on","radius":3.0,"time":0.5}],[539,4,{"type":"light","effect":"flicker_off","radius":3.0,"time":0.5}],[551,4,{"type":"light","effect":"flicker_on","radius":3.0,"time":0.5}],[560,3,{"type":"light","effect":"flicker_off","radius":3.0,"time":0.5}],[578,3,{"type":"light","effect":"flicker_on","radius":3.0,"time":0.5}],[581,5,{"type":"light","effect":"close_circle","radius":4.0,"time":0.5}],[584,5,{"type":"light","effect":"open_circle","radius":3.0,"time":0.5}],[696,4,{"type":"move","group":38,"dx":-5.0,"dy":0.5,"time":0,"ease":true}],[703,3,{"type":"reveal","group":37,"show":false}]]}')


def build_velocity_finish(lv):
    LevelData.from_json(VELOCITY_FINISH).build(lv)


# The official level ranks (hardest first).  RANKED_LEVELS[0] is the "Top 1":
# beating it earns the Crown cube.  Shown in the level select's "Ranks" tab.
RANKED_LEVELS = [
    dict(name="Velocity Finish", maker="AugmentedMagic", verifier="AXO",
         victors=["AXO"], frame_perfects="0"),
    dict(name="Velocity Battle", maker="AugmentedMagic", verifier="AXO",
         victors=["AXO"], frame_perfects="0"),
    dict(name="Neon Gauntlet", maker="Claude", verifier="AXO",
         victors=["AXO"], frame_perfects="1 (60 Hz)"),
    dict(name="Chopper City", maker="Claude", verifier="AXO",
         victors=["AXO"], frame_perfects="0"),
    dict(name="Inferno Circuit", maker="Claude", verifier="AXO",
         victors=["AXO"], frame_perfects="0"),
]
TOP_DEMONS = [r["name"] for r in RANKED_LEVELS]          # hardest first: [0] is the Top 1

# Completions earned before a level was added to the game: account name -> 100 percent.
# (Accounts live on each computer, so this goes to any account with that name.)
VERIFIED_COMPLETIONS = {"Velocity Finish": ["AXO"]}


LEVELS = [
    LevelDef("Test Course", "TEST", "Every game mode, in order, plus pads, orbs and portals",
             build_test_course),
    LevelDef("Warm Up", "EASY", "Cube and ship basics - a gentle start", build_warm_up),
    LevelDef("Flip Side", "NORMAL", "Ball, spider and swing copter: all about gravity",
             build_flip_side),
    LevelDef("Wave Runner", "NORMAL", "Tap to weave the wave through tunnels and spikes",
             build_wave_runner),
    LevelDef("Robot Factory", "HARD", "Precise robot jumps, spiders and a few orbs",
             build_robot_factory),
    LevelDef("Turbo Charge", "HARD", "Speed portals from 0.8x to 1.8x, plus a down orb",
             build_turbo),
    LevelDef("Sky High", "HARD", "Ship, UFO and wave through tight corridors", build_sky_high),
    LevelDef("Axolotl Lagoon", "HARD", "An underwater swim with the axolotls - beat it to "
             "unlock the Pink Axolotl ship", build_axolotl_lagoon),
    LevelDef("Dolphin Bay", "HARD", "Ride the wave with a pod of dolphins - beat it to "
             "unlock the Dolphin wave", build_dolphin_bay),
    LevelDef("Grand Finale", "INSANE", "All eight modes, no mercy", build_finale),
    LevelDef("Neon Gauntlet", "INSANE", "Ramps, ceiling runs, a spider maze and a wave in the "
             "dark - 3 coins", build_neon_gauntlet),
    LevelDef("Inferno Circuit", "INSANE", "UFO gaps, ball flips, swing gates, robot towers, "
             "sloped ship tunnel - 3 coins", build_inferno_circuit),
    LevelDef("Chopper City", "INSANE", "Swing through a city at night with helicopters "
             "overhead - beat it to unlock the Axo-Copter", build_chopper_city),
    LevelDef("Crystal Caverns", "INSANE", "Scuttle through glowing caves - beat it to unlock "
             "the Crystal Monster spider", build_crystal_caverns),
    LevelDef("Backyard Pups", "INSANE", "Romp around a backyard full of puppies - beat it to "
             "unlock the Puppy Bot robot", build_backyard_pups),
    LevelDef("Abyss Drift", "INSANE", "Gravity-flipping cube and ship, then a swing in the "
             "dark - 3 coins", build_abyss_drift),
    LevelDef("Velocity Battle", "DEMON", "DEMON  -  by AugmentedMagic",
             build_velocity_battle),
    LevelDef("Velocity Finish", "DEMON", "TOP 1 DEMON  -  by AugmentedMagic  -  beat it to "
             "earn the Crown cube", build_velocity_finish),
]



for _d in LEVELS:                        # ranked levels show their rank: "#3  Neon Gauntlet"
    if _d.name in TOP_DEMONS:
        _d.title = "#%d  %s" % (TOP_DEMONS.index(_d.name) + 1, _d.name)
# --------------------------------------------------------------------------
# Player
# --------------------------------------------------------------------------
class Player:
    def __init__(self):
        self.x = 0.0
        self.y = 240.0
        self.vy = 0.0
        self.g = 1
        self.mode = "cube"
        self.w, self.h = SIZE["cube"]
        self.section = 0
        self.on_ground = False
        self.alive = True
        self.rot = 0.0
        self.buffer = 0
        self.anim = 0
        self.robot_jumping = False
        self.robot_t = 0
        self.wave_dir = 1            # +1 = toward gravity (down), -1 = away (up)
        self.speed_mult = 1.0        # set by speed portals
        self.used_orbs = frozenset()
        self.coins = frozenset()     # coins picked up this attempt: {(col, row)}
        self.mini = False            # mini wave
        self.wave_hold = False       # wave control: False = click to switch, True = hold to rise
        self.trail = deque(maxlen=28)

    @property
    def speed(self):
        return SPEED * self.speed_mult

    def clone(self):
        c = copy.copy(self)
        c.trail = deque(maxlen=28)      # visual only
        return c

    # ---- state management ------------------------------------------------
    def rect(self):
        return pygame.Rect(int(round(self.x - self.w / 2)),
                           int(round(self.y - self.h / 2)), self.w, self.h)

    def set_mode(self, mode):
        self.mini = mode == "miniwave"       # the mini wave: small, and twice as steep
        if self.mini:
            mode = "wave"
        self.mode = mode
        self.w, self.h = MINI_WAVE_SIZE if self.mini else SIZE[mode]
        half = self.h / 2
        self.y = min(self.y, FLOOR - half)
        if mode in CEIL_MODES:
            self.y = max(self.y, CEIL + half)
        self.robot_jumping = False
        self.robot_t = 0
        self.wave_dir = 1
        self.trail.clear()

    def respawn(self, level, sec):
        mode, _ = level.sections[sec]
        self.section = sec
        self.x = 3.0 * B if sec == 0 else float(level.starts_px[sec])
        self.speed_mult = level.speed_at(self.x)
        self.y = 240.0
        self.vy = 0.0
        self.g = 1
        self.rot = 0.0
        self.alive = True
        self.buffer = 0
        self.anim = 0
        self.used_orbs = frozenset()
        self.coins = frozenset()
        self.set_mode(mode)
        if mode in ("cube", "robot", "ball", "spider"):
            self.y = FLOOR - self.h / 2
            self.on_ground = True
        else:
            self.on_ground = False

    def enter_section(self, idx, game):
        self.section = idx
        mode = game.level.sections[idx][0]
        game.cp_section = idx
        self.set_mode(mode)
        self.g = 1
        self.vy = 0.0
        self.rot = 0.0

    def bounce(self, up, power):
        """Pads and orbs.  `up` kicks you away from gravity, otherwise toward it.
        Works in every mode: the wave (which only has a direction) is simply pointed
        up or down, the others get a velocity kick that their own physics then plays out."""
        if self.mode == "wave":
            self.wave_dir = -1 if up else 1
            self.vy = self.speed * self.g * self.wave_dir
        else:
            self.vy = (-power if up else power) * self.g
        self.on_ground = False
        self.robot_jumping = False

    # ---- per-mode controls -------------------------------------------------
    def clamp_fall(self, maxf):
        if self.vy * self.g > maxf:
            self.vy = maxf * self.g

    def spider_teleport(self, level):
        """Instantly jump to the nearest surface in the opposite direction."""
        new_g = -self.g
        half = self.h / 2
        r = self.rect()
        if new_g == -1:      # go up
            best = CEIL
            for o in level.near(self.x):
                if (o.kind in SOLID and o.rect.right > r.left
                        and o.rect.left < r.right and o.rect.bottom <= r.top):
                    best = max(best, o.rect.bottom)
            self.y = best + half
        else:                # go down
            best = FLOOR
            for o in level.near(self.x):
                if (o.kind in SOLID and o.rect.right > r.left
                        and o.rect.left < r.right and o.rect.top >= r.bottom):
                    best = min(best, o.rect.top)
            self.y = best - half
        self.g = new_g
        self.vy = 0.0
        self.on_ground = True

    def control(self, held, level):
        m, g = self.mode, self.g
        press = self.buffer > 0

        if m == "cube":
            if self.on_ground and (held or press):
                self.vy = -CUBE_JUMP * g
                self.on_ground = False
                self.buffer = 0
            else:
                self.vy += g * CUBE_G
            self.clamp_fall(CUBE_MAXFALL)

        elif m == "robot":
            if self.on_ground and press:
                self.robot_jumping = True
                self.robot_t = 1
                self.vy = -ROBOT_V * g
                self.on_ground = False
                self.buffer = 0
            elif self.robot_jumping and held and self.robot_t < ROBOT_HOLD:
                self.vy = -ROBOT_V * g
                self.robot_t += 1
            else:
                self.robot_jumping = False
                self.vy += g * ROBOT_G
            self.clamp_fall(ROBOT_MAXFALL)

        elif m == "ball":
            if self.on_ground and press:
                self.g = -g
                g = self.g
                self.vy = 2.0 * g
                self.on_ground = False
                self.buffer = 0
            self.vy += g * BALL_G
            self.clamp_fall(BALL_MAXFALL)

        elif m == "ufo":
            self.vy += g * UFO_G
            if press:
                self.vy = -UFO_HOP * g
                self.buffer = 0
            self.clamp_fall(UFO_MAXFALL)

        elif m == "ship":
            self.vy += g * (-SHIP_UP if held else SHIP_DOWN)
            self.vy = max(-SHIP_MAX, min(SHIP_MAX, self.vy))

        elif m == "wave":
            if self.wave_hold:              # hold to rise, release to fall
                self.wave_dir = -1 if held else 1
                self.buffer = 0
            elif press:                     # each click toggles up <-> down
                self.wave_dir = -self.wave_dir
                self.buffer = 0
            self.vy = self.speed * g * self.wave_dir * (2 if self.mini else 1)

        elif m == "spider":
            if self.on_ground and press:
                self.spider_teleport(level)
                self.buffer = 0
            else:
                self.vy += g * SPIDER_G
                self.clamp_fall(SPIDER_MAXFALL)

        elif m == "swing":
            if press:
                self.g = -g
                self.buffer = 0
            self.vy += self.g * SWING_A
            self.vy = max(-SWING_MAX, min(SWING_MAX, self.vy))

    # ---- one physics step --------------------------------------------------
    def step(self, held, game):
        lv = game.level
        idx = bisect.bisect_right(lv.starts_px, self.x) - 1
        if idx != self.section:
            self.enter_section(idx, game)
        mode = self.mode
        self.anim += 1
        self.control(held, lv)

        # --- horizontal movement + side collisions -------------------------
        was_ground = self.on_ground
        self.x += self.speed
        near = lv.near(self.x)
        climb = self.speed + STEP_TOL            # how much a slope can lift you per frame
        if not game.noclip:
            r = self.rect()
            for o in near:
                if o.kind not in SOLID:
                    continue
                hit = solid_hit(o, r)
                if hit is None:
                    continue
                ramp = o.kind != "block"
                if mode == "wave":                  # the wave dies on any block or ramp
                    game.kill()
                    return
                top_pen, bot_pen = hit
                lift = (self.speed * ramp_steepness(o.kind) + STEP_TOL) if ramp else climb
                tol_top = lift if o.kind in FLOOR_RAMPS else STEP_TOL
                tol_bot = lift if (ramp and o.kind not in FLOOR_RAMPS) else STEP_TOL
                if top_pen <= tol_top and top_pen <= bot_pen:       # clipped a top corner
                    self.y -= top_pen
                    if self.vy > 0:
                        self.vy = 0.0
                elif bot_pen <= tol_bot:                            # clipped an underside corner
                    self.y += bot_pen
                    if self.vy < 0:
                        self.vy = 0.0
                else:                                               # hit a wall
                    game.kill()
                    return
                r = self.rect()

        # --- vertical movement + landing -----------------------------------
        half = self.h / 2
        prev_top = self.y - half
        prev_bottom = self.y + half
        self.y += self.vy
        self.on_ground = False
        r = self.rect()
        reach = abs(self.vy) + climb
        for o in near:
            if o.kind not in SOLID:
                continue
            hit = solid_hit(o, r)
            if hit is None:
                continue
            ramp = o.kind != "block"
            if mode == "wave" and not game.noclip:
                game.kill()
                return
            top_pen, bot_pen = hit
            if ramp:                       # steeper slopes lift you further per frame
                reach = abs(self.vy) + self.speed * ramp_steepness(o.kind) + STEP_TOL
            if ramp and o.kind in FLOOR_RAMPS and top_pen <= reach and top_pen <= bot_pen + 8:
                self.y -= top_pen                                   # on the slope
                if self.vy > 0:
                    self.vy = 0.0
                if self.g == 1:
                    self.on_ground = True
            elif ramp and o.kind not in FLOOR_RAMPS and bot_pen <= reach \
                    and bot_pen <= top_pen + 8:
                self.y += bot_pen                                   # under a ceiling slope
                if self.vy < 0:
                    self.vy = 0.0
                if self.g == -1:
                    self.on_ground = True
            elif prev_bottom <= o.rect.top + 1:                     # landed on top
                self.y = o.rect.top - half
                if self.vy > 0:
                    self.vy = 0.0
                if self.g == 1:
                    self.on_ground = True
            elif prev_top >= o.rect.bottom - 1:                     # bumped underside
                self.y = o.rect.bottom + half
                if self.vy < 0:
                    self.vy = 0.0
                if self.g == -1:
                    self.on_ground = True
            r = self.rect()

        # --- stick to downhill slopes instead of flying off them -------------
        if (was_ground and not self.on_ground and mode in ("cube", "robot", "ball", "spider")
                and self.vy * self.g >= 0):
            best = None
            for o in near:
                if o.kind not in RAMPS or r.right <= o.rect.left or r.left >= o.rect.right:
                    continue
                floor, y = ramp_span(o, r.left, r.right)
                if self.g == 1 and floor:
                    gap = y - r.bottom
                elif self.g == -1 and not floor:
                    gap = r.top - y
                else:
                    continue
                if (0 <= gap <= self.speed * ramp_steepness(o.kind) + 2
                        and (best is None or gap < best)):
                    best = gap
            if best is not None:
                self.y += best * self.g
                self.vy = 0.0
                self.on_ground = True
                r = self.rect()

        # --- floor / ceiling -----------------------------------------------
        if self.y + half >= FLOOR:
            self.y = FLOOR - half
            if self.vy > 0:
                self.vy = 0.0
            if self.g == 1:
                self.on_ground = True
        if mode in CEIL_MODES and self.y - half <= CEIL:
            self.y = CEIL + half
            if self.vy < 0:
                self.vy = 0.0
            if self.g == -1:
                self.on_ground = True

        # --- hazards & interactables ----------------------------------------
        r = self.rect()
        for o in near:
            k = o.kind
            if k in SPIKES:
                if r.colliderect(o.rect) and not game.noclip:
                    game.kill()
                    return
            elif k in ("pad", "dpad"):
                # pads fire whenever you touch them: yellow bounces you up, blue slams
                # you down (they ignore you if you're already moving that way)
                if r.colliderect(o.rect):
                    up = k == "pad"
                    if mode == "wave":
                        fire = self.wave_dir != (-1 if up else 1)
                    elif up:
                        fire = self.vy * self.g >= 0
                    else:
                        fire = self.vy * self.g < DPAD_V - 0.5
                    if fire:
                        self.bounce(up, PAD_V if up else DPAD_V)
                        game.burst(o.rect.centerx, o.rect.centery,
                                   (255, 230, 40) if up else (90, 150, 255), 10)
            elif k == "coin":
                key = (o.col, o.row)
                if key not in self.coins and r.colliderect(o.rect):
                    self.coins = self.coins | {key}
                    game.burst(o.rect.centerx, o.rect.centery, (255, 215, 60), 18)
            elif k == "grav":
                if r.colliderect(o.rect):
                    self.g = -1 if o.up else 1
            elif k == "speed":
                if r.colliderect(o.rect):
                    self.speed_mult = o.val
            elif k in ("orb", "dorb"):
                # orbs fire automatically when you touch them (once per attempt):
                # yellow bounces you up, blue slams you down
                key = (o.col, o.row)
                if (key not in self.used_orbs
                        and math.hypot(self.x - o.rect.centerx,
                                       self.y - o.rect.centery) < ORB_RADIUS):
                    self.used_orbs = self.used_orbs | {key}
                    self.bounce(k == "orb", ORB_V if k == "orb" else DORB_V)
                    game.burst(o.rect.centerx, o.rect.centery,
                               (255, 230, 40) if k == "orb" else (90, 150, 255), 14)

        # --- visuals ---------------------------------------------------------
        if mode == "cube":
            if self.on_ground:
                target = round(self.rot / 90.0) * 90.0
                self.rot += (target - self.rot) * 0.45
            else:
                self.rot -= 7.5 * self.g
        elif mode == "ball":
            self.rot -= 8.0 * self.g
        if mode == "wave":
            self.trail.append((self.x, self.y))
        elif self.trail:
            self.trail.clear()
        if self.buffer > 0:
            self.buffer -= 1

    def angle(self):
        m = self.mode
        if m in ("cube", "ball"):
            return self.rot
        if m == "ship":
            return max(-40, min(40, -self.vy * 3.5))
        if m == "ufo":
            return max(-15, min(15, -self.vy * 1.5))
        if m == "swing":
            return max(-20, min(20, -self.vy * 2.0))
        if m == "wave":
            return math.degrees(math.atan2(-self.vy, self.speed))
        return 0.0


# --------------------------------------------------------------------------
# Skins: every game mode has its own set.  A skin is a colour pair plus a
# drawing style; some are locked until you beat a certain level.
# --------------------------------------------------------------------------
PALETTES = {
    "classic": ((90, 245, 120), (60, 200, 255)),
    "inferno": ((255, 90, 60), (255, 210, 70)),
    "ocean": ((60, 140, 255), (120, 255, 240)),
    "royal": ((170, 90, 255), (255, 215, 90)),
    "bubblegum": ((255, 130, 200), (255, 240, 250)),
    "mono": ((235, 235, 235), (90, 90, 100)),
    "toxic": ((190, 255, 60), (40, 60, 40)),
    "axolotl": ((255, 150, 200), (255, 90, 150)),
    "dolphin": ((110, 165, 215), (225, 240, 250)),
    "bluelotl": ((70, 125, 245), (30, 55, 170)),
    "crown": ((120, 50, 200), (255, 205, 60)),
    "crystal": ((150, 90, 245), (110, 250, 240)),
    "puppy": ((222, 165, 90), (250, 232, 200)),
}
# per mode: (id, name, palette, style, unlocked by beating this level - None = free)
_COMMON = [("classic", "Classic", "classic", "classic", None),
           ("inferno", "Inferno", "inferno", "classic", None),
           ("ocean", "Ocean", "ocean", "classic", None),
           ("royal", "Royal", "royal", "classic", None),
           ("bubblegum", "Bubblegum", "bubblegum", "classic", None),
           ("mono", "Mono", "mono", "classic", None)]
_SPECIAL = {
    "cube": [("grin", "Grin", "toxic", "grin", "Warm Up"),
             ("visor", "Visor", "inferno", "visor", "Turbo Charge"),
             ("crown", "Crown", "crown", "crown", "TOP1")],      # beat the Top 1 demon
    "ship": [("jet", "Jet", "mono", "jet", "Sky High"),
             ("axolotl", "Pink Axolotl", "axolotl", "axolotl", "Axolotl Lagoon")],
    "ball": [("swirl", "Swirl", "royal", "swirl", "Flip Side")],
    "ufo": [("alien", "Alien", "toxic", "alien", "Sky High")],
    "wave": [("dart", "Neon Dart", "ocean", "dart", "Neon Gauntlet"),
             ("dolphin", "Dolphin", "dolphin", "dolphin", "Dolphin Bay")],
    "robot": [("antenna", "Antenna Bot", "inferno", "antenna", "Inferno Circuit"),
              ("puppy", "Puppy Bot", "puppy", "puppy", "Backyard Pups")],
    "spider": [("eyes", "Many Eyes", "royal", "eyes", "Robot Factory"),
               ("crystal", "Crystal Monster", "crystal", "crystal", "Crystal Caverns")],
    "swing": [("heli", "Heli", "mono", "heli", "Abyss Drift"),
              ("axocopter", "Axo-Copter", "bluelotl", "axocopter", "Chopper City")],
}
SKINS = {m: [dict(id=i, name=n, a=PALETTES[pal][0], b=PALETTES[pal][1], style=st, unlock=u)
             for i, n, pal, st, u in _COMMON + _SPECIAL[m]] for m in MODE_ORDER}


def find_skin(mode, sid):
    for sk in SKINS[mode]:
        if sk["id"] == sid:
            return sk
    return SKINS[mode][0]


def draw_axolotl(s, x, y, size=1.0, body=(255, 150, 200), gill=(255, 80, 150), t=0,
                 flip=False):
    """A little axolotl facing right (left with flip=True), centred on (x, y).
    `size` 1.0 is about 56 px long.  Used for the ship skin and the underwater theme."""
    def P(px, py):
        px = -px if flip else px
        return int(x + px * size), int(y + py * size)

    def R(v):
        return max(1, int(v * size))

    sway = math.sin(t * 0.15) * 3
    dark = tuple(max(0, c - 70) for c in body)
    # tail fin
    pygame.draw.polygon(s, dark, [P(-14, -4), P(-30, -9 + sway), P(-34, 0 + sway),
                                  P(-30, 8 + sway), P(-14, 5)])
    pygame.draw.polygon(s, body, [P(-14, -3), P(-28, -7 + sway), P(-31, 0 + sway),
                                  P(-28, 6 + sway), P(-14, 4)])
    # legs
    for lx, ph in ((-8, 0.0), (6, 1.7)):
        ly = math.sin(t * 0.25 + ph) * 2
        pygame.draw.line(s, dark, P(lx, 6), P(lx - 3, 13 + ly), R(4))
    # gills: three feathery fronds on each side, sweeping back from the head
    # (drawn before the head so their roots are hidden behind it)
    for k, (root, tip) in enumerate((((12, -7), (11, -24)), ((9, -5), (0, -21)),
                                     ((8, -2), (-9, -14)))):
        w = math.sin(t * 0.2 + k) * 1.5
        tx, ty = tip[0] + w, tip[1]
        pygame.draw.line(s, gill, P(*root), P(tx, ty), R(3))
        for f in (0.5, 0.75, 1.0):                       # feathery side tufts
            fx = root[0] + (tx - root[0]) * f
            fy = root[1] + (ty - root[1]) * f
            pygame.draw.line(s, gill, P(fx, fy), P(fx - 4, fy + 1), R(2))
            pygame.draw.line(s, gill, P(fx, fy), P(fx + 4, fy + 1), R(2))
    # body + head
    bx0, by0 = P(-18, -8)
    bx1, by1 = P(10, 8)
    pygame.draw.ellipse(s, body, (min(bx0, bx1), min(by0, by1), abs(bx1 - bx0), abs(by1 - by0)))
    hx, hy = P(14, -1)
    pygame.draw.circle(s, body, (hx, hy), R(11))
    # face
    pygame.draw.circle(s, (20, 10, 30), P(18, -4), R(2.5))
    pygame.draw.circle(s, (255, 255, 255), P(18.8, -4.8), R(0.9))
    pygame.draw.lines(s, (120, 40, 90), False, [P(15, 3), P(19, 5), P(23, 3)], R(1.5))
    pygame.draw.circle(s, (255, 190, 220), P(21, 2), R(2))          # rosy cheek


def draw_dolphin(s, x, y, size=1.0, body=(110, 165, 215), belly=(225, 240, 250), t=0,
                 flip=False, outline=None):
    """A dolphin facing right (left with flip=True), centred on (x, y).
    size 1.0 is about 66 px from snout to tail.  Used for the wave skin and the ocean theme."""
    def P(px, py):
        px = -px if flip else px
        return int(x + px * size), int(y + py * size)

    wag = math.sin(t * 0.3) * 3                    # tail beats up and down
    hull = [P(35, 2.5), P(29, 1.2), P(26, -0.5), P(25, -4), P(22, -8), P(17, -10.5),
            P(10, -11.5), P(0, -11), P(-10, -9), P(-19, -5.5), P(-26, -2 + wag * 0.4),
            P(-29, wag * 0.5),                                       # back, to the tail
            P(-27, 2 + wag * 0.4), P(-19, 3.5), P(-8, 7), P(5, 9), P(17, 8), P(25, 5.5),
            P(29, 5.8), P(35, 5.2)]                                  # belly, back to the beak
    fin = [P(3, -10), P(-2, -16), P(-8, -20), P(-11, -20.5), P(-9, -17), P(-9, -9)]
    flukes = [P(-27, wag * 0.5), P(-33, -3 + wag), P(-39, -6 + wag * 1.3), P(-36, wag),
              P(-39, 5 + wag * 1.3), P(-33, 3 + wag)]
    flipper = [P(10, 6), P(4, 14), P(1, 13.5), P(3, 6)]
    if outline:                                    # a dark rim keeps a small sprite readable
        for poly in (fin, flukes, flipper, hull):
            pygame.draw.polygon(s, outline, poly)
            pygame.draw.polygon(s, outline, poly, max(2, int(3 * size)))
    shade = tuple(max(0, c - 35) for c in body)
    pygame.draw.polygon(s, body, fin)
    pygame.draw.polygon(s, shade, flukes)
    pygame.draw.polygon(s, body, hull)
    pygame.draw.polygon(s, belly, [P(34, 4), P(28, 3.5), P(22, 2), P(12, 2.5), P(0, 3),
                                   P(-12, 2.5), P(-8, 7), P(5, 9), P(17, 8), P(25, 5.5),
                                   P(29, 5.8), P(35, 5.2)])         # pale belly + chin
    pygame.draw.polygon(s, shade, flipper)
    pygame.draw.circle(s, (15, 20, 35), P(20, -3.5), max(1, int(2.2 * size)))
    if size > 0.9:
        pygame.draw.circle(s, (255, 255, 255), P(20.6, -4.2), max(1, int(0.8 * size)))
    pygame.draw.lines(s, tuple(max(0, c - 70) for c in body), False,
                      [P(34, 4), P(28, 3.6), P(24, 2)], max(1, int(1.4 * size)))   # smile


def draw_axocopter(s, a, b, k, t):
    """A little rescue helicopter with a blue axolotl at the controls (64x64 sprite)."""
    hull, trim = (235, 70, 70), (255, 235, 235)
    # tail boom + tail rotor
    pygame.draw.polygon(s, k, [(4, 24), (20, 28), (20, 36), (4, 30)])
    pygame.draw.polygon(s, hull, [(6, 26), (20, 30), (20, 34), (6, 29)])
    tr = max(2, int(7 * abs(math.cos(t * 1.1))))
    pygame.draw.line(s, k, (5, 27 - tr), (5, 27 + tr), 3)
    # skids
    pygame.draw.line(s, k, (22, 44), (24, 50), 3)
    pygame.draw.line(s, k, (42, 44), (40, 50), 3)
    pygame.draw.line(s, k, (14, 51), (52, 51), 3)
    # cabin
    pygame.draw.ellipse(s, k, (13, 18, 42, 30))
    pygame.draw.ellipse(s, hull, (15, 20, 38, 26))
    pygame.draw.rect(s, trim, (17, 36, 26, 4))                 # stripe
    # glass bubble with the axolotl inside
    pygame.draw.ellipse(s, k, (29, 17, 28, 25))
    pygame.draw.ellipse(s, (226, 242, 255), (31, 19, 24, 21))
    pygame.draw.ellipse(s, a, (34, 34, 14, 8))                 # shoulders
    for i, (dx, dy) in enumerate(((-3, -10), (-7, -8), (-10, -4))):   # gills
        w = math.sin(t * 0.25 + i) * 1.2
        tip = (int(39 + dx + w), 28 + dy)
        pygame.draw.line(s, b, (39, 29), tip, 3)
        pygame.draw.circle(s, b, tip, 2)
    pygame.draw.circle(s, k, (43, 30), 8)                      # head (with a dark rim)
    pygame.draw.circle(s, a, (43, 30), 7)
    pygame.draw.circle(s, (255, 255, 255), (46, 28), 3)        # eye
    pygame.draw.circle(s, (10, 15, 35), (47, 28), 2)
    pygame.draw.line(s, (20, 35, 110), (43, 33), (48, 33), 1)  # smile
    pygame.draw.ellipse(s, (255, 255, 255), (48, 21, 5, 3))    # glint on the glass
    # rotor mast + spinning blades
    pygame.draw.line(s, k, (33, 18), (33, 11), 3)
    bw = max(6, int(52 * abs(math.cos(t * 0.9))))
    pygame.draw.rect(s, k, (33 - bw // 2 - 1, 8, bw + 2, 5))
    pygame.draw.rect(s, (220, 225, 235), (33 - bw // 2, 9, bw, 3))
    pygame.draw.circle(s, k, (33, 10), 3)


def draw_crown_cube(s, a, b, k, t):
    """A royal cube wearing a golden crown (64x64 sprite).  The cube body is drawn in the
    same place as the classic cube so it lines up exactly with the hitbox; the crown
    just sits on top."""
    pygame.draw.rect(s, k, (11, 11, 42, 42))
    pygame.draw.rect(s, a, (14, 14, 36, 36))
    pygame.draw.rect(s, b, (14, 14, 36, 4))                    # gold trim
    pygame.draw.rect(s, b, (14, 46, 36, 4))
    pygame.draw.rect(s, k, (21, 24, 7, 8))                     # eyes
    pygame.draw.rect(s, k, (36, 24, 7, 8))
    pygame.draw.rect(s, (255, 255, 255), (22, 25, 3, 3))
    pygame.draw.rect(s, (255, 255, 255), (37, 25, 3, 3))
    pygame.draw.rect(s, k, (25, 38, 14, 3))                    # a confident smile
    pygame.draw.rect(s, k, (22, 35, 4, 3))
    pygame.draw.rect(s, k, (38, 35, 4, 3))
    # the crown, resting on the top edge
    pygame.draw.polygon(s, k, [(14, 13), (14, 2), (21, 7), (27, 0), (32, 6), (37, 0),
                               (43, 7), (50, 2), (50, 13)])
    pygame.draw.polygon(s, b, [(16, 11), (16, 5), (21, 9), (27, 3), (32, 8), (37, 3),
                               (43, 9), (48, 5), (48, 11)])
    pygame.draw.rect(s, (200, 150, 30), (16, 9, 32, 3))
    for x_, c_ in ((22, (255, 60, 80)), (32, (80, 200, 255)), (42, (255, 60, 80))):
        pygame.draw.circle(s, c_, (x_, 10), 2)                   # jewels
    for px_, py_ in ((14, 2), (27, 1), (37, 1), (50, 2)):
        pygame.draw.circle(s, b, (px_, py_), 2)
    if (t // 8) % 6 == 0:                                        # a little sparkle
        pygame.draw.line(s, (255, 255, 255), (32, 0), (32, 4), 1)
        pygame.draw.line(s, (255, 255, 255), (30, 2), (34, 2), 1)


def shade(c, d):
    return tuple(max(0, min(255, v + d)) for v in c)


def draw_crystal_monster(s, a, b, k, t):
    """A spider made of crystal: a faceted gem body, crystal legs and glowing eyes."""
    # crystal legs (two segments each), scuttling
    for i, hx in enumerate((22, 27, 37, 42)):
        ph = t * 0.5 + i * 1.7
        side = -1 if i < 2 else 1
        knee = (hx + side * 16, 25 - max(0.0, math.sin(ph)) * 3)
        foot = (hx + side * 17 + math.sin(ph) * 3, 55 - max(0.0, math.sin(ph)) * 6)
        for p0, p1 in (((hx, 37), knee), (knee, foot)):
            pygame.draw.line(s, k, p0, p1, 6)
            pygame.draw.line(s, b, p0, p1, 3)
        pygame.draw.circle(s, (255, 255, 255), (int(knee[0]), int(knee[1])), 2)
    # crystal shards growing from its back
    for base, tip, base2 in (((20, 24), (15, 5), (26, 20)), ((28, 18), (31, 1), (35, 17)),
                             ((38, 18), (46, 4), (44, 23))):
        pygame.draw.polygon(s, k, [base, tip, base2])
        inner = [(base[0] + 1, base[1]), (tip[0], tip[1] + 3), (base2[0] - 1, base2[1])]
        pygame.draw.polygon(s, b, inner)
        pygame.draw.line(s, (255, 255, 255), (tip[0], tip[1] + 4),
                         ((base[0] + base2[0]) // 2, (base[1] + base2[1]) // 2), 1)
    # faceted gem body
    rim = [(14, 31), (19, 19), (31, 14), (44, 16), (50, 27), (47, 39), (32, 44), (18, 41)]
    pygame.draw.polygon(s, k, [(x + (1 if x > 32 else -1), y + (1 if y > 29 else -1))
                               for x, y in rim])
    c = (32, 29)
    for j in range(len(rim)):
        tri = [c, rim[j], rim[(j + 1) % len(rim)]]
        pygame.draw.polygon(s, shade(a, (35, -10, 15, -25, 25, -5, 10, -30)[j]), tri)
    for v in rim:
        pygame.draw.line(s, shade(a, 60), c, v, 1)                 # facet edges
    # glowing eyes and a jagged grin
    glow = 1 + (t // 6) % 2
    for ex, ey in ((37, 25), (44, 28)):
        pygame.draw.circle(s, (255, 90, 200), (ex, ey), 4 + glow)
        pygame.draw.circle(s, (255, 230, 250), (ex, ey), 2)
    pygame.draw.lines(s, (255, 255, 255), False,
                      [(33, 35), (35, 38), (37, 35), (39, 38), (41, 35), (43, 38), (45, 34)], 2)


def draw_puppy_bot(s, a, b, k, t, running):
    """A golden puppy standing up tall on its hind legs (fills the robot's shape)."""
    dark = shade(a, -55)
    sw = math.sin(t * 0.45) * 7 if running else 0
    lift = 0 if running else 5
    # wagging tail
    wag = math.sin(t * 0.6) * 6
    pygame.draw.lines(s, k, False, [(21, 40), (14, 36), (11 + wag * 0.3, 28 + wag)], 6)
    pygame.draw.lines(s, a, False, [(21, 40), (14, 36), (11 + wag * 0.3, 28 + wag)], 3)
    # hind legs + paws (walk like the robot's legs)
    for hip, fx in (((27, 42), 24 + sw), ((37, 42), 40 - sw)):
        foot = (fx, 49 - lift)
        pygame.draw.line(s, k, hip, foot, 9)
        pygame.draw.line(s, a, hip, foot, 5)
        pygame.draw.ellipse(s, k, (foot[0] - 6, foot[1] - 1, 13, 7))
        pygame.draw.ellipse(s, b, (foot[0] - 5, foot[1], 11, 5))
    # body standing upright, cream belly
    pygame.draw.ellipse(s, k, (18, 20, 28, 28))
    pygame.draw.ellipse(s, a, (20, 22, 24, 24))
    pygame.draw.ellipse(s, b, (26, 26, 14, 18))
    # front paws held up (begging)
    for px, py in ((24, 29), (39, 28)):
        pygame.draw.ellipse(s, k, (px - 4, py - 3, 10, 9))
        pygame.draw.ellipse(s, b, (px - 3, py - 2, 8, 7))
    # collar with a tag
    pygame.draw.rect(s, k, (22, 19, 22, 6), border_radius=3)
    pygame.draw.rect(s, (225, 45, 55), (23, 20, 20, 4), border_radius=2)
    pygame.draw.circle(s, (255, 215, 60), (33, 26), 2)
    # floppy ears hang behind the head, then the head
    flop = math.sin(t * 0.3) * 2 if running else 0
    for ex in (18, 41):
        pygame.draw.ellipse(s, k, (ex - 1, 4 + flop, 11, 18))
        pygame.draw.ellipse(s, dark, (ex, 5 + flop, 9, 16))
    pygame.draw.circle(s, k, (33, 12), 11)
    pygame.draw.circle(s, a, (33, 12), 9)
    pygame.draw.ellipse(s, k, (32, 12, 16, 11))           # snout
    pygame.draw.ellipse(s, b, (33, 13, 14, 9))
    pygame.draw.circle(s, (20, 15, 15), (46, 15), 3)       # nose
    pygame.draw.circle(s, (20, 15, 15), (31, 9), 2)        # eyes
    pygame.draw.circle(s, (20, 15, 15), (38, 8), 2)
    pygame.draw.circle(s, (255, 255, 255), (31, 8), 1)
    pygame.draw.circle(s, (255, 255, 255), (38, 7), 1)
    if running and (t // 8) % 2 == 0:                       # tongue out, panting
        pygame.draw.ellipse(s, (240, 100, 120), (39, 20, 6, 7))


def draw_dog(s, x, y, size=1.0, coat=(200, 150, 90), t=0, flip=False, spots=None):
    """A little puppy running on all fours, side view (for the backyard theme)."""
    def P(px, py):
        return int(x + (-px if flip else px) * size), int(y + py * size)

    def R(v):
        return max(1, int(v * size))
    dark = tuple(max(0, c - 60) for c in coat)
    gallop = math.sin(t * 0.5)
    for lx, ph in ((-10, 0), (-6, 2.4), (8, 1.2), (12, 3.6)):           # legs
        sw = math.sin(t * 0.5 + ph) * 5
        pygame.draw.line(s, dark, P(lx, 3), P(lx + sw, 12), R(3))
    wag = math.sin(t * 0.7) * 4
    pygame.draw.line(s, coat, P(-14, -2), P(-21, -9 + wag), R(3))       # tail
    bx0, by0 = P(-15, -6 + gallop)
    bx1, by1 = P(14, 6 + gallop)
    pygame.draw.ellipse(s, coat, (min(bx0, bx1), min(by0, by1), abs(bx1 - bx0), abs(by1 - by0)))
    if spots:
        pygame.draw.circle(s, spots, P(-4, -2 + gallop), R(4))
    hx, hy = P(16, -7 + gallop)
    pygame.draw.circle(s, coat, (hx, hy), R(7))                          # head
    pygame.draw.ellipse(s, coat, (min(P(18, -6)[0], P(26, -1)[0]), P(18, -6 + gallop)[1],
                                  R(8), R(5)))                           # snout
    pygame.draw.circle(s, (20, 15, 15), P(26, -4 + gallop), R(1.6))      # nose
    pygame.draw.circle(s, (20, 15, 15), P(17, -9 + gallop), R(1.3))      # eye
    ex, ey = P(11, -11 + gallop)
    pygame.draw.ellipse(s, dark, (min(ex, P(16, 0)[0]), ey, R(5), R(9)))  # ear


def special_sprite(s, m, style, a, b, k, t, p):
    """Draw a non-classic skin design.  Returns False if `style` isn't special."""
    if style == "axolotl":                         # the Pink Axolotl ship
        draw_axolotl(s, 33, 35, 0.95, a, b, t)
        return True
    if style == "jet":
        pygame.draw.polygon(s, k, [(4, 34), (16, 16), (60, 26), (16, 40)])
        pygame.draw.polygon(s, a, [(8, 33), (18, 20), (54, 26), (18, 37)])
        pygame.draw.polygon(s, b, [(26, 24), (40, 25), (26, 29)])
        pygame.draw.polygon(s, k, [(10, 34), (2, 46), (16, 38)])
        pygame.draw.circle(s, (255, 180, 60), (5, 31), 3 + (t // 3) % 2)
        return True
    if style == "grin":
        pygame.draw.rect(s, k, (11, 11, 42, 42))
        pygame.draw.rect(s, a, (14, 14, 36, 36))
        pygame.draw.rect(s, k, (21, 21, 6, 6))
        pygame.draw.rect(s, k, (37, 21, 6, 6))
        pygame.draw.rect(s, k, (19, 33, 26, 9))
        pygame.draw.rect(s, (255, 255, 255), (22, 34, 20, 4))
        return True
    if style == "visor":
        pygame.draw.rect(s, k, (11, 11, 42, 42))
        pygame.draw.rect(s, a, (14, 14, 36, 36))
        pygame.draw.rect(s, k, (16, 22, 32, 10))
        pygame.draw.rect(s, b, (18, 24, 28, 6))
        pygame.draw.rect(s, (255, 255, 255), (36, 25, 6, 3))
        pygame.draw.rect(s, b, (20, 40, 24, 5))
        return True
    if style == "swirl":
        pygame.draw.circle(s, k, (32, 32), 19)
        pygame.draw.circle(s, a, (32, 32), 16)
        for r_, c_ in ((13, b), (9, k), (5, b)):
            pygame.draw.arc(s, c_, (32 - r_, 32 - r_, 2 * r_, 2 * r_), 0.4, 4.6, 3)
        return True
    if style == "alien":
        pygame.draw.ellipse(s, k, (18, 8, 28, 30))
        pygame.draw.ellipse(s, (180, 230, 255), (21, 11, 22, 24))
        pygame.draw.ellipse(s, a, (25, 15, 14, 16))
        pygame.draw.ellipse(s, k, (27, 19, 4, 6))
        pygame.draw.ellipse(s, k, (33, 19, 4, 6))
        pygame.draw.ellipse(s, k, (4, 28, 56, 22))
        pygame.draw.ellipse(s, b, (7, 30, 50, 18))
        for i in range(4):
            on = (t // 6 + i) % 2 == 0
            pygame.draw.circle(s, (255, 240, 120) if on else k, (14 + i * 12, 40), 3)
        return True
    if style == "puppy":
        draw_puppy_bot(s, a, b, k, t, getattr(p, "on_ground", True))
        return True
    if style == "crystal":
        draw_crystal_monster(s, a, b, k, t)
        return True
    if style == "crown":
        draw_crown_cube(s, a, b, k, t)
        return True
    if style == "axocopter":
        draw_axocopter(s, a, b, k, t)
        return True
    if style == "dolphin":                         # small dolphin wave
        draw_dolphin(s, 32, 32, 0.62, a, b, t, outline=k)
        return True
    if style == "dart":
        pygame.draw.polygon(s, k, [(58, 32), (10, 16), (22, 32), (10, 48)])
        pygame.draw.polygon(s, a, [(52, 32), (15, 20), (25, 32), (15, 44)])
        pygame.draw.line(s, b, (24, 32), (50, 32), 3)
        return True
    if style == "antenna":
        run = p.on_ground
        sw = math.sin(t * 0.45) * 9 if run else 0
        lift = 0 if run else 6
        for hip, foot in (((27, 40), (24 + sw, 54 - lift)), ((37, 40), (40 - sw, 54 - lift))):
            pygame.draw.line(s, k, hip, foot, 8)
            pygame.draw.line(s, b, hip, foot, 4)
        pygame.draw.rect(s, k, (16, 14, 32, 30), border_radius=6)
        pygame.draw.rect(s, a, (18, 16, 28, 26), border_radius=5)
        pygame.draw.line(s, k, (32, 14), (32, 4), 3)
        pygame.draw.circle(s, b if (t // 10) % 2 else (255, 255, 255), (32, 4), 4)
        pygame.draw.rect(s, k, (24, 22, 18, 9))
        pygame.draw.rect(s, b, (26, 24, 14, 5))
        return True
    if style == "eyes":
        for i, hx in enumerate((24, 29, 35, 40)):
            ph = t * 0.5 + i * 1.7
            fx = hx + (-12 if i < 2 else 12) + math.sin(ph) * 5
            fy = 55 - max(0.0, math.sin(ph)) * 7
            pygame.draw.line(s, k, (hx, 38), (fx, fy), 6)
            pygame.draw.line(s, b, (hx, 38), (fx, fy), 3)
        pygame.draw.ellipse(s, k, (15, 15, 34, 28))
        pygame.draw.ellipse(s, a, (17, 17, 30, 24))
        for ex, ey, r_ in ((25, 25, 4), (38, 25, 4), (31, 20, 3), (31, 31, 3)):
            pygame.draw.circle(s, (255, 255, 255), (ex, ey), r_)
            pygame.draw.circle(s, k, (ex + 1, ey), max(1, r_ - 2))
        return True
    if style == "heli":
        pygame.draw.ellipse(s, k, (16, 24, 34, 24))
        pygame.draw.ellipse(s, a, (18, 26, 30, 20))
        pygame.draw.ellipse(s, (200, 240, 255), (32, 29, 12, 10))
        pygame.draw.line(s, k, (18, 36), (4, 30), 4)
        pygame.draw.line(s, k, (33, 24), (33, 14), 4)
        for ph in (0.0, 1.57):
            bw = max(4, int(44 * abs(math.cos(t * 0.8 + ph))))
            pygame.draw.rect(s, k, (33 - bw // 2 - 1, 10, bw + 2, 6))
            pygame.draw.rect(s, b, (33 - bw // 2, 11, bw, 4))
        return True
    return False


# --------------------------------------------------------------------------
# Sprites (drawn procedurally so there are no asset files)
# --------------------------------------------------------------------------
def make_sprite(p, skin=None):
    s = pygame.Surface((64, 64), pygame.SRCALPHA)
    m, k = p.mode, INK
    a, b = (skin["a"], skin["b"]) if skin else (PRIMARY, SECONDARY)
    t = p.anim
    if skin and skin["style"] != "classic" and special_sprite(s, m, skin["style"], a, b, k, t, p):
        return s

    if m == "cube":
        pygame.draw.rect(s, k, (11, 11, 42, 42))
        pygame.draw.rect(s, a, (14, 14, 36, 36))
        pygame.draw.rect(s, b, (20, 20, 24, 24))
        pygame.draw.rect(s, k, (23, 25, 5, 7))
        pygame.draw.rect(s, k, (36, 25, 5, 7))
        pygame.draw.rect(s, k, (26, 36, 12, 3))

    elif m == "ball":
        pygame.draw.circle(s, k, (32, 32), 19)
        pygame.draw.circle(s, a, (32, 32), 16)
        pygame.draw.circle(s, b, (32, 32), 9)
        pygame.draw.line(s, k, (16, 32), (48, 32), 3)
        pygame.draw.line(s, k, (32, 16), (32, 48), 3)
        pygame.draw.circle(s, k, (32, 32), 9, 2)

    elif m == "ship":
        pygame.draw.polygon(s, k, [(4, 38), (0, 22), (18, 28)])
        pygame.draw.polygon(s, a, [(6, 37), (3, 26), (15, 29)])
        pygame.draw.rect(s, k, (22, 10, 22, 22))
        pygame.draw.rect(s, b, (24, 12, 18, 18))
        pygame.draw.rect(s, k, (34, 17, 4, 6))
        pygame.draw.polygon(s, k, [(6, 38), (12, 27), (46, 27), (62, 37), (50, 49), (12, 49)])
        pygame.draw.polygon(s, a, [(9, 38), (14, 30), (45, 30), (57, 37), (48, 46), (14, 46)])

    elif m == "ufo":
        pygame.draw.ellipse(s, k, (20, 12, 24, 26))
        pygame.draw.ellipse(s, b, (23, 15, 18, 20))
        pygame.draw.ellipse(s, k, (6, 28, 52, 22))
        pygame.draw.ellipse(s, a, (9, 30, 46, 18))
        for i in range(3):
            pygame.draw.circle(s, k, (20 + i * 12, 40), 3)

    elif m == "wave":
        pts = [(52, 32), (16, 14), (27, 32), (16, 50)]
        pygame.draw.polygon(s, k, pts)
        pygame.draw.polygon(s, a, [(46, 32), (21, 19), (29, 32), (21, 45)])

    elif m == "robot":
        run = p.on_ground
        sw = math.sin(t * 0.45) * 9 if run else 0
        lift = 0 if run else 6
        for hip, foot in (((27, 40), (24 + sw, 54 - lift)), ((37, 40), (40 - sw, 54 - lift))):
            pygame.draw.line(s, k, hip, foot, 8)
            pygame.draw.line(s, b, hip, foot, 4)
        pygame.draw.rect(s, k, (17, 22, 30, 22))
        pygame.draw.rect(s, a, (19, 24, 26, 18))
        pygame.draw.rect(s, k, (20, 8, 28, 18))
        pygame.draw.rect(s, b, (22, 10, 24, 14))
        pygame.draw.rect(s, (255, 255, 255), (35, 13, 9, 7))
        pygame.draw.rect(s, k, (40, 14, 4, 5))

    elif m == "spider":
        for i, hx in enumerate((24, 29, 35, 40)):
            ph = t * 0.5 + i * 1.7
            fx = hx + (-12 if i < 2 else 12) + math.sin(ph) * 5
            fy = 55 - max(0.0, math.sin(ph)) * 7
            pygame.draw.line(s, k, (hx, 38), (fx, fy), 6)
            pygame.draw.line(s, b, (hx, 38), (fx, fy), 3)
        pygame.draw.rect(s, k, (17, 17, 30, 26))
        pygame.draw.rect(s, a, (19, 19, 26, 22))
        pygame.draw.rect(s, (255, 255, 255), (24, 24, 7, 7))
        pygame.draw.rect(s, (255, 255, 255), (35, 24, 7, 7))
        pygame.draw.rect(s, k, (27, 26, 3, 4))
        pygame.draw.rect(s, k, (38, 26, 3, 4))

    elif m == "swing":
        pygame.draw.rect(s, k, (20, 24, 26, 24))
        pygame.draw.rect(s, a, (22, 26, 22, 20))
        pygame.draw.rect(s, k, (26, 31, 4, 6))
        pygame.draw.rect(s, k, (36, 31, 4, 6))
        pygame.draw.line(s, k, (33, 24), (33, 15), 4)
        bw = max(4, int(34 * abs(math.cos(t * 0.8))))
        pygame.draw.rect(s, k, (33 - bw // 2 - 1, 11, bw + 2, 7))
        pygame.draw.rect(s, b, (33 - bw // 2, 12, bw, 5))
    return s


# --------------------------------------------------------------------------
# Save data
# --------------------------------------------------------------------------
def load_save():
    for path in (SAVE_PATH, OLD_SAVE_PATH):
        try:
            with open(path) as f:
                data = json.load(f)
                if isinstance(data, dict):
                    return data
        except Exception:
            continue
    return {}


_save_target = [SAVE_PATH]      # where progress is written (changes with the account)


def write_save(data):
    try:
        path = _save_target[0]
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            json.dump(data, f)
    except Exception:
        pass


def write_json(path, data):
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            json.dump(data, f)
        return True
    except Exception:
        return False


# --------------------------------------------------------------------------
# Accounts (stored on this computer).  Passwords are never saved - only a salted,
# slow hash of them, so nobody can read them back out of the file.
# --------------------------------------------------------------------------
def account_key(name):
    return " ".join(name.split()).lower()


ONLINE_SUBDIR = "PythonDashAccounts"     # made inside the shared online folder


def online_root(folder):
    """Where accounts live inside a shared (Google Drive / Dropbox / OneDrive) folder."""
    return os.path.join(folder, ONLINE_SUBDIR) if folder else None


def _read_local_accounts():
    try:
        with open(ACCOUNTS_PATH) as f:
            a = json.load(f)
        if isinstance(a, dict) and isinstance(a.get("users"), dict):
            a.setdefault("current", None)
            return a
    except Exception:
        pass
    return {"users": {}, "current": None}


def _user_ok(u):
    return isinstance(u, dict) and all(isinstance(u.get(k), str) for k in
                                       ("name", "salt", "hash", "file"))


def user_file_name(key):
    """One file per account in the online folder.  Named from the (lower-case) name in
    hex, so two different names can never end up as the same file."""
    return key.encode("utf-8").hex() + ".json"


def load_accounts(root=None):
    """Accounts on this computer (root=None) or in the shared online folder."""
    local = _read_local_accounts()
    if not root:
        return local
    users = {}
    try:
        names = os.listdir(os.path.join(root, "users"))
    except OSError:
        names = []
    for fn in names:
        if not fn.endswith(".json"):
            continue
        try:
            with open(os.path.join(root, "users", fn)) as f:
                u = json.load(f)
        except Exception:
            continue
        if _user_ok(u):
            users[account_key(u["name"])] = u
    return {"users": users, "current": local.get("current"), "online": True}


def store_current(key):
    """Who is signed in is remembered per computer, never in the shared folder."""
    local = _read_local_accounts()
    local["current"] = key
    write_json(ACCOUNTS_PATH, local)


def save_new_account(accounts, key, root=None):
    """Write a just-created account.  In the online folder the file is created only if it
    doesn't exist yet, so two people can't grab the same name.  Error message or None."""
    user = accounts["users"][key]
    if not root:
        local = _read_local_accounts()
        local["users"][key] = user
        return None if write_json(ACCOUNTS_PATH, local) else "Couldn't save the account"
    path = os.path.join(root, "users", user_file_name(key))
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        return "That name is taken - pick another one"
    except OSError:
        return "Can't reach the accounts folder"
    with os.fdopen(fd, "w") as f:
        json.dump(user, f)
    return None


def hash_password(password, salt):
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 120000).hex()


def account_name_problem(name):
    """Why a new account name isn't allowed (or None if it's fine)."""
    name = " ".join(name.split())
    if len(name) < ACCOUNT_NAME_MIN:
        return "Names need at least %d characters" % ACCOUNT_NAME_MIN
    if len(name) > ACCOUNT_NAME_MAX:
        return "Names can be at most %d characters" % ACCOUNT_NAME_MAX
    if not all(ch.isalnum() or ch in " -_" for ch in name):
        return "Names can only use letters, numbers, spaces, - and _"
    return None


def create_account(accounts, name, password):
    """Add an account.  Returns an error message, or None on success."""
    name = " ".join(name.split())
    problem = account_name_problem(name)
    if problem:
        return problem
    if account_key(name) in accounts["users"]:
        return "That name is taken - pick another one"
    if len(password) < PASSWORD_MIN:
        return "Passwords need at least %d characters" % PASSWORD_MIN
    salt = os.urandom(16)
    accounts["users"][account_key(name)] = {
        "name": name, "salt": salt.hex(), "hash": hash_password(password, salt),
        "file": slugify(name) + "-" + salt.hex()[:6] + ".json"}
    return None


def check_login(accounts, name, password):
    """The account if the name and password match, else None."""
    u = accounts["users"].get(account_key(name))
    if not u:
        hash_password(password, b"0" * 16)        # same delay either way
        return None
    try:
        good = hmac.compare_digest(hash_password(password, bytes.fromhex(u["salt"])), u["hash"])
    except (ValueError, KeyError):
        return None
    return u if good else None


def account_save_path(user, root=None):
    base = os.path.join(root, "progress") if root else ACCOUNT_DIR
    return os.path.join(base, os.path.basename(user["file"]))




# --------------------------------------------------------------------------
# Online levels + music, from the GitHub repo (REPO).  Everything here runs on a
# background thread so the game never freezes while it downloads.
# --------------------------------------------------------------------------
def http_get(url, timeout=15):
    req = urllib.request.Request(url, headers={"User-Agent": "PythonDash"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def raw_url(path, name):
    return "https://raw.githubusercontent.com/%s/%s/%s/%s" % (
        REPO, REPO_BRANCH, path, urllib.parse.quote(name))


def repo_list(path, exts):
    """[(file name, download url)] of the files in a folder of the repo.  Uses GitHub's
    API, and if that's unavailable (it allows 60 lookups an hour) reads the repo page."""
    try:
        data = json.loads(http_get("https://api.github.com/repos/%s/contents/%s?ref=%s"
                                   % (REPO, path, REPO_BRANCH)))
        if isinstance(data, list):
            return sorted(((f["name"], f.get("download_url") or raw_url(path, f["name"]))
                           for f in data if f.get("type") == "file"
                           and f["name"].lower().endswith(exts)), key=lambda t: t[0].lower())
    except Exception:
        pass
    html = http_get("https://github.com/%s/tree/%s/%s" % (REPO, REPO_BRANCH, path)).decode(
        "utf-8", "ignore")
    names = set()
    for m in __import__("re").finditer(r'"name":"([^"\\]+)"', html):
        n = m.group(1)
        if n.lower().endswith(exts):
            names.add(n)
    return sorted(((n, raw_url(path, n)) for n in names), key=lambda t: t[0].lower())


def fetch_online_levels(out):
    """Fill out["levels"] with what's online: name, author, modes and the raw file."""
    try:
        found = []
        for fn, url in repo_list("levels", (".json",))[:80]:
            try:
                raw = http_get(url)
                j = json.loads(raw.decode("utf-8"))
                j.pop("music_data", None)                 # (just a preview for now)
                d = LevelData.from_json(j)
                found.append({"file": fn, "raw": raw, "name": d.name, "author": d.author,
                              "modes": d.mode_list(), "objects": d.object_count(),
                              "music": j.get("music") or ""})
            except Exception:
                continue
        out["levels"] = found
        out["status"] = "ok"
    except Exception as ex:
        out["status"] = "error"
        out["err"] = "Couldn't reach GitHub (%s)" % (getattr(ex, "reason", None) or ex)


def fetch_online_music(out):
    try:
        out["songs"] = repo_list("music", MUSIC_EXTS)
        out["status"] = "ok"
    except Exception as ex:
        out["status"] = "error"
        out["err"] = "Couldn't reach GitHub (%s)" % (getattr(ex, "reason", None) or ex)


def download_song(name, url=None):
    """Download a song from the repo into the music folder (kept under its own name)."""
    dest = os.path.join(MUSIC_DIR, os.path.basename(name))
    if os.path.isfile(dest):
        return dest
    data = http_get(url or raw_url("music", name), timeout=60)
    os.makedirs(MUSIC_DIR, exist_ok=True)
    with open(dest, "wb") as f:
        f.write(data)
    return dest
# --------------------------------------------------------------------------
# Level editor
# --------------------------------------------------------------------------
_DIRS = ("tl", "tr", "bl", "br")
SLOPE_ROWS = [[("ramp_" + d, "1:1 " + d.upper()) for d in _DIRS]
              + [("gramp_" + d, "1:2 " + d.upper()) for d in _DIRS],
              [("sramp_" + d, "2:1 " + d.upper()) for d in _DIRS]]
TAB_DEFS = {
    # layer -> [(tab name, [row 1 tools, row 2 tools]), ...]   tool = (id, label)
    "main": [
        ("OBJECTS", [[("block", "BLOCK"), ("spike", "SPIKE ^"), ("spike_d", "SPIKE v"),
                      ("spike_l", "SPIKE <"), ("spike_r", "SPIKE >"), ("coin", "COIN"),
                      ("text", "TEXT")], []]),
        ("SLOPES", SLOPE_ROWS),
        ("PADS & ORBS", [[("pad", "PAD"), ("dpad", "PAD v"), ("orb", "ORB"), ("dorb", "ORB v"),
                          ("ipad", "I-PAD"), ("idpad", "I-PAD v"), ("iorb", "I-ORB"),
                          ("idorb", "I-ORB v")], []]),
        ("PORTALS", [[("portal:" + m, m.upper()) for m in MODE_ORDER],
                     [("portal:miniwave", "MINI WAVE"), ("finish", "FINISH"),
                      ("grav_d", "GRAV v"), ("grav_u", "GRAV ^")]]),
        ("SPEED", [[("speed:%g" % v, "%gx" % v) for v in SPEED_VALUES], []]),
        ("TRIGGERS", [[("trig:move", "MOVE"), ("trig:reveal", "REVEAL"),
                       ("light:flicker_on", "FLICK ON"), ("light:flicker_off", "FLICK OFF"),
                       ("light:close_circle", "CLOSE"),
                       ("light:open_circle", "OPEN")], []]),
    ],
    "bg": [
        ("BACKGROUND", [[("block", "BLOCK"), ("spike", "SPIKE ^"), ("spike_d", "SPIKE v"),
                         ("spike_l", "SPIKE <"), ("spike_r", "SPIKE >")], []]),
        ("BG SLOPES", SLOPE_ROWS),
    ],
}
TOOL_HELP = {
    "block": "Solid block", "spike": "Spike", "spike_d": "Upside-down spike",
    "spike_l": "Spike pointing left", "spike_r": "Spike pointing right",
    "portal:miniwave": "Mini wave portal: a smaller wave that moves twice as steeply",
    "ramp_tl": "Ramp: top-left half", "ramp_tr": "Ramp: top-right half",
    "ramp_bl": "Ramp: bottom-left half (downhill)", "ramp_br": "Ramp: bottom-right half (uphill)",
    "coin": "Coin - collect them all in normal mode", "text": "Text box - click to type",
    "trig:move": "Move trigger - moves a group when you pass it",
    "trig:reveal": "Reveal trigger - makes a group appear (or disappear)",
    "light:flicker_on": "Light trigger - lights flicker back on",
    "light:flicker_off": "Light trigger - lights flicker off",
    "light:close_circle": "Light trigger - darkness closes in to a circle around you",
    "light:open_circle": "Light trigger - the circle of light opens back up",
    "select": "Select: drag an area, then Ctrl+C / X / V, DELETE, G = set group",
    "color": "Colour for new background blocks (with a selection: recolours it)."
             "  Right-click to edit",
    "objcolor": "Colour for blocks, spikes and ramps (with a selection: recolours it)."
                "  Right-click to edit",
    "editcolor": "Change the selected colour - everything using it updates",
    "theme": "Background theme for the whole level (try UNDERWATER)",
    "erase": "Eraser (right mouse button erases with any tool)",
    "delete": "Delete the selection - or press DELETE / BACKSPACE over any object",
    "copy": "Copy the selection (Ctrl/Cmd+C)", "cut": "Cut the selection (Ctrl/Cmd+X)",
    "paste": "Paste - then click where it goes (Ctrl/Cmd+V)",
}
# tool -> (cell kind, flip flag).  For pads and orbs the flag means "invisible".
_WHERE = {"tl": "ceiling, low on the left", "tr": "ceiling, low on the right",
          "bl": "floor, going down", "br": "floor, going up"}
for _d in _DIRS:
    TOOL_HELP["ramp_" + _d] = "45-degree slope (1 block) - " + _WHERE[_d]
    TOOL_HELP["gramp_" + _d] = "Gentle slope 1/2 (2 wide, 1 tall) - " + _WHERE[_d]
    TOOL_HELP["sramp_" + _d] = "Steep slope 2 (1 wide, 2 tall) - " + _WHERE[_d]
TOOL_CELL = {
    "block": ("block", False), "spike": ("spike", False), "spike_d": ("spike", True),
    "spike_l": ("spike_l", False), "spike_r": ("spike_r", False),
    "pad": ("pad", False), "dpad": ("dpad", False), "orb": ("orb", False),
    "dorb": ("dorb", False),
    "ipad": ("pad", True), "idpad": ("dpad", True), "iorb": ("orb", True),
    "idorb": ("dorb", True), "coin": ("coin", False),
}
for _k in RAMPS:
    TOOL_CELL[_k] = (_k, False)
CELL_TOOLS = tuple(TOOL_CELL)
GHOST_BASE = {"ipad": "pad", "idpad": "dpad", "iorb": "orb", "idorb": "dorb"}
PORTAL_MIN_COL = 4
TRIG_COLOR = {"move": (110, 255, 160), "reveal": (255, 150, 255), "light": (255, 235, 120)}

TOP_BUTTONS = {            # name -> rect (top bar)
    "back": pygame.Rect(6, 5, 54, 30),
    "save": pygame.Rect(64, 5, 56, 30),
    "name": pygame.Rect(124, 5, 136, 30),
    "desc": pygame.Rect(264, 5, 50, 30),
    "start": pygame.Rect(318, 5, 124, 30),
    "music": pygame.Rect(446, 5, 66, 30),
    "group": pygame.Rect(516, 5, 84, 30),
    "layer": pygame.Rect(604, 5, 76, 30),
    "play": pygame.Rect(684, 5, 50, 30),
    "here": pygame.Rect(738, 5, 88, 30),
}
SIDE_BUTTONS = {
    "select": pygame.Rect(778, FLOOR + 31, 58, 28),
    "erase": pygame.Rect(838, FLOOR + 31, 56, 28),
    "delete": pygame.Rect(896, FLOOR + 31, 58, 28),
    "copy": pygame.Rect(778, FLOOR + 62, 58, 28),
    "cut": pygame.Rect(838, FLOOR + 62, 56, 28),
    "paste": pygame.Rect(896, FLOOR + 62, 58, 28),
}


def swatch_x0(layer):
    """Background mode: swatches start at the left.  Main layer (OBJECTS tab): after TEXT."""
    return 8


def swatch_rect(i, layer="bg"):
    return pygame.Rect(swatch_x0(layer) + i * 42, FLOOR + 62, 38, 28)


def color_edit_rect(layer):
    return pygame.Rect(swatch_x0(layer) + COLOR_SLOTS * 42 + 4, FLOOR + 62, 92, 28)


THEME_BUTTON = pygame.Rect(color_edit_rect("bg").right + 8, FLOOR + 62, 168, 28)


def slot_color(palette, color, acc):
    """The real colour of colour slot `color` (0 = the game mode's accent)."""
    if color and 0 < color < COLOR_SLOTS:
        return tuple(palette[color - 1])
    return tuple(acc)


def bg_fill(acc, color, palette=DEFAULT_PALETTE):
    """Colour a background-layer object is drawn in."""
    if color and 0 < color < COLOR_SLOTS:
        return tuple(int(v * 0.62 + 12) for v in palette[color - 1])
    return tuple(int(a * 0.35 + 10) for a in acc)


def pal_rect(i, row, n=8):
    """Tool button i in a palette row of n tools (rows with more than 8 get narrower)."""
    step = min(96, 768 // max(1, n))
    return pygame.Rect(8 + i * step, FLOOR + 31 + row * 31, step - 4, 28)


def etab_rect(i):
    return pygame.Rect(8 + i * 112, FLOOR + 5, 108, 22)


def trigger_fields(cfg):
    """The editable fields of a trigger: (key, label, kind, extra)."""
    t = cfg["type"]
    if t == "move":
        return [("group", "Group", "int", (1, GROUP_MAX, 1)),
                ("dx", "Move X (blocks, + = right)", "float", (-200, 200, 0.5)),
                ("dy", "Move Y (blocks, + = up)", "float", (-20, 20, 0.5)),
                ("time", "Time (seconds)", "float", (0, 10, 0.1)),
                ("ease", "Easing", "choice", [(True, "Smooth"), (False, "Linear")])]
    if t == "reveal":
        return [("group", "Group", "int", (1, GROUP_MAX, 1)),
                ("show", "Action", "choice", [(True, "Reveal (appear)"),
                                              (False, "Hide (disappear)")])]
    return [("effect", "Effect", "choice", [(e, LIGHT_NAMES[e]) for e in LIGHT_EFFECTS]),
            ("radius", "Circle radius (blocks)", "float", (1, 12, 0.5)),
            ("time", "Time (seconds)", "float", (0, 10, 0.1))]


class Editor:
    def __init__(self, game, data, named):
        self.game = game
        self.data = data
        self.named = named
        self.cam = 0.0
        self.tool = "block"
        self.layer = "main"          # "main" or "bg" (Edit Background mode)
        self.tab = {"main": 0, "bg": 0}
        self.group = 0               # group given to newly placed objects (0 = none)
        self.bg_color = 0            # colour for new background blocks (0 = automatic)
        self.obj_color = 0           # colour for new main-layer blocks / spikes / ramps
        self.cedit = None            # colour slot being edited: {"slot", "rgb", "sel"}
        self.undo, self.redo = [], []
        self.drag = None
        self.last_cell = None
        self.dirty = False
        self.toast, self.toast_t = "", 0
        self.leave_armed = 0
        self.modal = None            # None | save | rename | desc | text | group | music | props
        self.modal_text = ""
        self.modal_cell = None
        self.form = None             # trigger settings being edited
        self.sel = None              # selection (c0, r0, c1, r1), inclusive
        self.sel_anchor = None
        self.clip = None             # copied objects
        self.pasting = False
        self.preview = False         # music preview playing
        self.songs = []              # song picker: files in the songs folder
        self.song_sel = 0
        self.song_scroll = 0
        self.song_scan = 0
        self.song_online = False     # showing the songs in the GitHub repo
        self.song_dl = None          # song being downloaded
        self.song_dl_done = None     # set by the download thread when it finishes

    # ---- helpers -----------------------------------------------------------
    def say(self, msg):
        self.toast, self.toast_t = msg, 150

    def sections(self):
        return [(self.data.start_mode, 0)] + [(m, c) for c, m in sorted(self.data.portals.items())]

    def tabs(self):
        return TAB_DEFS[self.layer]

    def cur_tab(self):
        return self.tabs()[self.tab[self.layer]][1]

    def layer_cells(self):
        return self.data.cells if self.layer == "main" else self.data.bg

    def push_undo(self):
        self.undo.append(self.data.snapshot())
        if len(self.undo) > 100:
            self.undo.pop(0)
        self.redo.clear()

    def do_undo(self):
        if self.undo:
            self.redo.append(self.data.snapshot())
            self.data.restore(self.undo.pop())
            self.dirty = True

    def do_redo(self):
        if self.redo:
            self.undo.append(self.data.snapshot())
            self.data.restore(self.redo.pop())
            self.dirty = True

    def cell_at(self, x, y):
        col = int((x + self.cam) // B)
        row = (FLOOR - 1 - y) // B
        return col, row

    def set_tool(self, tool):
        self.tool = tool
        self.pasting = False

    def set_layer(self, layer):
        self.layer = layer
        self.sel = None
        self.pasting = False
        tools = [t for row in self.cur_tab() for t, _ in row]
        if self.tool not in ("select", "erase") and self.tool not in tools:
            self.tool = tools[0]
        self.say("Editing the BACKGROUND layer (decoration only)" if layer == "bg"
                 else "Editing the main layer")

    # ---- editing -----------------------------------------------------------
    def place(self, col, row, first):
        d, tool = self.data, self.tool
        if col < 0 or col >= MAX_COLS or not (0 <= row < ROWS):
            return
        if tool == "erase":
            self.erase(col, row, first)
        elif tool in CELL_TOOLS:
            if col < SAFE_COLS:
                return
            kind, flip = TOOL_CELL[tool]
            if self.layer == "bg":
                self.data.bg[(col, row)] = (kind, flip, self.group, self.bg_color)
            else:
                colr = self.obj_color if kind in COLORABLE else 0
                self.data.cells[(col, row)] = (kind, flip, self.group, colr)
        elif not first:
            return
        elif tool == "text":
            old = d.texts.get((col, row))
            self.open_modal("text", old[0] if old else "", (col, row))
        elif tool.startswith("trig:") or tool.startswith("light:"):
            if (col, row) not in d.triggers:
                d.triggers[(col, row)] = default_trigger(tool, self.group)
            self.open_props((col, row))
        elif tool in ("grav_d", "grav_u"):
            if col >= SAFE_COLS:
                d.gravs[col] = (tool == "grav_u")
        elif tool == "finish":
            if col >= SAFE_COLS:
                d.finish = col
        elif tool.startswith("speed:"):
            if col >= SAFE_COLS:
                d.speeds[col] = float(tool.split(":")[1])
        elif tool.startswith("portal:"):
            if col >= PORTAL_MIN_COL:
                d.portals[col] = tool.split(":")[1]

    @staticmethod
    def covering(cells, col, row):
        """The cell key of an object covering (col, row) - big slopes span 2 cells."""
        if (col, row) in cells:
            return (col, row)
        for c, r in ((col - 1, row), (col, row - 1)):
            v = cells.get((c, r))
            if v and v[0] in RAMPS:
                w, h = ramp_size(v[0])
                if col < c + w and row < r + h:
                    return (c, r)
        return None

    def erase(self, col, row, first):
        d = self.data
        if self.layer == "bg":
            k = self.covering(d.bg, col, row)
            if k:
                d.bg.pop(k, None)
            return
        if (col, row) in d.triggers:
            del d.triggers[(col, row)]
        elif (col, row) in d.texts:
            del d.texts[(col, row)]
        elif self.covering(d.cells, col, row):
            del d.cells[self.covering(d.cells, col, row)]
        elif first:                       # column objects only on the first click
            if col in d.portals:
                del d.portals[col]
            elif col in d.gravs:
                del d.gravs[col]
            elif col in d.speeds:
                del d.speeds[col]
            elif d.finish == col:
                d.finish = None

    def apply_mouse(self, x, y, button, first):
        col, row = self.cell_at(x, y)
        if (col, row) == self.last_cell and not first:
            return
        self.last_cell = (col, row)
        if button == "paint":
            self.place(col, row, first)
        else:
            self.erase(col, row, first)

    def end_stroke(self):
        if self.drag in ("paint", "erase"):
            if self.undo and self.undo[-1] == self.data.snapshot():
                self.undo.pop()
            else:
                self.dirty = True
        self.drag = None
        self.last_cell = None

    # ---- selection, copy & paste -------------------------------------------
    def sel_rect(self):
        if not self.sel:
            return None
        c0, r0, c1, r1 = self.sel
        return min(c0, c1), min(r0, r1), max(c0, c1), max(r0, r1)

    def in_sel(self, c, r):
        c0, r0, c1, r1 = self.sel_rect()
        return c0 <= c <= c1 and r0 <= r <= r1

    def selected(self):
        """Everything in the selection on the current layer, as clipboard items
        (kind, col, row, value)."""
        if not self.sel:
            return []
        d = self.data
        c0, r0, c1, r1 = self.sel_rect()
        out = []
        if self.layer == "bg":
            out += [("bg", c, r, v) for (c, r), v in d.bg.items() if self.in_sel(c, r)]
            return out
        out += [("cell", c, r, v) for (c, r), v in d.cells.items() if self.in_sel(c, r)]
        out += [("text", c, r, v) for (c, r), v in d.texts.items() if self.in_sel(c, r)]
        out += [("trig", c, r, dict(v)) for (c, r), v in d.triggers.items()
                if self.in_sel(c, r)]
        whole = r0 == 0 and r1 == ROWS - 1      # column objects need the full height
        if whole:
            out += [("grav", c, 0, v) for c, v in d.gravs.items() if c0 <= c <= c1]
            out += [("speed", c, 0, v) for c, v in d.speeds.items() if c0 <= c <= c1]
            out += [("portal", c, 0, v) for c, v in d.portals.items() if c0 <= c <= c1]
        return out

    def remove_items(self, items):
        d = self.data
        for kind, c, r, _ in items:
            if kind == "bg":
                d.bg.pop((c, r), None)
            elif kind == "cell":
                d.cells.pop((c, r), None)
            elif kind == "text":
                d.texts.pop((c, r), None)
            elif kind == "trig":
                d.triggers.pop((c, r), None)
            elif kind == "grav":
                d.gravs.pop(c, None)
            elif kind == "speed":
                d.speeds.pop(c, None)
            elif kind == "portal":
                d.portals.pop(c, None)

    def copy_sel(self, cut=False):
        items = self.selected()
        if not items:
            self.say("Nothing selected - use SELECT (V) and drag over some objects")
            return
        c0, r0, c1, r1 = self.sel_rect()
        self.clip = {"w": c1 - c0 + 1, "h": r1 - r0 + 1,
                     "items": [(k, c - c0, r - r0, copy.deepcopy(v)) for k, c, r, v in items]}
        if cut:
            self.push_undo()
            self.remove_items(items)
            self.dirty = True
            self.say("Cut %d objects - Ctrl+V to paste" % len(items))
        else:
            self.say("Copied %d objects - Ctrl+V to paste" % len(items))

    def start_paste(self):
        if not self.clip:
            self.say("The clipboard is empty - select an area and press Ctrl+C first")
            return
        self.tool = "select"
        self.pasting = True
        self.say("Click to paste (the bottom-left corner goes where you click)   ESC cancels")

    def paste_at(self, col, row):
        d = self.data
        self.push_undo()
        n = 0
        for kind, dc, dr, v in self.clip["items"]:
            c, r = col + dc, row + dr
            if not (0 <= r < ROWS and 0 <= c < MAX_COLS):
                continue
            v = copy.deepcopy(v)
            if kind in ("cell", "bg"):
                if c < SAFE_COLS:
                    continue
                (d.cells if kind == "cell" else d.bg)[(c, r)] = v
            elif kind == "text":
                d.texts[(c, r)] = v
            elif kind == "trig":
                d.triggers[(c, r)] = v
            elif kind == "grav" and c >= SAFE_COLS:
                d.gravs[c] = v
            elif kind == "speed" and c >= SAFE_COLS:
                d.speeds[c] = v
            elif kind == "portal" and c >= PORTAL_MIN_COL:
                d.portals[c] = v
            else:
                continue
            n += 1
        self.sel = (col, row, col + self.clip["w"] - 1, min(ROWS - 1, row + self.clip["h"] - 1))
        self.pasting = False
        self.dirty = True
        self.say("Pasted %d objects" % n)

    def delete_sel(self):
        items = self.selected()
        if items:
            self.push_undo()
            self.remove_items(items)
            self.dirty = True
            self.say("Deleted %d objects" % len(items))
        else:
            where = "background" if self.layer == "bg" else "main"
            self.say("Nothing on the %s layer in the selection" % where)

    def delete_key(self):
        """DELETE / BACKSPACE: remove the selection, or else whatever is under the mouse."""
        if self.sel:
            self.delete_sel()
            return
        mx, my = pygame.mouse.get_pos()
        if not (CEIL <= my < FLOOR):
            self.say("Select an area (V) or point at an object, then press DELETE")
            return
        col, row = self.cell_at(mx, my)
        before = self.data.snapshot()
        self.erase(col, row, True)
        if self.data.snapshot() != before:
            self.undo.append(before)
            self.redo.clear()
            self.dirty = True
        else:
            self.say("Nothing here to delete")

    def group_sel(self):
        items = [it for it in self.selected() if it[0] in ("cell", "bg", "text")]
        if not items:
            self.say("Select some objects first (SELECT tool, V)")
            return
        self.push_undo()
        d, g = self.data, self.group
        for kind, c, r, v in items:
            if kind == "cell":
                d.cells[(c, r)] = (v[0], v[1], g, v[3])
            elif kind == "bg":
                d.bg[(c, r)] = (v[0], v[1], g, v[3])
            else:
                d.texts[(c, r)] = (v[0], g)
        self.dirty = True
        self.say("%d objects %s" % (len(items), "put in group %d" % g if g
                                     else "removed from their groups"))

    # ---- saving ------------------------------------------------------------
    def save(self):
        if not self.named and self.data.path is None:
            self.open_modal("save", self.data.name)
            return
        self.write()

    def write(self):
        d = self.data
        try:
            os.makedirs(LEVEL_DIR, exist_ok=True)
            if d.path is None:
                d.path = unique_level_path(d.name)
            with open(d.path, "w") as f:
                json.dump(d.to_json(), f)
            self.dirty = False
            self.named = True
            self.say("Saved: " + os.path.basename(d.path))
        except OSError as ex:
            self.say("Save failed: %s" % (ex.strerror or ex))

    def request_leave(self):
        if self.dirty and self.leave_armed <= 0:
            self.leave_armed = 200
            self.say("Unsaved changes!  Press BACK/ESC again to leave, or SAVE")
            return
        self.stop_preview()
        self.game.go_mylevels()

    # ---- music -------------------------------------------------------------
    def attach_music(self, path):
        path = path.strip().strip('"').strip("'")
        if path.startswith("file://"):
            path = path[7:]
        path = os.path.expanduser(path)
        if not os.path.isfile(path):
            self.say("File not found: " + os.path.basename(path))
            return False
        if os.path.splitext(path)[1].lower() not in MUSIC_EXTS:
            self.say("Songs must be " + " / ".join(MUSIC_EXTS) + " files")
            return False
        try:
            name = store_music(path)
        except OSError:
            self.say("Couldn't copy the song")
            return False
        self.push_undo()
        self.data.music = name
        self.dirty = True
        self.say("Song attached: " + os.path.basename(path))
        return True

    def toggle_preview(self):
        if self.preview:
            self.stop_preview()
            return
        path = music_path(self.data.music)
        if not path:
            self.say("No song picked - click SONGS to choose one")
            return
        sx = sorted(self.data.speeds)
        t = time_to_x([c * B + B // 2 for c in sx], [self.data.speeds[c] for c in sx],
                      self.cam + CAM_OFFSET)
        if self.game.play_music(path, t, force=True):
            self.preview = True
            self.say("Music preview from here - M to stop")

    def stop_preview(self):
        if self.preview:
            self.game.stop_music()
            self.preview = False

    # ---- modals ------------------------------------------------------------
    def open_modal(self, kind, text, cell=None):
        self.modal, self.modal_text, self.modal_cell = kind, text, cell
        self.drag = None

    def open_props(self, cell):
        self.form = {"cell": cell, "cfg": dict(self.data.triggers[cell]), "sel": 0, "typing": ""}
        self.modal = "props"
        self.drag = None

    def close_props(self, keep=True):
        f = self.form
        if keep and f:
            self.commit_typing()
            cfg = clean_trigger(f["cfg"])
            if cfg and cfg != self.data.triggers.get(f["cell"]):
                self.push_undo()
                self.data.triggers[f["cell"]] = cfg
                self.dirty = True
        self.modal, self.form = None, None

    def commit_typing(self):
        f = self.form
        if not f or not f["typing"]:
            return
        key, _, kind, ext = trigger_fields(f["cfg"])[f["sel"]]
        try:
            v = float(f["typing"])
            lo, hi, _ = ext
            v = max(lo, min(hi, v))
            f["cfg"][key] = int(round(v)) if kind == "int" else round(v, 2)
        except ValueError:
            pass
        f["typing"] = ""

    def adjust(self, i, d):
        f = self.form
        key, _, kind, ext = trigger_fields(f["cfg"])[i]
        if kind == "choice":
            vals = [v for v, _ in ext]
            j = vals.index(f["cfg"][key]) if f["cfg"][key] in vals else 0
            f["cfg"][key] = vals[(j + d) % len(vals)]
        else:
            lo, hi, step = ext
            v = f["cfg"][key] + d * step
            v = max(lo, min(hi, v))
            f["cfg"][key] = int(round(v)) if kind == "int" else round(v, 2)
        f["typing"] = ""

    def props_geom(self):
        n = len(trigger_fields(self.form["cfg"]))
        box = pygame.Rect(0, 0, 640, 120 + n * 40)
        box.center = (W // 2, H // 2)
        rows = []
        for i in range(n):
            r = pygame.Rect(box.x + 20, box.y + 62 + i * 40, box.w - 40, 34)
            rows.append((r, pygame.Rect(r.right - 186, r.y + 3, 30, 28),
                         pygame.Rect(r.right - 34, r.y + 3, 30, 28)))
        return box, rows

    def props_delete_rect(self):
        box, _ = self.props_geom()
        return pygame.Rect(box.right - 124, box.y + 14, 104, 32)

    def delete_trigger(self):
        self.push_undo()
        self.data.triggers.pop(self.form["cell"], None)
        self.dirty = True
        self.modal, self.form = None, None
        self.say("Trigger deleted")

    def props_event(self, e):
        f = self.form
        fields = trigger_fields(f["cfg"])
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            box, rows = self.props_geom()
            if self.props_delete_rect().collidepoint(e.pos):
                self.delete_trigger()
                return
            for i, (r, minus, plus) in enumerate(rows):
                if minus.collidepoint(e.pos):
                    self.commit_typing()
                    f["sel"] = i
                    self.adjust(i, -1)
                elif plus.collidepoint(e.pos):
                    self.commit_typing()
                    f["sel"] = i
                    self.adjust(i, 1)
                elif r.collidepoint(e.pos):
                    self.commit_typing()
                    f["sel"] = i
            if not box.collidepoint(e.pos):
                self.close_props()
            return
        if e.type != pygame.KEYDOWN:
            return
        k = e.key
        if k == pygame.K_ESCAPE:
            self.close_props(keep=False)
        elif k in (pygame.K_RETURN, pygame.K_KP_ENTER):
            if f["typing"]:
                self.commit_typing()
            else:
                self.close_props()
        elif k == pygame.K_DELETE or (k == pygame.K_BACKSPACE and not f["typing"]):
            self.delete_trigger()               # (Backspace is the Mac's delete key)
        elif k in (pygame.K_UP, pygame.K_w):
            self.commit_typing()
            f["sel"] = (f["sel"] - 1) % len(fields)
        elif k in (pygame.K_DOWN, pygame.K_s, pygame.K_TAB):
            self.commit_typing()
            f["sel"] = (f["sel"] + 1) % len(fields)
        elif k in (pygame.K_LEFT, pygame.K_a):
            self.adjust(f["sel"], -1)
        elif k in (pygame.K_RIGHT, pygame.K_d):
            self.adjust(f["sel"], 1)
        elif k == pygame.K_BACKSPACE:
            f["typing"] = f["typing"][:-1]
        elif e.unicode and e.unicode in "0123456789.-" and fields[f["sel"]][2] != "choice":
            if len(f["typing"]) < 7:
                f["typing"] += e.unicode

    # ---- song picker ---------------------------------------------------------
    SONG_ROWS = 7

    def open_songs(self):
        self.songs = list_songs()
        names = [""] + self.songs
        self.song_sel = names.index(self.data.music) if self.data.music in names else 0
        self.song_scroll = max(0, self.song_sel - self.SONG_ROWS + 1)
        self.modal = "songs"
        self.drag = None

    def rescan_songs(self):
        cur = ([""] + self.songs)[self.song_sel] if self.song_sel <= len(self.songs) else ""
        self.songs = list_songs()
        names = [""] + self.songs
        self.song_sel = names.index(cur) if cur in names else min(self.song_sel, len(self.songs))
        self.fix_song_scroll()

    def fix_song_scroll(self):
        n = len(self.songs) + 1
        if self.song_sel < self.song_scroll:
            self.song_scroll = self.song_sel
        elif self.song_sel >= self.song_scroll + self.SONG_ROWS:
            self.song_scroll = self.song_sel - self.SONG_ROWS + 1
        self.song_scroll = max(0, min(self.song_scroll, max(0, n - self.SONG_ROWS)))

    def songs_geom(self):
        box = pygame.Rect(0, 0, 680, 112 + self.SONG_ROWS * 34 + 52)
        box.center = (W // 2, H // 2)
        rows = [pygame.Rect(box.x + 20, box.y + 62 + i * 34, box.w - 40, 30)
                for i in range(self.SONG_ROWS)]
        y = rows[-1].bottom + 12
        btns = {"preview": pygame.Rect(box.x + 20, y, 120, 32),
                "folder": pygame.Rect(box.x + 148, y, 150, 32),
                "online": pygame.Rect(box.x + 306, y, 120, 32),
                "use": pygame.Rect(box.right - 250, y, 110, 32),
                "cancel": pygame.Rect(box.right - 130, y, 110, 32)}
        return box, rows, btns

    def choose_song(self, i):
        name = ([""] + self.songs)[i]
        self.stop_preview()
        self.modal = None
        if name == self.data.music:
            return
        self.push_undo()
        self.data.music = name
        self.dirty = True
        self.say(("Song: " + song_title(name)) if name else "Song removed")

    def preview_song(self, i):
        name = ([""] + self.songs)[i]
        if not name:
            self.stop_preview()
            return
        if self.game.play_music(os.path.join(MUSIC_DIR, name), 0.0, force=True):
            self.preview = True

    # ---- online songs (from the GitHub repo) -------------------------------------
    def online_song_list(self):
        o = self.game.online_songs
        return o.get("songs", []) if o["status"] == "ok" else []

    def songs_online_event(self, e):
        songs = self.online_song_list()
        n = len(songs)
        box, rows, btns = self.songs_geom()
        if e.type == pygame.MOUSEWHEEL:
            self.song_scroll = max(0, min(self.song_scroll - e.y, max(0, n - self.SONG_ROWS)))
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for slot, r in enumerate(rows):
                i = self.song_scroll + slot
                if i < n and r.collidepoint(e.pos):
                    if i == self.song_sel:
                        self.get_online_song(i)
                    else:
                        self.song_sel = i
                    return
            if btns["online"].collidepoint(e.pos):
                self.song_online = False
                self.song_sel = self.song_scroll = 0
            elif btns["use"].collidepoint(e.pos):
                self.get_online_song(self.song_sel)
            elif btns["cancel"].collidepoint(e.pos) or not box.collidepoint(e.pos):
                self.modal = None
        elif e.type == pygame.KEYDOWN:
            k = e.key
            if k == pygame.K_ESCAPE:
                self.song_online = False
                self.song_sel = self.song_scroll = 0
            elif n and k in (pygame.K_UP, pygame.K_w):
                self.song_sel = (self.song_sel - 1) % n
            elif n and k in (pygame.K_DOWN, pygame.K_s):
                self.song_sel = (self.song_sel + 1) % n
            elif k in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.get_online_song(self.song_sel)
            elif k == pygame.K_r:
                self.game.fetch_online_songs(force=True)
            if n:
                self.song_sel = min(self.song_sel, n - 1)
                if self.song_sel < self.song_scroll:
                    self.song_scroll = self.song_sel
                elif self.song_sel >= self.song_scroll + self.SONG_ROWS:
                    self.song_scroll = self.song_sel - self.SONG_ROWS + 1

    def get_online_song(self, i):
        songs = self.online_song_list()
        if not (0 <= i < len(songs)):
            return
        name, url = songs[i]
        if os.path.isfile(os.path.join(MUSIC_DIR, name)):
            self.show_local_song(name)
            return
        if self.song_dl:
            return
        self.song_dl = name

        def work():
            try:
                download_song(name, url)
                self.song_dl_done = name
            except Exception:
                self.song_dl_done = "!" + name
            self.song_dl = None
        threading.Thread(target=work, daemon=True).start()
        self.say("Downloading " + song_title(name) + "...")

    def show_local_song(self, name):
        """Back to your songs list with a just-downloaded song highlighted."""
        self.song_online = False
        self.songs = list_songs()
        names = [""] + self.songs
        self.song_sel = names.index(name) if name in names else 0
        self.song_scroll = 0
        self.fix_song_scroll()
        self.say("Got %s - press ENTER to use it" % song_title(name))

    def songs_event(self, e):
        if self.song_online:
            self.songs_online_event(e)
            return
        n = len(self.songs) + 1
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1 and \
                self.songs_geom()[2]["online"].collidepoint(e.pos):
            self.song_online = True
            self.song_sel = self.song_scroll = 0
            self.game.fetch_online_songs()
            return
        if e.type == pygame.MOUSEWHEEL:
            self.song_scroll = max(0, min(self.song_scroll - e.y, max(0, n - self.SONG_ROWS)))
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            box, rows, btns = self.songs_geom()
            for slot, r in enumerate(rows):
                i = self.song_scroll + slot
                if i < n and r.collidepoint(e.pos):
                    if i == self.song_sel:          # click a highlighted song again to use it
                        self.choose_song(i)
                    else:
                        self.song_sel = i
                    return
            if btns["preview"].collidepoint(e.pos):
                self.preview_song(self.song_sel)
            elif btns["folder"].collidepoint(e.pos):
                self.game.open_folder(MUSIC_DIR)
            elif btns["use"].collidepoint(e.pos):
                self.choose_song(self.song_sel)
            elif btns["cancel"].collidepoint(e.pos) or not box.collidepoint(e.pos):
                self.stop_preview()
                self.modal = None
        elif e.type == pygame.KEYDOWN:
            k = e.key
            if k == pygame.K_ESCAPE:
                self.stop_preview()
                self.modal = None
            elif k in (pygame.K_UP, pygame.K_w):
                self.song_sel = (self.song_sel - 1) % n
            elif k in (pygame.K_DOWN, pygame.K_s):
                self.song_sel = (self.song_sel + 1) % n
            elif k in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.choose_song(self.song_sel)
            elif k == pygame.K_SPACE:
                if self.preview:
                    self.stop_preview()
                else:
                    self.preview_song(self.song_sel)
            elif k == pygame.K_o:
                self.game.open_folder(MUSIC_DIR)
            elif k == pygame.K_r:
                self.rescan_songs()
            self.fix_song_scroll()

    def draw_songs_online(self):
        g = self.game
        s = g.screen
        self.draw_veil()
        box, rows, btns = self.songs_geom()
        pygame.draw.rect(s, (20, 24, 50), box, border_radius=12)
        pygame.draw.rect(s, (120, 200, 255), box, 3, border_radius=12)
        s.blit(g.mid.render("Online songs", True, (255, 255, 255)), (box.x + 24, box.y + 16))
        sub = g.small.render("github.com/%s - music" % REPO, True, (150, 160, 200))
        s.blit(sub, (box.right - sub.get_width() - 24, box.y + 26))
        o = g.online_songs
        songs = self.online_song_list()
        mx, my = pygame.mouse.get_pos()
        if o["status"] != "ok" or not songs:
            msg = {"loading": "Loading songs from GitHub...", "idle": "Loading songs...",
                   "error": o.get("err", "Couldn't load the online songs") + "  (R: retry)",
                   "ok": "No songs online yet"}[o["status"]]
            t = g.font.render(msg, True, (200, 200, 230))
            s.blit(t, (box.centerx - t.get_width() // 2, rows[2].y))
        for slot, r in enumerate(rows):
            i = self.song_scroll + slot
            if i >= len(songs):
                break
            name, _ = songs[i]
            on = i == self.song_sel
            pygame.draw.rect(s, (40, 46, 90) if on else (30, 30, 62) if r.collidepoint((mx, my))
                             else (16, 19, 42), r, border_radius=6)
            pygame.draw.rect(s, (120, 200, 255) if on else (60, 68, 120), r, 2, border_radius=6)
            s.blit(g.font.render(song_title(name), True, (255, 255, 255)), (r.x + 12, r.y + 7))
            have = os.path.isfile(os.path.join(MUSIC_DIR, name))
            tag = ("DOWNLOADING..." if self.song_dl == name else "DOWNLOADED" if have else "GET")
            t = g.small.render(tag, True, (90, 230, 120) if have else (120, 200, 255))
            s.blit(t, (r.right - t.get_width() - 12, r.y + 8))
        for k, label in (("online", "MY SONGS"), ("use", "DOWNLOAD"), ("cancel", "CLOSE")):
            self.draw_button(btns[k], label, active=btns[k].collidepoint((mx, my)),
                             color=(120, 200, 255))
        ht = g.tiny.render("UP/DOWN choose   ENTER download   R refresh   ESC back to my songs",
                           True, (150, 160, 200))
        s.blit(ht, (box.centerx - ht.get_width() // 2, box.bottom - 22))

    def draw_songs(self):
        g = self.game
        s = g.screen
        if self.song_online:
            self.draw_songs_online()
            return
        self.draw_veil()
        box, rows, btns = self.songs_geom()
        pygame.draw.rect(s, (20, 24, 50), box, border_radius=12)
        pygame.draw.rect(s, (255, 150, 230), box, 3, border_radius=12)
        s.blit(g.mid.render("Pick a song", True, (255, 255, 255)), (box.x + 24, box.y + 16))
        sub = g.small.render("from your songs folder", True, (150, 160, 200))
        s.blit(sub, (box.right - sub.get_width() - 24, box.y + 26))
        names = [""] + self.songs
        mx, my = pygame.mouse.get_pos()
        for slot, r in enumerate(rows):
            i = self.song_scroll + slot
            if i >= len(names):
                break
            on = i == self.song_sel
            cur = names[i] == self.data.music
            hov = r.collidepoint((mx, my))
            pygame.draw.rect(s, (48, 40, 84) if on else (30, 30, 62) if hov else (16, 19, 42),
                             r, border_radius=6)
            pygame.draw.rect(s, (255, 150, 230) if on else (60, 68, 120), r, 2, border_radius=6)
            label = song_title(names[i]) if names[i] else "(no song)"
            while g.font.size(label)[0] > r.w - 120 and len(label) > 4:
                label = label[:-4] + "..."
            s.blit(g.font.render(label, True, (255, 255, 255) if names[i] else (170, 170, 200)),
                   (r.x + 12, r.y + 7))
            if cur:
                t = g.small.render("CURRENT", True, (255, 150, 230))
                s.blit(t, (r.right - t.get_width() - 12, r.y + 8))
        if not self.songs:
            lines = ["Your songs folder is empty.",
                     "Click OPEN FOLDER, drop .mp3 / .ogg / .wav files in it, then come back."]
            for j, ln in enumerate(lines):
                t = g.small.render(ln, True, (200, 200, 230))
                s.blit(t, (box.centerx - t.get_width() // 2, rows[2].y + j * 24))
        if self.song_scroll > 0:
            pygame.draw.polygon(s, (200, 200, 230), [(box.right - 14, rows[0].y + 14),
                                                     (box.right - 6, rows[0].y + 14),
                                                     (box.right - 10, rows[0].y + 6)])
        if self.song_scroll + self.SONG_ROWS < len(names):
            yb = rows[-1].bottom
            pygame.draw.polygon(s, (200, 200, 230), [(box.right - 14, yb - 14),
                                                     (box.right - 6, yb - 14),
                                                     (box.right - 10, yb - 6)])
        labels = {"preview": "STOP" if self.preview else "PREVIEW", "folder": "OPEN FOLDER",
                  "online": "ONLINE",
                  "use": "USE SONG", "cancel": "CANCEL"}
        for k, r in btns.items():
            self.draw_button(r, labels[k], active=r.collidepoint((mx, my)) or
                             (k == "preview" and self.preview), color=(255, 150, 230))
        ht = g.tiny.render("UP/DOWN choose   SPACE preview   ENTER use   O open folder   "
                           "ESC cancel", True, (150, 160, 200))
        s.blit(ht, (box.centerx - ht.get_width() // 2, box.bottom - 22))

    def modal_event(self, e):
        if self.modal == "props":
            self.props_event(e)
            return
        if self.modal == "songs":
            self.songs_event(e)
            return
        if self.modal == "color":
            self.cedit_event(e)
            return
        if e.type != pygame.KEYDOWN:
            return
        cmd = e.mod & (pygame.KMOD_CTRL | pygame.KMOD_META)
        if e.key == pygame.K_ESCAPE:
            self.modal = None
        elif cmd and e.key == pygame.K_v:          # paste text (e.g. a song's path)
            self.modal_text += self.game.clipboard_text()
            self.modal_text = self.modal_text[:TEXT_MAX]
        elif e.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
            text = self.modal_text.strip()
            kind = self.modal
            if kind == "desc":                       # may be empty: that clears it
                self.push_undo()
                self.data.description = text
                self.modal = None
                self.dirty = True
            elif kind == "text":
                self.push_undo()
                if text:
                    self.data.texts[self.modal_cell] = (text, self.group)
                else:
                    self.data.texts.pop(self.modal_cell, None)
                self.modal = None
                self.dirty = True
            elif kind == "group":
                try:
                    self.group = max(0, min(GROUP_MAX, int(text or "0")))
                except ValueError:
                    pass
                self.modal = None
            elif text:
                self.data.name = text
                self.named = True
                self.modal = None
                if kind == "save":
                    self.write()
                else:
                    self.dirty = True
        elif e.key == pygame.K_BACKSPACE:
            self.modal_text = self.modal_text[:-1]
        elif e.unicode and e.unicode.isprintable():
            if self.modal == "group" and not e.unicode.isdigit():
                return
            limit = {"desc": DESC_MAX, "text": TEXT_MAX, "group": 3}.get(
                self.modal, NAME_MAX)
            if len(self.modal_text) < limit:
                self.modal_text += e.unicode

    # ---- events ------------------------------------------------------------
    def handle(self, e):
        if self.modal:
            self.modal_event(e)
            return
        if e.type == pygame.MOUSEWHEEL:
            self.cam += (e.x - e.y) * 80
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button in (1, 3):
            x, y = e.pos
            if y < CEIL:
                if e.button == 1:
                    self.top_click(x, y)
            elif y >= FLOOR:
                self.pal_click(x, y, e.button)
            elif e.button == 1 and self.tool == "select":
                col, row = self.cell_at(x, y)
                if self.pasting:
                    self.paste_at(col, row)
                else:
                    self.sel = (col, row, col, row)
                    self.drag = "select"
            else:
                self.push_undo()
                self.drag = "paint" if e.button == 1 else "erase"
                self.apply_mouse(x, y, self.drag, True)
        elif e.type == pygame.MOUSEMOTION and self.drag:
            x, y = e.pos
            if self.drag == "select":
                col, row = self.cell_at(x, max(CEIL, min(FLOOR - 1, y)))
                self.sel = (self.sel[0], self.sel[1], col, row)
            elif CEIL <= y < FLOOR:
                self.apply_mouse(x, y, self.drag, False)
        elif e.type == pygame.MOUSEBUTTONUP and e.button in (1, 3):
            self.end_stroke()
        elif e.type == pygame.KEYDOWN:
            self.key(e)
        self.cam = max(0.0, min(self.cam, MAX_COLS * B))

    def key(self, e):
        mods = e.mod                       # modifier state when the key was pressed
        cmd = mods & (pygame.KMOD_CTRL | pygame.KMOD_META)
        shift = mods & pygame.KMOD_SHIFT
        k = e.key
        if k == pygame.K_ESCAPE:
            if self.pasting:
                self.pasting = False
            elif self.sel:
                self.sel = None
            else:
                self.request_leave()
        elif cmd and k == pygame.K_s:
            self.save()
        elif cmd and k == pygame.K_z:
            self.do_redo() if shift else self.do_undo()
        elif cmd and k == pygame.K_y:
            self.do_redo()
        elif cmd and k == pygame.K_c:
            self.copy_sel()
        elif cmd and k == pygame.K_x:
            self.copy_sel(cut=True)
        elif cmd and k == pygame.K_v:
            self.start_paste()
        elif cmd and k == pygame.K_d:
            self.copy_sel()
            if self.clip:
                self.start_paste()
        elif cmd and k == pygame.K_a:
            self.tool = "select"
            self.sel = (0, 0, max(self.data.last_col(), 1), ROWS - 1)
        elif k in (pygame.K_DELETE, pygame.K_BACKSPACE):
            self.delete_key()
        elif k == pygame.K_e:
            self.set_tool("erase")
        elif k == pygame.K_v:
            self.set_tool("select")
        elif k == pygame.K_g:
            self.group_sel()
        elif k == pygame.K_b:
            self.set_layer("bg" if self.layer == "main" else "main")
        elif k == pygame.K_m:
            self.toggle_preview()
        elif k == pygame.K_LEFTBRACKET:
            self.group = max(0, self.group - 1)
        elif k == pygame.K_RIGHTBRACKET:
            self.group = min(GROUP_MAX, self.group + 1)
        elif k == pygame.K_TAB:
            n = len(self.tabs())
            self.tab[self.layer] = (self.tab[self.layer] + (-1 if shift else 1)) % n
        elif k == pygame.K_p or k in (pygame.K_RETURN, pygame.K_KP_ENTER):
            self.playtest(here=bool(shift))
        elif k == pygame.K_HOME:
            self.cam = 0.0
        elif pygame.K_1 <= k <= pygame.K_9:
            i = k - pygame.K_1
            row = self.cur_tab()[1 if shift else 0]
            if i < len(row):
                self.set_tool(row[i][0])

    def top_click(self, x, y):
        pos = (x, y)
        if TOP_BUTTONS["back"].collidepoint(pos):
            self.request_leave()
        elif TOP_BUTTONS["save"].collidepoint(pos):
            self.save()
        elif TOP_BUTTONS["name"].collidepoint(pos):
            self.open_modal("rename", self.data.name)
        elif TOP_BUTTONS["desc"].collidepoint(pos):
            self.open_modal("desc", self.data.description)
        elif TOP_BUTTONS["start"].collidepoint(pos):
            self.push_undo()
            i = MODE_ORDER.index(self.data.start_mode)
            self.data.start_mode = MODE_ORDER[(i + 1) % len(MODE_ORDER)]
            self.dirty = True
        elif TOP_BUTTONS["music"].collidepoint(pos):
            self.open_songs()
        elif TOP_BUTTONS["group"].collidepoint(pos):
            self.open_modal("group", str(self.group) if self.group else "")
        elif TOP_BUTTONS["layer"].collidepoint(pos):
            self.set_layer("bg" if self.layer == "main" else "main")
        elif TOP_BUTTONS["play"].collidepoint(pos):
            self.playtest(here=False)
        elif TOP_BUTTONS["here"].collidepoint(pos):
            self.playtest(here=True)

    def swatches_shown(self):
        return self.tab[self.layer] == 0        # OBJECTS / BACKGROUND tab

    def pick_color(self, i):
        """Pick the colour for new objects - and recolour the selection."""
        if self.layer == "bg":
            self.bg_color = i
            items = [it for it in self.selected() if it[0] == "bg"] if self.sel else []
        else:
            self.obj_color = i
            items = ([it for it in self.selected() if it[0] == "cell" and it[3][0] in COLORABLE]
                     if self.sel else [])
        if items:
            self.push_undo()
            for kind, c, r, v in items:
                (self.data.bg if kind == "bg" else self.data.cells)[(c, r)] = \
                    (v[0], v[1], v[2], i)
            self.dirty = True
            self.say("Recoloured %d objects" % len(items))

    def cur_color(self):
        return self.bg_color if self.layer == "bg" else self.obj_color

    def open_color_editor(self, slot=None):
        slot = self.cur_color() if slot is None else slot
        if not slot:
            self.say("AUTO follows the game mode - pick a numbered colour to edit it")
            return
        self.cedit = {"slot": slot, "rgb": list(self.data.palette[slot - 1]), "sel": 0,
                      "drag": None}
        self.modal = "color"
        self.drag = None

    def cedit_geom(self):
        box = pygame.Rect(0, 0, 560, 330)
        box.center = (W // 2, H // 2 - 10)
        sliders = [pygame.Rect(box.x + 70, box.y + 84 + i * 50, 262, 22) for i in range(3)]
        preview = pygame.Rect(box.right - 160, box.y + 74, 130, 130)
        presets = [pygame.Rect(box.x + 24 + i * 46, box.y + 240, 40, 26)
                   for i in range(len(DEFAULT_PALETTE))]
        btns = {"ok": pygame.Rect(box.right - 250, box.bottom - 46, 110, 32),
                "cancel": pygame.Rect(box.right - 130, box.bottom - 46, 110, 32),
                "reset": pygame.Rect(box.x + 24, box.bottom - 46, 140, 32)}
        return box, sliders, preview, presets, btns

    def cedit_set_from_mouse(self, i, x):
        _, sliders, _, _, _ = self.cedit_geom()
        r = sliders[i]
        self.cedit["rgb"][i] = max(0, min(255, int(round((x - r.x) / r.w * 255))))
        self.cedit["sel"] = i

    def cedit_close(self, keep):
        if keep:
            slot, rgb = self.cedit["slot"], tuple(self.cedit["rgb"])
            if tuple(self.data.palette[slot - 1]) != rgb:
                self.push_undo()
                self.data.palette[slot - 1] = rgb
                self.dirty = True
                self.say("Colour %d updated - everything using it changed too" % slot)
        self.cedit = None
        self.modal = None

    def cedit_event(self, e):
        ce = self.cedit
        box, sliders, preview, presets, btns = self.cedit_geom()
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for i, r in enumerate(sliders):
                if r.inflate(16, 16).collidepoint(e.pos):
                    ce["drag"] = i
                    self.cedit_set_from_mouse(i, e.pos[0])
                    return
            for i, r in enumerate(presets):
                if r.collidepoint(e.pos):
                    ce["rgb"] = list(DEFAULT_PALETTE[i])
                    return
            if btns["ok"].collidepoint(e.pos):
                self.cedit_close(True)
            elif btns["cancel"].collidepoint(e.pos) or not box.collidepoint(e.pos):
                self.cedit_close(False)
            elif btns["reset"].collidepoint(e.pos):
                ce["rgb"] = list(DEFAULT_PALETTE[ce["slot"] - 1])
        elif e.type == pygame.MOUSEMOTION and ce["drag"] is not None:
            self.cedit_set_from_mouse(ce["drag"], e.pos[0])
        elif e.type == pygame.MOUSEBUTTONUP:
            ce["drag"] = None
        elif e.type == pygame.KEYDOWN:
            step = 25 if e.mod & pygame.KMOD_SHIFT else 5
            if e.key == pygame.K_ESCAPE:
                self.cedit_close(False)
            elif e.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.cedit_close(True)
            elif e.key in (pygame.K_UP, pygame.K_w):
                ce["sel"] = (ce["sel"] - 1) % 3
            elif e.key in (pygame.K_DOWN, pygame.K_s, pygame.K_TAB):
                ce["sel"] = (ce["sel"] + 1) % 3
            elif e.key in (pygame.K_LEFT, pygame.K_a, pygame.K_RIGHT, pygame.K_d):
                d = -step if e.key in (pygame.K_LEFT, pygame.K_a) else step
                ce["rgb"][ce["sel"]] = max(0, min(255, ce["rgb"][ce["sel"]] + d))

    def draw_color_editor(self):
        g = self.game
        s = g.screen
        ce = self.cedit
        self.draw_veil()
        box, sliders, preview, presets, btns = self.cedit_geom()
        rgb = tuple(ce["rgb"])
        pygame.draw.rect(s, (20, 24, 50), box, border_radius=12)
        pygame.draw.rect(s, rgb, box, 3, border_radius=12)
        s.blit(g.mid.render("Edit colour %d" % ce["slot"], True, (255, 255, 255)),
               (box.x + 24, box.y + 18))
        mx, my = pygame.mouse.get_pos()
        for i, (r, name) in enumerate(zip(sliders, "RGB")):
            on = i == ce["sel"]
            lab = g.mid.render(name, True, (255, 255, 255) if on else (160, 170, 210))
            s.blit(lab, (box.x + 30, r.centery - lab.get_height() // 2))
            for x in range(r.w):                         # gradient track
                c = list(rgb)
                c[i] = int(x / (r.w - 1) * 255)
                pygame.draw.line(s, c, (r.x + x, r.y), (r.x + x, r.bottom - 1))
            pygame.draw.rect(s, (255, 230, 90) if on else (90, 100, 160), r, 2, border_radius=3)
            kx = r.x + int(rgb[i] / 255 * r.w)
            pygame.draw.rect(s, (255, 255, 255), (kx - 4, r.y - 5, 8, r.h + 10), border_radius=3)
            pygame.draw.rect(s, (10, 10, 20), (kx - 4, r.y - 5, 8, r.h + 10), 2, border_radius=3)
            vt = g.font.render(str(rgb[i]), True, (255, 255, 255))
            s.blit(vt, (r.right + 12, r.centery - vt.get_height() // 2))
        # preview: a block, spike and ramp in this colour
        pygame.draw.rect(s, (12, 14, 32), preview, border_radius=8)
        bx, by = preview.x + 4, preview.y + 45
        g.draw_obj_at("block", bx, by, rgb)
        g.draw_obj_at("ramp_br", bx + 42, by, rgb)
        g.draw_obj_at("spike", bx + 84, by, rgb)
        pygame.draw.rect(s, bg_fill((0, 0, 0), 1, [rgb]), (preview.x + 15, preview.y + 95,
                                                           100, 20), border_radius=4)
        t = g.micro.render("background", True, (220, 220, 240))
        s.blit(t, (preview.centerx - t.get_width() // 2, preview.y + 98))
        s.blit(g.small.render("Quick picks:", True, (150, 160, 200)), (box.x + 24, box.y + 218))
        for i, r in enumerate(presets):
            pygame.draw.rect(s, DEFAULT_PALETTE[i], r, border_radius=4)
            pygame.draw.rect(s, (255, 255, 255) if r.collidepoint((mx, my)) else (60, 68, 120),
                             r, 2, border_radius=4)
        for k, label in (("ok", "OK"), ("cancel", "CANCEL"), ("reset", "RESET")):
            self.draw_button(btns[k], label, active=btns[k].collidepoint((mx, my)),
                             color=(255, 230, 90))
        ht = g.micro.render("drag the sliders   UP/DOWN: R/G/B   LEFT/RIGHT: change "
                            "(Shift = faster)   ENTER: ok   ESC: cancel", True, (150, 160, 200))
        s.blit(ht, (box.centerx - ht.get_width() // 2, box.bottom + 8))

    def pal_click(self, x, y, button=1):
        pos = (x, y)
        if self.swatches_shown():
            for i in range(COLOR_SLOTS):
                if swatch_rect(i, self.layer).collidepoint(pos):
                    if button == 3:                       # right-click: edit that colour
                        self.open_color_editor(i)
                    else:
                        self.pick_color(i)
                    return
            if color_edit_rect(self.layer).collidepoint(pos):
                self.open_color_editor()
                return
        if self.layer == "bg":
            if THEME_BUTTON.collidepoint(pos):
                keys = [k for k, _ in THEMES]
                self.push_undo()
                self.data.theme = keys[(keys.index(self.data.theme) + 1) % len(keys)]
                self.dirty = True
                self.say("Background theme: " + dict(THEMES)[self.data.theme])
                return
        for i in range(len(self.tabs())):
            if etab_rect(i).collidepoint(pos):
                self.tab[self.layer] = i
                return
        for row, pal in enumerate(self.cur_tab()):
            for i, (tool, _) in enumerate(pal):
                if pal_rect(i, row, len(pal)).collidepoint(pos):
                    self.set_tool(tool)
                    return
        if SIDE_BUTTONS["select"].collidepoint(pos):
            self.set_tool("select")
        elif SIDE_BUTTONS["erase"].collidepoint(pos):
            self.set_tool("erase")
        elif SIDE_BUTTONS["delete"].collidepoint(pos):
            if self.sel:
                self.delete_sel()
            else:
                self.say("Select an area first (SELECT or V), then press DELETE")
        elif SIDE_BUTTONS["copy"].collidepoint(pos):
            self.copy_sel()
        elif SIDE_BUTTONS["cut"].collidepoint(pos):
            self.copy_sel(cut=True)
        elif SIDE_BUTTONS["paste"].collidepoint(pos):
            self.start_paste()

    def playtest(self, here):
        self.stop_preview()
        self.game.start_playtest(self.data, self.cam + CAM_OFFSET if here else None)

    def update(self):
        if self.toast_t > 0:
            self.toast_t -= 1
        if self.leave_armed > 0:
            self.leave_armed -= 1
        if self.song_dl_done:
            done, self.song_dl_done = self.song_dl_done, None
            if done.startswith("!"):
                self.say("Couldn't download " + song_title(done[1:]))
            elif self.modal == "songs":
                self.show_local_song(done)
        if self.modal == "songs" and not self.song_online:
            self.song_scan += 1
            if self.song_scan % 45 == 0:     # pick up songs you just dropped in the folder
                self.rescan_songs()
        if self.modal:
            return
        keys = pygame.key.get_pressed()
        mods = pygame.key.get_mods()
        if mods & (pygame.KMOD_CTRL | pygame.KMOD_META):
            return
        speed = 36 if (mods & pygame.KMOD_SHIFT) else 14
        if keys[pygame.K_LEFT] or keys[pygame.K_a]:
            self.cam -= speed
        if keys[pygame.K_RIGHT] or keys[pygame.K_d]:
            self.cam += speed
        self.cam = max(0.0, min(self.cam, MAX_COLS * B))

    # ---- drawing -------------------------------------------------------------
    def draw_button(self, rect, text, active=False, color=(120, 140, 220), font=None):
        g = self.game
        s = g.screen
        pygame.draw.rect(s, (40, 46, 90) if active else (24, 28, 60), rect, border_radius=6)
        pygame.draw.rect(s, color if active else (60, 68, 120), rect, 2, border_radius=6)
        t = (font or g.small).render(text, True, (255, 255, 255))
        s.blit(t, (rect.centerx - t.get_width() // 2, rect.centery - t.get_height() // 2))

    def draw_icon(self, tool, cx, cy):
        s = self.game.screen
        if tool == "block":
            r = pygame.Rect(0, 0, 22, 22)
            r.center = (cx, cy)
            pygame.draw.rect(s, (12, 14, 32), r)
            pygame.draw.rect(s, (70, 200, 255), r, 2)
        elif tool in RAMPS:
            w, h = ramp_size(tool)
            sc = 22 / max(w, h)
            pts = ramp_points(tool, cx - w * sc / 2, cy - h * sc / 2, w * sc, h * sc)
            pygame.draw.polygon(s, (12, 14, 32), pts)
            pygame.draw.polygon(s, (70, 200, 255), pts, 2)
        elif tool == "coin":
            pygame.draw.circle(s, (255, 205, 50), (cx, cy), 10)
            pygame.draw.circle(s, (255, 250, 200), (cx, cy), 10, 2)
            pygame.draw.circle(s, (200, 140, 20), (cx, cy), 5, 2)
        elif tool == "text":
            t = self.game.font.render("Aa", True, (255, 255, 255))
            s.blit(t, (cx - t.get_width() // 2, cy - t.get_height() // 2))
        elif tool.startswith("trig:") or tool.startswith("light:"):
            colr = TRIG_COLOR["light" if tool.startswith("light:") else tool[5:]]
            pygame.draw.circle(s, (20, 22, 40), (cx, cy), 11)
            pygame.draw.circle(s, colr, (cx, cy), 11, 2)
            sub = tool.split(":")[1]
            if sub == "move":
                pygame.draw.line(s, colr, (cx - 5, cy + 5), (cx + 5, cy - 5), 2)
                pygame.draw.polygon(s, colr, [(cx + 6, cy - 6), (cx, cy - 6), (cx + 6, cy)])
            elif sub == "reveal":
                pygame.draw.ellipse(s, colr, (cx - 7, cy - 4, 14, 8), 2)
                pygame.draw.circle(s, colr, (cx, cy), 2)
            elif sub in ("flicker_on", "flicker_off"):
                on = sub == "flicker_on"
                pygame.draw.circle(s, colr if on else (90, 90, 70), (cx, cy - 2), 5)
                pygame.draw.rect(s, colr, (cx - 3, cy + 3, 6, 4))
            else:
                pygame.draw.circle(s, colr, (cx, cy), 7 if sub == "open_circle" else 3, 2)
        elif tool in ("spike", "spike_d", "spike_l", "spike_r"):
            pts = {"spike": [(cx - 11, cy + 11), (cx, cy - 11), (cx + 11, cy + 11)],
                   "spike_d": [(cx - 11, cy - 11), (cx, cy + 11), (cx + 11, cy - 11)],
                   "spike_r": [(cx - 11, cy - 11), (cx + 11, cy), (cx - 11, cy + 11)],
                   "spike_l": [(cx + 11, cy - 11), (cx - 11, cy), (cx + 11, cy + 11)]}[tool]
            pygame.draw.polygon(s, (6, 6, 14), pts)
            pygame.draw.polygon(s, (255, 255, 255), pts, 2)
        elif tool in GHOST_BASE:           # invisible variants: the icon plus a dashed box
            self.draw_icon(GHOST_BASE[tool], cx, cy)
            draw_dashed_rect(s, pygame.Rect(cx - 13, cy - 12, 26, 24), (255, 255, 255), 4, 3, 1)
        elif tool == "pad":
            pygame.draw.ellipse(s, (255, 230, 40), (cx - 12, cy + 2, 24, 10))
        elif tool == "dpad":
            pygame.draw.ellipse(s, (80, 140, 255), (cx - 12, cy - 12, 24, 10))
        elif tool in ("orb", "dorb"):
            pygame.draw.circle(s, (255, 230, 40) if tool == "orb" else (80, 140, 255),
                               (cx, cy), 7)
            pygame.draw.circle(s, (255, 255, 255), (cx, cy), 12, 2)
            d = 1 if tool == "dorb" else -1
            pygame.draw.polygon(s, (255, 255, 255),
                                [(cx - 4, cy - 2 * d), (cx + 4, cy - 2 * d), (cx, cy + 3 * d)])
        elif tool.startswith("speed:"):
            v = float(tool.split(":")[1])
            colr = SPEED_COLOR[v]
            pygame.draw.ellipse(s, colr, (cx - 6, cy - 11, 12, 22), 3)
            pygame.draw.lines(s, colr, False, [(cx - 3, cy - 5), (cx + 2, cy), (cx - 3, cy + 5)], 2)
        elif tool in ("grav_d", "grav_u"):
            col = (255, 225, 30) if tool == "grav_u" else (60, 170, 255)
            pygame.draw.ellipse(s, col, (cx - 6, cy - 11, 12, 22), 3)
            d = -1 if tool == "grav_u" else 1
            pygame.draw.polygon(s, col, [(cx - 5, cy - 4 * d), (cx + 5, cy - 4 * d),
                                         (cx, cy + 6 * d)])
        elif tool == "finish":
            for i in range(3):
                for j in range(2):
                    c = (255, 255, 255) if (i + j) % 2 == 0 else (40, 40, 40)
                    pygame.draw.rect(s, c, (cx - 8 + j * 8, cy - 11 + i * 7, 8, 7))
        elif tool == "erase":
            pygame.draw.line(s, (255, 90, 90), (cx - 9, cy - 9), (cx + 9, cy + 9), 4)
            pygame.draw.line(s, (255, 90, 90), (cx - 9, cy + 9), (cx + 9, cy - 9), 4)
        elif tool.startswith("portal:"):
            m = tool.split(":")[1]
            pygame.draw.ellipse(s, ACCENT[m], (cx - 7, cy - 11, 14, 22), 3)

    def draw_group_tag(self, g, sx, sy):
        if g:
            t = self.game.tiny.render(str(g), True, (255, 230, 90))
            bx = pygame.Rect(sx + 1, sy + 1, t.get_width() + 4, t.get_height() + 1)
            pygame.draw.rect(self.game.screen, (8, 8, 20), bx)
            self.game.screen.blit(t, (bx.x + 2, bx.y + 1))

    def draw_trigger(self, c, r, cfg, cam, alpha=255):
        g = self.game
        s = g.screen
        t = cfg["type"]
        colr = TRIG_COLOR[t]
        x = c * B - cam
        for yy in range(CEIL, FLOOR, 12):          # where it fires
            pygame.draw.line(s, tuple(v // 2 for v in colr), (x, yy), (x, yy + 5), 1)
        cx, cy = int(x + B / 2), FLOOR - r * B - B // 2
        tool = "trig:" + t if t != "light" else "light:" + cfg["effect"]
        self.draw_icon(tool, cx, cy)
        lab = "G%d" % cfg["group"] if t != "light" else ""
        if lab:
            tt = g.tiny.render(lab, True, colr)
            s.blit(tt, (cx - tt.get_width() // 2, cy + 12))

    def draw_layer(self, which, cam, acc, lo, hi):
        g = self.game
        d = self.data
        if which == "bg":
            for (c, r), (kind, flip, grp, colr) in d.bg.items():
                if lo <= c <= hi:
                    g.draw_obj(Obj(kind, c, r, flip=flip, color=colr), cam, acc, layer="bg")
                    if self.layer == "bg":
                        self.draw_group_tag(grp, c * B - cam, FLOOR - (r + 1) * B)
            return
        for (c, r), (kind, flip, grp, colr) in d.cells.items():
            if lo <= c <= hi:
                g.draw_obj(Obj(kind, c, r, flip=flip, color=colr), cam, acc)
                self.draw_group_tag(grp, c * B - cam, FLOOR - (r + 1) * B)
        for c, up in d.gravs.items():
            if lo <= c <= hi:
                g.draw_obj(Obj("grav", c, 0, up=up), cam, acc)
        for c, v in d.speeds.items():
            if lo <= c <= hi:
                g.draw_obj(Obj("speed", c, 0, val=v), cam, acc)
        for c, mode in d.portals.items():
            if lo <= c <= hi:
                g.draw_mode_portal(mode, c * B - cam, CEIL + 36)
        for (c, r), (text, grp) in d.texts.items():
            if lo - 6 <= c <= hi + 6:
                g.draw_text_obj(TextObj(c, r, text), cam)
                draw_dashed_rect(g.screen, pygame.Rect(int(c * B - cam), FLOOR - (r + 1) * B,
                                                      B, B), (200, 200, 255), 3, 3, 1)
                self.draw_group_tag(grp, c * B - cam, FLOOR - (r + 1) * B)
        for (c, r), cfg in d.triggers.items():
            if lo <= c <= hi:
                self.draw_trigger(c, r, cfg, cam)

    def draw(self):
        g = self.game
        s = g.screen
        g.palette = self.data.palette
        cam = self.cam
        secs = self.sections()
        s.fill((10, 12, 30))

        # section backgrounds, floor / ceiling lines
        for i, (mode, c0) in enumerate(secs):
            x0 = c0 * B - cam
            x1 = secs[i + 1][1] * B - cam if i + 1 < len(secs) else W + 10
            if x1 < 0 or x0 > W:
                continue
            x0, x1 = max(0, x0), min(W, x1)
            pygame.draw.rect(s, BG[mode], (x0, CEIL, x1 - x0, FLOOR - CEIL))
            pygame.draw.line(s, ACCENT[mode], (x0, CEIL), (x1, CEIL), 3)
            pygame.draw.line(s, ACCENT[mode], (x0, FLOOR), (x1, FLOOR), 3)

        # grid
        first = int(cam // B)
        for ci in range(first, first + W // B + 2):
            x = ci * B - cam
            pygame.draw.line(s, (96, 106, 160) if ci % 10 == 0 else (52, 60, 104),
                             (x, CEIL), (x, FLOOR), 1)
            if ci % 10 == 0:
                s.blit(g.small.render(str(ci), True, (190, 200, 240)), (x + 3, CEIL + 3))
        for r in range(ROWS + 1):
            y = FLOOR - r * B
            pygame.draw.line(s, (52, 60, 104), (0, y), (W, y), 1)

        # safe start zone + spawn marker
        sx1 = SAFE_COLS * B - cam
        if sx1 > 0:
            dim = pygame.Surface((int(sx1), FLOOR - CEIL), pygame.SRCALPHA)
            dim.fill((0, 0, 0, 120))
            s.blit(dim, (0, CEIL))
            s.blit(g.small.render("START ZONE", True, (200, 200, 220)), (8 - cam, CEIL + 24))
            pygame.draw.rect(s, PRIMARY, (3 * B - 18 - cam, FLOOR - 36, 36, 36), 2)

        acc = ACCENT[secs[0][0]]
        lo, hi = first - 1, first + W // B + 2
        # the layer you're not editing is drawn faded
        self.draw_layer("bg", cam, acc, lo, hi)
        if self.layer == "bg":
            layer = pygame.Surface((W, H), pygame.SRCALPHA)
            g.screen = layer
            try:
                self.draw_layer("main", cam, acc, lo, hi)
            finally:
                g.screen = s
            layer.set_alpha(70)
            s.blit(layer, (0, 0))
        else:
            self.draw_layer("main", cam, acc, lo, hi)
        fin = self.data.finish
        if fin is not None and lo <= fin <= hi:
            fx = fin * B - cam
            for i in range(CEIL, FLOOR, 20):
                for j in range(2):
                    colr = (255, 255, 255) if ((i - CEIL) // 20 + j) % 2 == 0 else (30, 30, 30)
                    pygame.draw.rect(s, colr, (fx + j * 20, i, 20, 20))

        # selection
        if self.sel:
            c0, r0, c1, r1 = self.sel_rect()
            rect = pygame.Rect(int(c0 * B - cam), FLOOR - (r1 + 1) * B,
                               (c1 - c0 + 1) * B, (r1 - r0 + 1) * B)
            veil = pygame.Surface(rect.size, pygame.SRCALPHA)
            veil.fill((255, 230, 90, 40))
            s.blit(veil, rect.topleft)
            draw_dashed_rect(s, rect, (255, 230, 90), 7, 4, 2)

        # hover preview
        mx, my = pygame.mouse.get_pos()
        if CEIL <= my < FLOOR and not self.modal:
            col, row = self.cell_at(mx, my)
            r = pygame.Rect(col * B - cam, FLOOR - (row + 1) * B, B, B)
            tool = self.tool
            if self.pasting and self.clip:
                ghost = pygame.Surface((W, H), pygame.SRCALPHA)
                g.screen = ghost
                try:
                    for kind, dc, dr, v in self.clip["items"]:
                        c, rr = col + dc, row + dr
                        if kind in ("cell", "bg"):
                            g.draw_obj(Obj(v[0], c, rr, flip=v[1], color=v[3]), cam, acc,
                                       layer="bg" if kind == "bg" else "main")
                        elif kind == "text":
                            g.draw_text_obj(TextObj(c, rr, v[0]), cam)
                        elif kind == "trig":
                            self.draw_trigger(c, rr, v, cam)
                        elif kind == "grav":
                            g.draw_obj(Obj("grav", c, 0, up=v), cam, acc)
                        elif kind == "speed":
                            g.draw_obj(Obj("speed", c, 0, val=v), cam, acc)
                        elif kind == "portal":
                            g.draw_mode_portal(v, c * B - cam, CEIL + 36)
                finally:
                    g.screen = s
                ghost.set_alpha(150)
                s.blit(ghost, (0, 0))
                box = pygame.Rect(r.x, FLOOR - (row + self.clip["h"]) * B,
                                  self.clip["w"] * B, self.clip["h"] * B)
                draw_dashed_rect(s, box, (120, 255, 160), 7, 4, 2)
            elif tool in CELL_TOOLS:
                kind, flip = TOOL_CELL[tool]
                g.draw_obj(Obj(kind, col, row, flip=flip,
                               color=self.bg_color if self.layer == "bg"
                               else self.obj_color if kind in COLORABLE else 0), cam, acc,
                           layer="bg" if self.layer == "bg" else "main")
                pygame.draw.rect(s, (255, 255, 255), r, 2)
            elif tool == "erase":
                pygame.draw.rect(s, (255, 80, 80), r, 3)
            elif tool in ("select", "text") or tool.startswith(("trig:", "light:")):
                pygame.draw.rect(s, (255, 230, 90) if tool == "select" else (255, 255, 255), r, 2)
            else:
                pygame.draw.rect(s, (255, 255, 255), pygame.Rect(r.x, CEIL, B, FLOOR - CEIL), 2)

        if self.layer == "bg":
            t = g.font.render("EDIT BACKGROUND", True, (255, 230, 90))
            s.blit(t, (W - t.get_width() - 12, FLOOR - 28))
        self.draw_panels(mx, my)
        self.game.present()

    def draw_panels(self, mx, my):
        g = self.game
        s = g.screen
        # palette: tabs + two rows of tools + selection / eraser buttons
        pygame.draw.rect(s, (14, 16, 36), (0, FLOOR + 2, W, H - FLOOR - 2))
        hover_tool = None
        for i, (name, _) in enumerate(self.tabs()):
            r = etab_rect(i)
            on = i == self.tab[self.layer]
            pygame.draw.rect(s, (40, 46, 90) if on else (18, 21, 46), r, border_radius=6)
            pygame.draw.rect(s, (255, 230, 90) if on else (60, 68, 120), r, 2, border_radius=6)
            t = g.tiny.render(name, True, (255, 255, 255) if on else (160, 170, 210))
            s.blit(t, (r.centerx - t.get_width() // 2, r.centery - t.get_height() // 2))
        for row, pal in enumerate(self.cur_tab()):
            for i, (tool, label) in enumerate(pal):
                r = pal_rect(i, row, len(pal))
                self.draw_button(r, "", active=(tool == self.tool), color=(255, 230, 90))
                self.draw_icon(tool, r.x + 18, r.centery)
                t = g.micro.render(label, True, (255, 255, 255))
                s.blit(t, (r.x + 31, r.centery - t.get_height() // 2))
                if r.collidepoint((mx, my)):
                    hover_tool = tool
        if self.swatches_shown():
            acc0 = ACCENT[self.data.start_mode]
            pal = self.data.palette
            for i in range(COLOR_SLOTS):
                r = swatch_rect(i, self.layer)
                pygame.draw.rect(s, bg_fill(acc0, i, pal) if self.layer == "bg"
                                 else slot_color(pal, i, acc0), r, border_radius=5)
                on = i == self.cur_color()
                pygame.draw.rect(s, (255, 230, 90) if on else (60, 68, 120), r, 3 if on else 1,
                                 border_radius=5)
                if i == 0:
                    t = g.micro.render("AUTO", True, (10, 10, 20) if self.layer == "main"
                                       else (255, 255, 255))
                    s.blit(t, (r.centerx - t.get_width() // 2, r.centery - t.get_height() // 2))
                if r.collidepoint((mx, my)):
                    hover_tool = "color" if self.layer == "bg" else "objcolor"
            er = color_edit_rect(self.layer)
            self.draw_button(er, "EDIT COLOUR", active=er.collidepoint((mx, my)),
                             color=(255, 230, 90), font=g.micro)
            if er.collidepoint((mx, my)):
                hover_tool = "editcolor"
        if self.layer == "bg":
            self.draw_button(THEME_BUTTON, "THEME: " + dict(THEMES)[self.data.theme],
                             active=bool(self.data.theme), color=(90, 200, 255), font=g.micro)
            if THEME_BUTTON.collidepoint((mx, my)):
                hover_tool = "theme"
        for name, r in SIDE_BUTTONS.items():
            act = (name == self.tool) or (name == "paste" and self.pasting)
            colr = {"select": (255, 230, 90), "erase": (255, 90, 90),
                    "delete": (255, 90, 90)}.get(name, (120, 255, 160))
            self.draw_button(r, name.upper(), active=act, color=colr, font=g.micro)
            if r.collidepoint((mx, my)) and name in TOOL_HELP:
                hover_tool = name
        col = int((mx + self.cam) // B) if CEIL <= my < FLOOR else int(self.cam // B)
        nsel = len(self.selected()) if self.sel else 0
        info = "col %d   objects %d%s" % (col, self.data.object_count(),
                                          ("   selected %d" % nsel) if self.sel else "")
        it = g.tiny.render(info, True, (190, 200, 240))
        s.blit(it, (W - it.get_width() - 10, FLOOR + 10))
        helptxt = TOOL_HELP.get(hover_tool)
        if helptxt:                                # tooltip just above the palette
            ht = g.small.render(helptxt, True, (255, 255, 255))
            box = pygame.Rect(0, 0, ht.get_width() + 14, ht.get_height() + 8)
            box.bottomleft = (min(max(4, mx - 20), W - box.w - 4), FLOOR - 4)
            pygame.draw.rect(s, (20, 24, 50), box, border_radius=6)
            pygame.draw.rect(s, (255, 230, 90), box, 1, border_radius=6)
            s.blit(ht, (box.x + 7, box.y + 4))

        # top bar
        pygame.draw.rect(s, (14, 16, 36), (0, 0, W, CEIL))
        pygame.draw.line(s, (60, 68, 120), (0, CEIL - 1), (W, CEIL - 1), 1)
        mode_name = self.data.start_mode.upper()
        self.draw_button(TOP_BUTTONS["back"], "BACK")
        self.draw_button(TOP_BUTTONS["save"], "SAVE" + ("*" if self.dirty else ""))
        nm = self.data.name if len(self.data.name) <= 13 else self.data.name[:12] + "..."
        self.draw_button(TOP_BUTTONS["name"], nm)
        self.draw_button(TOP_BUTTONS["desc"], "DESC", active=bool(self.data.description),
                         color=(255, 230, 90))
        self.draw_button(TOP_BUTTONS["start"], "START: " + mode_name)
        self.draw_button(TOP_BUTTONS["music"], "SONGS", active=bool(self.data.music),
                         color=(255, 150, 230))
        self.draw_button(TOP_BUTTONS["group"], "GROUP %s" % (self.group or "-"),
                         active=bool(self.group), color=(255, 230, 90))
        self.draw_button(TOP_BUTTONS["layer"], "EDIT BG", active=self.layer == "bg",
                         color=(255, 230, 90))
        self.draw_button(TOP_BUTTONS["play"], "PLAY", color=(90, 230, 120))
        self.draw_button(TOP_BUTTONS["here"], "PLAY HERE", color=(90, 230, 120))

        if self.toast_t > 0:
            t = g.font.render(self.toast, True, (255, 255, 255))
            box = pygame.Rect(0, 0, t.get_width() + 24, 34)
            box.midtop = (W // 2, CEIL + 8)
            pygame.draw.rect(s, (20, 24, 50), box, border_radius=8)
            pygame.draw.rect(s, (255, 230, 90), box, 2, border_radius=8)
            s.blit(t, (box.x + 12, box.y + 8))

        if self.modal == "props":
            self.draw_props()
        elif self.modal == "songs":
            self.draw_songs()
        elif self.modal == "color":
            self.draw_color_editor()
        elif self.modal:
            self.draw_text_modal()

    def draw_veil(self):
        veil = pygame.Surface((W, H), pygame.SRCALPHA)
        veil.fill((0, 0, 0, 170))
        self.game.screen.blit(veil, (0, 0))

    def draw_text_modal(self):
        g = self.game
        s = g.screen
        self.draw_veil()
        box = pygame.Rect(0, 0, 520, 150)
        box.center = (W // 2, H // 2)
        pygame.draw.rect(s, (20, 24, 50), box, border_radius=12)
        pygame.draw.rect(s, (255, 230, 90), box, 3, border_radius=12)
        title = {"save": "Name your level", "rename": "Rename level",
                 "desc": "Describe your level", "text": "Text box",
                 "group": "Group for new objects (0 = none)"}[self.modal]
        s.blit(g.mid.render(title, True, (255, 255, 255)), (box.x + 24, box.y + 18))
        field = pygame.Rect(box.x + 24, box.y + 66, box.w - 48, 40)
        pygame.draw.rect(s, (8, 8, 20), field, border_radius=6)
        cursor = "|" if (pygame.time.get_ticks() // 450) % 2 == 0 else ""
        font = g.font if self.modal in ("desc", "text") else g.mid
        shown = self.modal_text
        while shown and font.size(shown + cursor)[0] > field.w - 20:
            shown = shown[1:]                    # long text scrolls: show the end
        img = font.render(shown + cursor, True, (255, 255, 255))
        s.blit(img, (field.x + 10, field.centery - img.get_height() // 2))
        limit = {"desc": DESC_MAX, "text": TEXT_MAX}.get(self.modal)
        if limit:
            cnt = g.small.render("%d/%d" % (len(self.modal_text), limit), True,
                                 (150, 160, 200))
            s.blit(cnt, (box.right - cnt.get_width() - 24, box.y + 24))
        hint = "ENTER to confirm    ESC to cancel"
        if self.modal == "text":
            hint = "ENTER to confirm (empty removes it)    ESC to cancel"
        s.blit(g.small.render(hint, True, (150, 160, 200)), (box.x + 24, box.y + 116))

    def draw_props(self):
        g = self.game
        s = g.screen
        f = self.form
        self.draw_veil()
        box, rows = self.props_geom()
        cfg = f["cfg"]
        colr = TRIG_COLOR[cfg["type"]]
        pygame.draw.rect(s, (20, 24, 50), box, border_radius=12)
        pygame.draw.rect(s, colr, box, 3, border_radius=12)
        title = {"move": "Move trigger", "reveal": "Reveal trigger",
                 "light": "Light trigger"}[cfg["type"]]
        s.blit(g.mid.render(title, True, (255, 255, 255)), (box.x + 24, box.y + 16))
        mx, my = pygame.mouse.get_pos()
        dr = self.props_delete_rect()
        self.draw_button(dr, "DELETE", active=dr.collidepoint((mx, my)), color=(255, 90, 90))
        for i, ((key, label, kind, ext), (r, minus, plus)) in enumerate(
                zip(trigger_fields(cfg), rows)):
            on = i == f["sel"]
            pygame.draw.rect(s, (40, 46, 90) if on else (16, 19, 42), r, border_radius=6)
            pygame.draw.rect(s, colr if on else (60, 68, 120), r, 2, border_radius=6)
            s.blit(g.font.render(label, True, (255, 255, 255)), (r.x + 12, r.y + 8))
            if kind == "choice":
                val = dict(ext).get(cfg[key], str(cfg[key]))
            elif on and f["typing"]:
                val = f["typing"] + ("|" if (pygame.time.get_ticks() // 450) % 2 == 0 else "")
            else:
                val = "%g" % cfg[key]
            vt = g.font.render(val, True, colr)
            s.blit(vt, ((minus.right + plus.left) // 2 - vt.get_width() // 2, r.y + 8))
            for b, sym in ((minus, "<" if kind == "choice" else "-"),
                           (plus, ">" if kind == "choice" else "+")):
                hov = b.collidepoint((mx, my))
                pygame.draw.rect(s, (60, 66, 120) if hov else (28, 32, 66), b, border_radius=5)
                st = g.font.render(sym, True, (255, 255, 255))
                s.blit(st, (b.centerx - st.get_width() // 2, b.centery - st.get_height() // 2))
        hint = ("UP/DOWN pick   LEFT/RIGHT change   type a number   "
                "ENTER ok   DELETE remove   ESC cancel")
        ht = g.tiny.render(hint, True, (150, 160, 200))
        s.blit(ht, (box.centerx - ht.get_width() // 2, box.bottom - 26))


# --------------------------------------------------------------------------
# Game
# --------------------------------------------------------------------------
FS_BUTTON = pygame.Rect(W - 46, 5, 40, 30)      # fullscreen button (menus + editor)
PAUSE_BUTTON = pygame.Rect(12, 44, 30, 28)      # pause button while playing


def make_display(fullscreen):
    """Window drawn at a fixed 960x540 and scaled (letterboxed) to the window or
    screen; pygame.SCALED also translates mouse positions for us."""
    flags = pygame.SCALED | pygame.RESIZABLE
    if fullscreen:
        flags |= pygame.FULLSCREEN
    try:
        return pygame.display.set_mode((W, H), flags)
    except pygame.error:                       # very old / unusual setups
        return pygame.display.set_mode((W, H))


VISIBLE_CARDS = 5
TAB_NAMES = ["Levels", "Your Levels", "Downloaded Levels", "All Levels", "Ranks", "Online"]
DOWNLOADED_TAB = 2
RANKS_TAB = 4
ONLINE_TAB = 5
CARD_H, CARD_GAP, CARD_TOP, CARD_X, CARD_W = 68, 8, 104, 50, 860
HOME_BUTTONS = [("PLAY", (90, 230, 120)), ("BUILD LEVELS", (120, 200, 255)),
                ("SKINS", (120, 255, 220)), ("SONGS", (255, 150, 230)),
                ("SETTINGS", (255, 210, 90)), ("QUIT", (220, 120, 150))]
SETTING_INFO = [
    ("account", "Account", "Your account name goes on levels you export: \"[Level] by [you]\""),
    ("merge_guest", "Bring in Guest progress", "Copy your progress from before accounts into "
                                                "this account (nothing is lost)"),
    ("default_practice", "Default game mode", "Mode a level starts in (P still switches it)"),
    ("wave_hold", "Wave controls", "CLICK: each click switches direction   HOLD: hold to go up"),
    ("music", "Music", "Play the songs attached to levels"),
    ("noclip", "Noclip", "Pass through everything and never die"),
    ("warp", "Level warping", "Number keys 1-9 jump to a section of the level"),
    ("hitboxes", "Show hitboxes", "Draw player and hazard hitboxes (H toggles it in a level)"),
    ("fps", "Show FPS", "Display the current frame rate in the bottom-right corner"),
    ("fullscreen", "Fullscreen", "F11, Alt+Enter or Ctrl/Cmd+F from anywhere"),
]
SETTING_DEFAULTS = {"accounts_folder": "", "default_practice": False, "wave_hold": False,
                    "music": True, "noclip": False, "warp": False, "hitboxes": False,
                    "fps": False, "fullscreen": False}
USERNAME_MAX = 20


class Game:
    def __init__(self):
        pygame.init()
        pygame.display.set_caption("Python Dash")
        self._fs = bool((load_save().get("__settings__") or {}).get("fullscreen"))
        self.screen = make_display(self._fs)
        try:                      # remembered so leaving fullscreen can restore it
            self._default_window = None if self._fs else pygame.display.get_window_size()
        except (AttributeError, pygame.error):
            self._default_window = None
        self.clock = pygame.time.Clock()
        self.font = pygame.font.Font(None, 26)
        self.small = pygame.font.Font(None, 22)
        self.tiny = pygame.font.Font(None, 19)
        self.micro = pygame.font.Font(None, 17)
        self.mid = pygame.font.Font(None, 38)
        self.big = pygame.font.Font(None, 84)
        self.huge = pygame.font.Font(None, 150)
        self.save = load_save()
        self.state = "home"
        self.sel = 0
        self.scroll = 0
        self.items = []
        self.levels = list(LEVELS)
        self.custom = []
        self.my_page = "list"
        self.tab = 0                       # level-select tab (see TAB_NAMES)
        self.tab_lists = [[] for _ in TAB_NAMES]
        self.online = {"status": "idle"}          # online levels (fetched in the background)
        self.online_songs = {"status": "idle"}    # online music
        self.move_old_downloads()
        self.other = []
        self.empty_lines = []
        self.confirm_del = None
        self.editor = None
        self.level = None
        self.level_idx = 0
        self.player = Player()
        self.practice = True
        self.settings = dict(SETTING_DEFAULTS)
        saved = self.save.get("__settings__")
        if isinstance(saved, dict):
            for k, v in SETTING_DEFAULTS.items():
                if k in saved:
                    self.settings[k] = (str(saved[k])[:1000] if isinstance(v, str)
                                        else bool(saved[k]))
        self.practice = self.settings["default_practice"]
        if isinstance(saved, dict) and "username" in saved:     # old usernames are gone:
            saved.pop("username", None)                         # everyone uses accounts now
            self.save_settings()
        self.acc_root = online_root(SHARED_DIR)      # None = not in an online folder
        self.known_salts = {}
        if self.acc_root:
            self.migrate_accounts()
            self.accounts = load_accounts(self.acc_root)
        else:                                        # no online folder: no accounts
            self.accounts = {"users": {}, "current": None}
        self.account = None          # display name of the signed-in account (None = guest)
        self.acct = None             # the sign-in / sign-up form
        self.music_ok = None         # can we play sound at all? (decided on first use)
        self.music_on = None         # path of the song that is playing
        sk = self.save.get("__skins__")
        self.skins = dict(sk) if isinstance(sk, dict) else {}     # mode -> skin id
        cur = self.accounts.get("current")
        u = self.accounts["users"].get(cur) if cur else None
        if u and u.get("salt") in self.known_salts.get(cur, {u.get("salt")}):
            self.load_profile(u)     # stay signed in between sessions
        elif cur:
            store_current(None)      # not that account any more: sign in again
        self.check_top1()            # (keeps the Crown if you beat the Top 1 earlier)
        self.skin_mode = 0           # SKINS screen: which game-mode tab
        self.skin_sel = 0
        self.ocean = None            # cached underwater gradient
        self.sea = None              # cached open-ocean gradient
        self.city = None             # cached night sky + skyline layers
        self.cave = None             # cached crystal cavern layers
        self.yard = None             # cached backyard layers
        self.palette = list(DEFAULT_PALETTE)   # colour slots of the level being drawn
        self.paused = False
        self.pause_sel = 0
        self.settings_return = "home"
        self.assisted = False        # this attempt used noclip or warping
        self.toast, self.toast_t = "", 0
        if getattr(self, "startup_note", None):
            self.say(self.startup_note)
        self.playtest = False
        self.playtest_sec = 0
        self.playtest_x = None
        self.attempt = 1
        self.cp_section = 0
        self.dead_timer = 0
        self.finished = False
        self.input_lock = False
        self.particles = []
        self.menu_t = 0
        self._mode_cache = {}
        self.bg = list(BG["cube"])
        self.accent = list(ACCENT["cube"])

    # ---- settings ------------------------------------------------------------------
    @property
    def noclip(self):
        return self.settings["noclip"]

    @noclip.setter
    def noclip(self, v):
        self.settings["noclip"] = bool(v)

    @property
    def show_hitboxes(self):
        return self.settings["hitboxes"]

    @show_hitboxes.setter
    def show_hitboxes(self, v):
        self.settings["hitboxes"] = bool(v)

    def save_settings(self):
        """Settings belong to this computer, not to an account: they live in the guest file."""
        guest = load_save()
        guest["__settings__"] = dict(self.settings)
        write_json(SAVE_PATH, guest)
        if _save_target[0] == SAVE_PATH:
            self.save["__settings__"] = dict(self.settings)

    # ---- accounts ----------------------------------------------------------------------
    def load_profile(self, user):
        """Switch progress (best %, coins, skins, unlocks) to an account, or to the guest."""
        if user:
            _save_target[0] = account_save_path(user, self.acc_root)
            try:
                with open(_save_target[0]) as f:
                    data = json.load(f)
                self.save = data if isinstance(data, dict) else {}
            except Exception:
                self.save = {}
            self.account = user["name"]
        else:
            _save_target[0] = SAVE_PATH
            self.save = load_save()
            self.account = None
        sk = self.save.get("__skins__")
        self.skins = dict(sk) if isinstance(sk, dict) else {}
        if user:
            self.grant_verified(user)

    def grant_verified(self, user):
        """Give 100 percent on levels this account beat before they were added to the game."""
        changed = False
        for name, who in VERIFIED_COMPLETIONS.items():
            if account_key(user["name"]) in {account_key(w) for w in who}:
                for d in LEVELS:
                    if d.name == name and self.save.get(d.key, 0) < 100:
                        self.save[d.key] = 100
                        changed = True
        if changed:
            write_save(self.save)

    # ---- main levels (admin) ----------------------------------------------------------
    def is_admin(self):
        return bool(self.account) and account_key(self.account) in ADMIN_ACCOUNTS

    @staticmethod
    def main_meta():
        try:
            with open(MAIN_META) as f:
                m = json.load(f)
            return m if isinstance(m, dict) else {}
        except Exception:
            return {}

    def builtin_levels(self, include_hidden=False):
        """The built-in levels as main levels, with AugmentedMagic's changes applied
        (new name, new difficulty, hidden).  Progress keys never change, so renaming a
        level keeps everyone's best % and coins."""
        meta = self.main_meta()
        out = []
        for d in LEVELS:
            o = meta.get("builtin:" + d.name)
            o = o if isinstance(o, dict) else {}
            if o.get("hidden") and not include_hidden:
                continue
            c = copy.copy(d)
            c.base_name = d.name
            c.hidden = bool(o.get("hidden"))
            if o.get("difficulty") in MAIN_DIFFICULTIES:
                c.difficulty = o["difficulty"]
            if o.get("name"):
                c.name = str(o["name"])[:NAME_MAX]
                c.title = c.name
            if d.name in TOP_DEMONS:
                c.title = "#%d  %s" % (TOP_DEMONS.index(d.name) + 1, c.name)
            out.append(c)
        return out

    def load_main_levels(self):
        """Main levels: level files in the main levels folder that have been set up."""
        meta = self.main_meta()
        out = []
        for data in load_custom_levels(MAIN_DIR):
            fn = os.path.basename(data.path)
            info = meta.get(fn)
            if not isinstance(info, dict) or info.get("difficulty") not in MAIN_DIFFICULTIES:
                continue                       # not set up yet
            data.name = str(info.get("name") or data.name)[:NAME_MAX]
            by = ("  -  by " + data.author) if data.author else ""
            ld = LevelDef(data.name, info["difficulty"],
                          (data.description or "%d objects" % data.object_count()) + by,
                          lambda lv, dd=data: dd.build(lv))
            ld.path = data.path
            ld.author = data.author
            ld.key = "main:" + fn
            ld.base_name = ld.name
            if ld.name in TOP_DEMONS:
                ld.title = "#%d  %s" % (TOP_DEMONS.index(ld.name) + 1, ld.name)
            out.append(ld)
        return out

    def go_admin(self, sel=0):
        """The MAIN LEVELS screen (AugmentedMagic only)."""
        if not self.is_admin():
            self.go_home()
            return
        os.makedirs(MAIN_DIR, exist_ok=True)
        meta = self.main_meta()
        items = [{"type": "admin_folder", "name": "+ OPEN MAIN LEVELS FOLDER",
                  "sub": "Drop level .json files in it (or drag them onto this window)",
                  "tag": "FOLDER", "col": (90, 230, 120), "modes": [], "best": None}]
        for d in self.builtin_levels(include_hidden=True):
            items.append({"type": "admin_builtin", "level": d, "name": d.title,
                          "sub": ("Built-in level  -  HIDDEN from the level list" if d.hidden
                                  else "Built-in level") + (
                              "  (was %s)" % d.base_name if d.name != d.base_name else ""),
                          "tag": "HIDDEN" if d.hidden else d.difficulty,
                          "col": (150, 155, 185) if d.hidden else DIFF_COLOR[d.difficulty],
                          "modes": self.level_modes(d), "best": None})
        for data in load_custom_levels(MAIN_DIR):
            fn = os.path.basename(data.path)
            info = meta.get(fn) if isinstance(meta.get(fn), dict) else {}
            diff = info.get("difficulty")
            ready = diff in MAIN_DIFFICULTIES
            items.append({"type": "admin_level", "file": fn, "data": data,
                          "name": str(info.get("name") or data.name) if ready else data.name,
                          "sub": ("Main level  -  " + fn) if ready
                          else "Not set up yet  -  ENTER to pick its name and difficulty",
                          "tag": diff if ready else "NEEDS SETUP",
                          "col": DIFF_COLOR[diff] if ready else (255, 160, 90),
                          "modes": data.mode_list(), "best": None})
        self.admin_files = len(items) - 1
        self.admin_scan = 0
        self.set_list("admin", items, min(sel, len(items) - 1))

    def admin_import(self, path):
        """A level file dropped on the window while on the MAIN LEVELS screen."""
        try:
            with open(path) as f:
                LevelData.from_json(json.load(f))          # make sure it's a real level
            os.makedirs(MAIN_DIR, exist_ok=True)
            dest = unique_level_path(os.path.splitext(os.path.basename(path))[0], MAIN_DIR)
            with open(path, "rb") as src, open(dest, "wb") as out:
                out.write(src.read())
        except Exception:
            self.say("That isn't a level file")
            return
        self.go_admin(len(self.items))
        self.say("Added - now pick its name and difficulty")

    def open_main_setup(self, it):
        if it["type"] == "admin_builtin":
            d = it["level"]
            self.msetup = {"key": "builtin:" + d.base_name, "builtin": True, "name": d.name,
                           "diff": d.difficulty, "hidden": d.hidden, "sel": 0, "err": "",
                           "label": "built-in level: " + d.base_name}
        else:
            info = self.main_meta().get(it["file"]) or {}
            diff = info.get("difficulty") if info.get("difficulty") in MAIN_DIFFICULTIES else "HARD"
            self.msetup = {"key": it["file"], "file": it["file"], "builtin": False,
                           "name": str(info.get("name") or it["data"].name), "diff": diff,
                           "hidden": False, "sel": 0, "err": "", "label": "file: " + it["file"]}
        self.state = "mainsetup"

    def msetup_geom(self):
        box = pygame.Rect(0, 0, 680, 330)
        box.center = (W // 2, H // 2 + 20)
        name = pygame.Rect(box.x + 30, box.y + 92, box.w - 60, 42)
        diffs = [pygame.Rect(box.x + 30 + i * 104, box.y + 180, 98, 40)
                 for i in range(len(MAIN_DIFFICULTIES))]
        btns = {"save": pygame.Rect(box.x + 30, box.bottom - 62, 190, 42),
                "remove": pygame.Rect(box.x + 232, box.bottom - 62, 190, 42),
                "back": pygame.Rect(box.right - 150, box.bottom - 62, 120, 42)}
        return box, name, diffs, btns

    def msetup_save(self):
        m = self.msetup
        name = " ".join(m["name"].split())
        if not name:
            m["err"] = "Give the level a name"
            return
        meta = self.main_meta()
        meta[m["key"]] = {"name": name[:NAME_MAX], "difficulty": m["diff"]}
        if m["builtin"] and m["hidden"]:
            meta[m["key"]]["hidden"] = True
        os.makedirs(MAIN_DIR, exist_ok=True)
        write_json(MAIN_META, meta)
        self.say("%s is now a main level (%s)" % (name, m["diff"]))
        self.go_admin()

    def msetup_remove(self):
        """Take a level out of the main levels (deletes its copy in the folder).
        Built-in levels can't be deleted - they're hidden from the list instead."""
        m = self.msetup
        meta = self.main_meta()
        if m["builtin"]:
            o = dict(meta.get(m["key"]) or {})
            o["hidden"] = not m["hidden"]
            meta[m["key"]] = o
            os.makedirs(MAIN_DIR, exist_ok=True)
            write_json(MAIN_META, meta)
            self.say(("%s is hidden from the level list" if o["hidden"]
                      else "%s is back in the level list") % m["name"])
            self.go_admin()
            return
        meta.pop(m["file"], None)
        write_json(MAIN_META, meta)
        try:
            os.remove(os.path.join(MAIN_DIR, m["file"]))
        except OSError:
            pass
        self.say("Removed from the main levels")
        self.go_admin()

    def msetup_event(self, e):
        m = self.msetup
        box, name, diffs, btns = self.msetup_geom()
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            if name.collidepoint(e.pos):
                m["sel"] = 0
            for i, r in enumerate(diffs):
                if r.collidepoint(e.pos):
                    m["diff"], m["sel"] = MAIN_DIFFICULTIES[i], 1
            if btns["save"].collidepoint(e.pos):
                self.msetup_save()
            elif btns["remove"].collidepoint(e.pos):
                self.msetup_remove()
            elif btns["back"].collidepoint(e.pos):
                self.go_admin()
            return
        if e.type != pygame.KEYDOWN:
            return
        k = e.key
        cmd = e.mod & (pygame.KMOD_CTRL | pygame.KMOD_META)
        if k == pygame.K_ESCAPE:
            self.go_admin()
        elif k in (pygame.K_RETURN, pygame.K_KP_ENTER):
            self.msetup_save()
        elif k in (pygame.K_TAB, pygame.K_UP, pygame.K_DOWN):
            m["sel"] = 1 - m["sel"]
        elif m["sel"] == 1 and k in (pygame.K_LEFT, pygame.K_RIGHT, pygame.K_a, pygame.K_d):
            i = MAIN_DIFFICULTIES.index(m["diff"])
            d = -1 if k in (pygame.K_LEFT, pygame.K_a) else 1
            m["diff"] = MAIN_DIFFICULTIES[(i + d) % len(MAIN_DIFFICULTIES)]
        elif m["sel"] == 0:
            if k == pygame.K_BACKSPACE:
                m["name"] = m["name"][:-1]
            elif cmd and k == pygame.K_v:
                m["name"] = (m["name"] + self.clipboard_text())[:NAME_MAX]
            elif e.unicode and e.unicode.isprintable() and not cmd and len(m["name"]) < NAME_MAX:
                m["name"] += e.unicode
                m["err"] = ""

    def draw_msetup(self):
        s = self.screen
        m = self.msetup
        self.draw_menu_bg()
        t = self.big.render("MAIN LEVEL", True, (255, 255, 255))
        s.blit(t, (W // 2 - t.get_width() // 2, 14))
        box, name, diffs, btns = self.msetup_geom()
        pygame.draw.rect(s, (20, 24, 50), box, border_radius=14)
        pygame.draw.rect(s, DIFF_COLOR[m["diff"]], box, 3, border_radius=14)
        st = self.small.render(m["label"], True, (150, 160, 200))
        s.blit(st, (box.centerx - st.get_width() // 2, box.y + 16))
        if m["err"]:
            et = self.font.render(m["err"], True, (255, 110, 110))
            s.blit(et, (box.centerx - et.get_width() // 2, box.y + 38))
        s.blit(self.font.render("Name", True, (220, 225, 245)), (name.x, name.y - 24))
        pygame.draw.rect(s, (8, 8, 20), name, border_radius=8)
        pygame.draw.rect(s, (255, 230, 90) if m["sel"] == 0 else (60, 68, 120), name, 2,
                         border_radius=8)
        cursor = "|" if m["sel"] == 0 and (pygame.time.get_ticks() // 450) % 2 == 0 else ""
        img = self.mid.render(m["name"] + cursor, True, (255, 255, 255))
        s.blit(img, (name.x + 12, name.centery - img.get_height() // 2))
        s.blit(self.font.render("Difficulty", True, (220, 225, 245)),
               (diffs[0].x, diffs[0].y - 24))
        mx, my = pygame.mouse.get_pos()
        for r, d in zip(diffs, MAIN_DIFFICULTIES):
            on = d == m["diff"]
            col = DIFF_COLOR[d]
            pygame.draw.rect(s, (40, 46, 90) if on else (16, 19, 42), r, border_radius=8)
            pygame.draw.rect(s, col if (on or r.collidepoint((mx, my))) else (60, 68, 120), r,
                             3 if on else 2, border_radius=8)
            tt = self.font.render(d, True, col)
            s.blit(tt, (r.centerx - tt.get_width() // 2, r.centery - tt.get_height() // 2))
        if m["sel"] == 1:
            r = diffs[MAIN_DIFFICULTIES.index(m["diff"])]
            pygame.draw.rect(s, (255, 230, 90), r.inflate(8, 8), 2, border_radius=10)
        rlabel = ("SHOW" if m["hidden"] else "HIDE") if m["builtin"] else "REMOVE"
        for key, label, col in (("save", "SAVE", (90, 230, 120)),
                                ("remove", rlabel, (255, 110, 110)),
                                ("back", "BACK", (200, 205, 230))):
            r = btns[key]
            hov = r.collidepoint((mx, my))
            pygame.draw.rect(s, (34, 40, 80) if hov else (16, 19, 42), r, border_radius=10)
            pygame.draw.rect(s, col, r, 3 if hov else 2, border_radius=10)
            tt = self.font.render(label, True, col)
            s.blit(tt, (r.centerx - tt.get_width() // 2, r.centery - tt.get_height() // 2))
        h = self.small.render("type the name   TAB: name / difficulty   LEFT/RIGHT: difficulty"
                              "   ENTER: save   ESC: back", True, (130, 140, 180))
        s.blit(h, (W // 2 - h.get_width() // 2, H - 24))
        self.present()

    @staticmethod
    def guest_progress():
        """The Guest save's progress entries (best %, coins, skins, unlocks)."""
        guest = load_save()
        return {k: v for k, v in guest.items() if k != "__settings__" and v}

    def merge_guest(self):
        """Copy Guest progress into the signed-in account, keeping the best of both."""
        if not self.account:
            return
        guest = self.guest_progress()
        levels = coins = 0
        for k, v in guest.items():
            if k == "__unlocks__" and isinstance(v, dict):
                u = dict(self.save.get("__unlocks__") or {})
                for name, on in v.items():
                    u[name] = bool(u.get(name)) or bool(on)
                self.save["__unlocks__"] = u
            elif k == "__skins__" and isinstance(v, dict):
                mine = dict(self.save.get("__skins__") or {})
                for m, sid in v.items():
                    mine.setdefault(m, sid)          # keep skins you already picked here
                self.save["__skins__"] = mine
                self.skins = dict(mine)
            elif k.endswith("#coins") and isinstance(v, list):
                have = {tuple(c) for c in self.save.get(k, [])}
                new = have | {tuple(c) for c in v}
                coins += len(new) - len(have)
                self.save[k] = sorted(list(c) for c in new)
            elif isinstance(v, (int, float)) and not k.startswith("__"):
                if v > self.save.get(k, 0):
                    self.save[k] = v
                    levels += 1
        write_save(self.save)
        self.check_top1()
        self.say("Guest progress added to %s: %d level%s improved, %d coin%s" % (
            self.account, levels, "" if levels == 1 else "s", coins, "" if coins == 1 else "s"))

    def sign_in(self, user):
        self.load_profile(user)
        self.accounts["current"] = account_key(user["name"])
        store_current(self.accounts["current"])
        self.check_top1()

    def sign_out(self):
        name = self.account
        self.load_profile(None)
        self.accounts["current"] = None
        store_current(None)
        if name:
            self.say("Signed out of %s - playing as Guest" % name)

    def open_account(self, mode, back="home"):
        if not self.acc_root:
            self.say(self.NEED_ONLINE)
            return
        self.acct = {"mode": mode, "fields": ["", "", ""], "sel": 0, "err": "",
                     "show": False, "back": back}
        self.state = "account"

    def account_fields(self):
        return 3 if self.acct["mode"] == "signup" else 2

    def account_geom(self):
        n = self.account_fields()
        box = pygame.Rect(0, 0, 520, 170 + n * 78)
        box.center = (W // 2, H // 2 + 10)
        fields = [pygame.Rect(box.x + 30, box.y + 96 + i * 78, box.w - 60, 40) for i in range(n)]
        y = fields[-1].bottom + 20
        btns = {"go": pygame.Rect(box.x + 30, y, 220, 44),
                "back": pygame.Rect(box.right - 150, y, 120, 44),
                "show": pygame.Rect(fields[1].right - 70, fields[1].y + 6, 62, 28),
                "switch": pygame.Rect(box.x + 30, box.bottom + 10, box.w - 60, 30)}
        return box, fields, btns

    def account_submit(self):
        a = self.acct
        name, pw, pw2 = a["fields"]
        if a["mode"] == "signup":
            if pw != pw2:
                a["err"] = "The two passwords don't match"
                return
            self.accounts = load_accounts(self.acc_root)     # see names others just took
            if self.acc_root and not os.path.isdir(self.acc_root):
                a["err"] = "Can't reach the online accounts folder"
                return
            err = create_account(self.accounts, name, pw)
            if not err:
                err = save_new_account(self.accounts, account_key(name), self.acc_root)
                if err:
                    self.accounts["users"].pop(account_key(name), None)
            if err:
                a["err"] = err
                return
            user = self.accounts["users"][account_key(name)]
            self.sign_in(user)
            self.say("Account created - welcome, %s!" % user["name"]
                     + ("  (Settings > Bring in Guest progress)" if self.guest_progress() else ""))
        else:
            self.accounts = load_accounts(self.acc_root)
            user = check_login(self.accounts, name, pw)
            if not user and self.acc_root and not os.path.isdir(self.acc_root):
                a["err"] = "Can't reach the online accounts folder"
                return
            if not user:
                a["err"] = "Wrong name or password"
                a["fields"][1] = ""
                return
            self.sign_in(user)
            self.say("Welcome back, %s!" % user["name"]
                     + ("  (Settings > Bring in Guest progress)" if self.guest_progress() else ""))
        self.account_leave()

    def account_leave(self):
        back = self.acct["back"]
        self.acct = None
        if back == "settings":
            self.open_settings("home")
        else:
            self.go_home()

    def account_event(self, e):
        a = self.acct
        n = self.account_fields()
        box, fields, btns = self.account_geom()
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            if btns["show"].collidepoint(e.pos):
                a["show"] = not a["show"]
                return
            for i, r in enumerate(fields):
                if r.collidepoint(e.pos):
                    a["sel"] = i
                    return
            if btns["go"].collidepoint(e.pos):
                self.account_submit()
            elif btns["back"].collidepoint(e.pos):
                self.account_leave()
            elif btns["switch"].collidepoint(e.pos):
                self.open_account("signin" if a["mode"] == "signup" else "signup", a["back"])
            return
        if e.type != pygame.KEYDOWN:
            return
        cmd = e.mod & (pygame.KMOD_CTRL | pygame.KMOD_META)
        k = e.key
        if k == pygame.K_ESCAPE:
            self.account_leave()
        elif k in (pygame.K_RETURN, pygame.K_KP_ENTER):
            if a["sel"] < n - 1:
                a["sel"] += 1                        # ENTER moves on to the next box...
            else:
                self.account_submit()                # ...and on the last one, submits
        elif k == pygame.K_TAB:
            a["sel"] = (a["sel"] + (-1 if e.mod & pygame.KMOD_SHIFT else 1)) % n
        elif k == pygame.K_DOWN:
            a["sel"] = (a["sel"] + 1) % n
        elif k == pygame.K_UP:
            a["sel"] = (a["sel"] - 1) % n
        elif k == pygame.K_BACKSPACE:
            a["fields"][a["sel"]] = a["fields"][a["sel"]][:-1]
            a["err"] = ""
        elif cmd and k == pygame.K_v:
            limit = ACCOUNT_NAME_MAX if a["sel"] == 0 else 40
            a["fields"][a["sel"]] = (a["fields"][a["sel"]] + self.clipboard_text())[:limit]
        elif e.unicode and e.unicode.isprintable() and not cmd:
            limit = ACCOUNT_NAME_MAX if a["sel"] == 0 else 40
            if len(a["fields"][a["sel"]]) < limit:
                a["fields"][a["sel"]] += e.unicode
                a["err"] = ""

    def draw_account(self):
        s = self.screen
        a = self.acct
        self.draw_menu_bg()
        signup = a["mode"] == "signup"
        t = self.big.render("SIGN UP" if signup else "SIGN IN", True, (255, 255, 255))
        s.blit(t, (W // 2 - t.get_width() // 2, 8))
        box, fields, btns = self.account_geom()
        pygame.draw.rect(s, (20, 24, 50), box, border_radius=14)
        pygame.draw.rect(s, (120, 230, 255), box, 3, border_radius=14)
        sub = ("Pick a name nobody on this computer has used, and a password"
               if signup else "Sign in to your account")
        st = self.small.render(sub, True, (150, 160, 200))
        s.blit(st, (box.centerx - st.get_width() // 2, box.y + 16))
        labels = ["Name", "Password", "Password again"]
        cursor = "|" if (pygame.time.get_ticks() // 450) % 2 == 0 else ""
        mx, my = pygame.mouse.get_pos()
        for i, r in enumerate(fields):
            on = i == a["sel"]
            s.blit(self.font.render(labels[i], True, (220, 225, 245)), (r.x, r.y - 24))
            pygame.draw.rect(s, (8, 8, 20), r, border_radius=8)
            pygame.draw.rect(s, (255, 230, 90) if on else (60, 68, 120), r, 2, border_radius=8)
            v = a["fields"][i]
            if i > 0 and not a["show"]:
                v = "*" * len(v)
            img = self.mid.render(v + (cursor if on else ""), True, (255, 255, 255))
            s.blit(img, (r.x + 12, r.centery - img.get_height() // 2))
        sh = btns["show"]
        pygame.draw.rect(s, (40, 46, 90), sh, border_radius=6)
        tt = self.small.render("HIDE" if a["show"] else "SHOW", True, (220, 225, 245))
        s.blit(tt, (sh.centerx - tt.get_width() // 2, sh.centery - tt.get_height() // 2))
        for key, label, colr in (("go", "CREATE ACCOUNT" if signup else "SIGN IN",
                                  (90, 230, 120)), ("back", "BACK", (200, 205, 230))):
            r = btns[key]
            hov = r.collidepoint((mx, my))
            pygame.draw.rect(s, (34, 40, 80) if hov else (16, 19, 42), r, border_radius=10)
            pygame.draw.rect(s, colr, r, 3 if hov else 2, border_radius=10)
            tt = self.font.render(label, True, colr)
            s.blit(tt, (r.centerx - tt.get_width() // 2, r.centery - tt.get_height() // 2))
        if a["err"]:
            et = self.font.render(a["err"], True, (255, 110, 110))
            s.blit(et, (box.centerx - et.get_width() // 2, box.y + 42))
        sw = btns["switch"]
        msg = "Already have an account?  SIGN IN" if signup else "No account yet?  SIGN UP"
        tt = self.font.render(msg, True, (255, 230, 90) if sw.collidepoint((mx, my))
                              else (180, 190, 230))
        s.blit(tt, (sw.centerx - tt.get_width() // 2, sw.centery - tt.get_height() // 2))
        h = self.small.render("TAB / ENTER: next box   ENTER on the last box: "
                              + ("create" if signup else "sign in") + "   ESC: back",
                              True, (130, 140, 180))
        s.blit(h, (W // 2 - h.get_width() // 2, H - 22))
        self.present()

    def say(self, msg):
        self.toast, self.toast_t = msg, 150

    def apply_fullscreen(self):
        """Make the window match settings['fullscreen'] (and re-read the display
        surface, which pygame may replace)."""
        want = self.settings["fullscreen"]
        try:
            cur = pygame.display.is_fullscreen()
        except (AttributeError, pygame.error):
            cur = self._fs
        if cur != want:
            ok = False
            try:
                ok = bool(pygame.display.toggle_fullscreen())
            except pygame.error:
                ok = False
            if not ok:                         # fall back to rebuilding the window
                self.screen = make_display(want)
        self.screen = pygame.display.get_surface() or self.screen
        try:
            actual = pygame.display.is_fullscreen()
        except (AttributeError, pygame.error):
            actual = want
        self._fs = actual
        self.settings["fullscreen"] = actual
        if cur and not actual:                 # just left fullscreen
            self.restore_window_size()

    def restore_window_size(self):
        """Back to the default window size after leaving fullscreen."""
        size = self._default_window or (W, H)
        try:
            win = pygame.Window.from_display_module()
            win.size = size
            return
        except (AttributeError, TypeError, ValueError, pygame.error):
            pass
        self.screen = make_display(False)       # fallback: rebuilding resets the size
        self.screen = pygame.display.get_surface() or self.screen

    def toggle_fullscreen(self):
        self.settings["fullscreen"] = not self.settings["fullscreen"]
        self.apply_fullscreen()
        self.save_settings()
        self.say("Fullscreen on" if self.settings["fullscreen"] else "Fullscreen off")
        if self.state == "settings":
            self.items = self.settings_items()

    @staticmethod
    def is_fullscreen_hotkey(e):
        if e.key == pygame.K_F11:
            return True
        if e.key in (pygame.K_RETURN, pygame.K_KP_ENTER) and e.mod & pygame.KMOD_ALT:
            return True
        return e.key == pygame.K_f and bool(e.mod & (pygame.KMOD_CTRL | pygame.KMOD_META))

    def present(self):
        """Finish a frame: draw the toast and optional FPS counter, then flip."""
        if self.toast_t > 0:
            tt = self.font.render(self.toast, True, (255, 255, 255))
            box = pygame.Rect(0, 0, tt.get_width() + 24, 34)
            if self.state in ("play", "editor"):
                box.midtop = (W // 2, 64)         # below the in-game HUD / editor bar
            else:
                box.topleft = (12, 12)            # menus: keep titles and cards clear
            pygame.draw.rect(self.screen, (20, 24, 50), box, border_radius=8)
            pygame.draw.rect(self.screen, (255, 230, 90), box, 2, border_radius=8)
            self.screen.blit(tt, (box.x + 12, box.y + 8))
        if self.settings["fps"]:
            fps = self.clock.get_fps()
            colr = (90, 230, 120) if fps >= 55 else (255, 220, 70) if fps >= 30 else (255, 90, 90)
            txt = self.small.render("%d FPS" % round(fps), True, colr)
            box = pygame.Rect(0, 0, txt.get_width() + 12, txt.get_height() + 6)
            box.bottomright = (W - 6, H - 6)
            pygame.draw.rect(self.screen, (8, 8, 20), box, border_radius=5)
            self.screen.blit(txt, (box.x + 6, box.y + 3))
        if self.state != "play":
            self.draw_fs_button()
        pygame.display.flip()

    def draw_fs_button(self):
        s = self.screen
        r = FS_BUTTON
        hover = r.collidepoint(pygame.mouse.get_pos())
        on = self.settings["fullscreen"]
        pygame.draw.rect(s, (40, 46, 90) if hover else (20, 24, 52), r, border_radius=7)
        pygame.draw.rect(s, (255, 230, 90) if hover else (90, 100, 160), r, 2, border_radius=7)
        cx, cy = r.center
        colr = (255, 255, 255) if hover else (200, 210, 240)
        for sx in (-1, 1):
            for sy in (-1, 1):
                if on:      # "exit fullscreen": corners pointing inward
                    pts = [(cx + sx * 8, cy + sy * 3), (cx + sx * 3, cy + sy * 3),
                           (cx + sx * 3, cy + sy * 8)]
                else:       # "enter fullscreen": corners pointing outward
                    pts = [(cx + sx * 8, cy + sy * 3), (cx + sx * 8, cy + sy * 8),
                           (cx + sx * 3, cy + sy * 8)]
                pygame.draw.lines(s, colr, False, pts, 2)
        if hover:
            tip = self.small.render("Exit fullscreen (F11)" if on else "Fullscreen (F11)",
                                    True, (255, 255, 255))
            box = pygame.Rect(0, 0, tip.get_width() + 14, tip.get_height() + 8)
            box.topright = (r.right, r.bottom + 6)
            pygame.draw.rect(s, (20, 24, 50), box, border_radius=6)
            pygame.draw.rect(s, (255, 230, 90), box, 1, border_radius=6)
            s.blit(tip, (box.x + 7, box.y + 4))

    def settings_items(self):
        items = []
        for key, name, sub in SETTING_INFO:
            if key == "merge_guest" and not (self.account and self.guest_progress()):
                continue                       # only shown when it can do something
            v = self.settings.get(key)
            if key == "merge_guest":
                tag, col = "ENTER", (90, 230, 120)
            elif key == "account":
                tag = self.account or "GUEST"
                col = (120, 230, 255) if self.account else (150, 155, 185)
                sub = sub + ("   - ENTER: sign out" if self.account else "   - ENTER: sign in")
            elif key == "default_practice":
                tag, col = ("PRACTICE" if v else "NORMAL"), (255, 210, 90)
            elif key == "wave_hold":
                tag, col = ("HOLD" if v else "CLICK"), (110, 150, 255)
            else:
                tag, col = ("ON" if v else "OFF"), ((90, 230, 120) if v else (150, 155, 185))
            items.append({"type": "setting", "key": key, "name": name, "sub": sub,
                          "tag": tag, "col": col, "modes": [], "best": None})
        return items

    def open_settings(self, came_from):
        self.settings_return = came_from
        if came_from == "play":
            self.pause_music()
        self.set_list("settings", self.settings_items(), 0)

    def close_settings(self):
        if self.settings_return == "play":
            self.state = "play"
            self.input_lock = True          # ignore keys held while in the menu
            self.player.wave_hold = self.settings["wave_hold"]
            if not self.settings["music"]:
                self.stop_music()
            elif self.music_on:
                self.resume_music()
            elif self.player.alive and not self.finished:
                self.start_level_music()
        else:
            self.go_home()
            self.sel = 4

    # ---- navigation ---------------------------------------------------------------
    def quit(self):
        pygame.quit()
        sys.exit()

    def go_home(self):
        self.state = "home"
        self.sel = 0

    def set_list(self, state, items, sel=0):
        self.state = state
        self.items = items
        self.sel = max(0, min(sel, len(items) - 1))
        self.scroll = 0
        self.confirm_del = None
        self.fix_scroll()

    def fix_scroll(self):
        n = len(self.items)
        if self.sel < self.scroll:
            self.scroll = self.sel
        elif self.sel >= self.scroll + VISIBLE_CARDS:
            self.scroll = self.sel - VISIBLE_CARDS + 1
        self.scroll = max(0, min(self.scroll, max(0, n - VISIBLE_CARDS)))

    def level_info(self, d):
        """(modes, number of coins) of a level - cached for the built-in ones."""
        if d.path is None and d.key in self._mode_cache:
            return self._mode_cache[d.key]
        lv = Level(d)
        info = ([m for m, _ in lv.sections], len(lv.coins))
        if d.path is None:                    # custom levels can change, don't cache
            self._mode_cache[d.key] = info
        return info

    def level_modes(self, d):
        return self.level_info(d)[0]

    def level_coins(self, d):
        return self.level_info(d)[1]

    def reload_levels(self):
        self.custom = load_custom_levels(LEVEL_DIR)
        self.other = load_custom_levels(OTHER_DIR)
        mine = [custom_def(d) for d in self.custom]
        theirs = [custom_def(d, "OTHER") for d in self.other]
        built = self.builtin_levels()
        by_name = {d.base_name: d for d in built}
        ranked = [by_name[r["name"]] for r in RANKED_LEVELS if r["name"] in by_name]
        main = built + self.load_main_levels()          # all main levels, by difficulty
        main.sort(key=lambda d: DIFF_ORDER.index(d.difficulty) if d.difficulty in DIFF_ORDER
                  else len(DIFF_ORDER))
        self.tab_lists = [main, mine, theirs, main + mine + theirs, ranked, []]  # [] = Online

    def level_item(self, d):
        if d.key.startswith("main:"):        # main levels can't be deleted from the list
            it = self.level_item_raw(d)
            it["path"] = None
            return it
        return self.level_item_raw(d)

    def level_item_raw(self, d):
        return {"name": d.title, "sub": d.blurb, "tag": d.difficulty,
                "col": DIFF_COLOR[d.difficulty], "modes": self.level_modes(d),
                "best": self.save.get(d.key, 0), "path": d.path,
                "coins": (len(self.save.get(d.key + "#coins", [])), self.level_coins(d))}

    def go_select(self, sel=0, tab=None):
        if tab is not None:
            self.tab = tab
        self.reload_levels()
        self.levels = self.tab_lists[self.tab]
        self.empty_lines = {
            1: ["You haven't built any levels yet.",
                "Choose BUILD LEVELS on the home screen to make one."],
            2: ["No downloaded levels yet.",
                "Get some from the Online tab, drag a level .json onto this window,",
                "or press O to open the folder and drop it in:", OTHER_DIR],
        }.get(self.tab, [])
        if self.tab == ONLINE_TAB:
            self.fetch_online()
            items = self.online_items()
        elif self.tab == RANKS_TAB:
            items = [self.rank_item(d) for d in self.levels]
        else:
            items = [self.level_item(d) for d in self.levels]
        self.set_list("select", items, sel)

    @staticmethod
    def move_old_downloads():
        """'Other Levels' is now 'Downloaded Levels': move files from the old folder."""
        if not os.path.isdir(OLD_OTHER_DIR):
            return
        try:
            if not os.path.exists(OTHER_DIR):
                os.rename(OLD_OTHER_DIR, OTHER_DIR)
                return
            for fn in os.listdir(OLD_OTHER_DIR):
                src, dst = os.path.join(OLD_OTHER_DIR, fn), os.path.join(OTHER_DIR, fn)
                if not os.path.exists(dst):
                    os.rename(src, dst)
            if not os.listdir(OLD_OTHER_DIR):
                os.rmdir(OLD_OTHER_DIR)
        except OSError:
            pass

    # ---- online levels -------------------------------------------------------------
    def fetch_online(self, force=False):
        if self.online["status"] == "loading" or (self.online["status"] == "ok" and not force):
            return
        self.online = {"status": "loading"}
        threading.Thread(target=fetch_online_levels, args=(self.online,), daemon=True).start()

    def fetch_online_songs(self, force=False):
        o = self.online_songs
        if o["status"] == "loading" or (o["status"] == "ok" and not force):
            return
        self.online_songs = {"status": "loading"}
        threading.Thread(target=fetch_online_music, args=(self.online_songs,),
                         daemon=True).start()

    def online_items(self):
        st = self.online["status"]
        if st != "ok":
            msg = {"loading": ("Loading levels from GitHub...", "github.com/" + REPO),
                   "error": (self.online.get("err", "Couldn't load the online levels"),
                             "Check your internet connection, then press R to try again"),
                   "idle": ("Loading levels from GitHub...", "")}[st]
            return [{"type": "online_msg", "name": msg[0], "sub": msg[1], "tag": "",
                     "col": (150, 160, 200), "modes": [], "best": None}]
        items = []
        for lv in self.online["levels"]:
            have = os.path.isfile(os.path.join(OTHER_DIR, lv["file"]))
            title = lv["name"] + ((" by " + lv["author"]) if lv["author"] else "")
            items.append({"type": "online", "info": lv, "name": title,
                          "sub": ("Downloaded - ENTER to play" if have else
                                  "%d objects%s  -  ENTER to download" % (
                                      lv["objects"], "  -  has music" if lv["music"] else "")),
                          "tag": "DOWNLOADED" if have else "GET",
                          "col": (90, 230, 120) if have else (120, 200, 255),
                          "modes": [m for m in lv["modes"] if m in ACCENT], "best": None})
        if not items:
            items = [{"type": "online_msg", "name": "No levels online yet",
                      "sub": "github.com/%s - levels folder" % REPO, "tag": "",
                      "col": (150, 160, 200), "modes": [], "best": None}]
        return items

    def online_activate(self, i):
        it = self.items[i]
        if it["type"] != "online":
            return
        lv = it["info"]
        dest = os.path.join(OTHER_DIR, lv["file"])
        if not os.path.isfile(dest):
            try:
                os.makedirs(OTHER_DIR, exist_ok=True)
                with open(dest, "wb") as f:
                    f.write(lv["raw"])
            except OSError:
                self.say("Couldn't save the level")
                return
            msg = "Downloaded %s" % lv["name"]
            song = os.path.basename(lv["music"]) if lv["music"] else ""
            if song and not music_path(song):
                threading.Thread(target=self.fetch_level_song, args=(song,),
                                 daemon=True).start()
                msg += " - getting its song too"
            self.say(msg + "  (ENTER to play)")
            self.go_select(i, ONLINE_TAB)
            return
        for k, d in enumerate(self.tab_lists[DOWNLOADED_TAB]):     # play it
            if d.path and os.path.basename(d.path) == lv["file"]:
                self.go_select(k, DOWNLOADED_TAB)
                self.start_level(k)
                return

    def fetch_level_song(self, song):
        try:
            download_song(song)
        except Exception:
            pass

    def rank_item(self, d):
        """A level card for the Ranks tab: maker, verifier, victors and frame perfects."""
        base = getattr(d, "base_name", d.name)       # (the name before any rename)
        info = next(r for r in RANKED_LEVELS if r["name"] == base)
        it = self.level_item(d)
        it["sub"] = "Made by %s     Verified by %s" % (info["maker"], info["verifier"])
        it["sub2"] = "Victors: %s     Frame perfects: %s" % (
            ", ".join(info["victors"]) or "none yet", info["frame_perfects"])
        if self.save.get(d.key, 0) >= 100:
            it["sub2"] += "     - you beat it!"
        return it

    def set_tab(self, i):
        self.go_select(0, i)

    def go_mylevels(self, page="list", sel=0):
        self.my_page = page
        items = []
        if page == "list":
            self.custom = load_custom_levels(LEVEL_DIR)
            items.append({"type": "new", "name": "+ NEW LEVEL", "sub": "Start with an empty course",
                          "tag": "CREATE", "col": (90, 230, 120), "modes": [], "best": None})
            items.append({"type": "templates", "name": "COPY A LEVEL",
                          "sub": "Use a built-in or imported level as a starting point",
                          "tag": "TEMPLATE", "col": (120, 200, 255), "modes": [], "best": None})
            for d in self.custom:
                items.append({"type": "custom", "data": d, "name": d.name, "path": d.path,
                              "sub": d.description or "%d objects" % d.object_count(),
                              "tag": "CUSTOM", "col": DIFF_COLOR["CUSTOM"],
                              "modes": d.mode_list(), "best": None})
        else:
            defs = list(LEVELS) + [custom_def(d, "OTHER") for d in load_custom_levels(OTHER_DIR)]
            for ld in defs:
                items.append({"type": "template", "level": ld, "name": ld.title,
                              "sub": "Copy this level into the editor",
                              "tag": ld.difficulty, "col": DIFF_COLOR[ld.difficulty],
                              "modes": self.level_modes(ld), "best": None})
        self.set_list("mylevels", items, sel)

    def copy_selected(self):
        """Duplicate one of your levels as '[Level Name] Copy'."""
        if self.state != "mylevels" or self.my_page != "list" or not self.items:
            return
        it = self.items[self.sel]
        if it.get("type") != "custom":
            return
        src = it["data"]
        data = LevelData.from_json(src.to_json())            # a full, independent copy
        data.name = copy_name(src.name, {d.name for d in self.custom})
        try:
            os.makedirs(LEVEL_DIR, exist_ok=True)
            data.path = unique_level_path(data.name)
            with open(data.path, "w") as f:
                json.dump(data.to_json(), f)
        except OSError:
            self.say("Couldn't copy the level")
            return
        self.say("Copied as: " + data.name)
        self.go_mylevels("list", 0)
        for i, item in enumerate(self.items):                 # select the new copy
            if item.get("path") == data.path:
                self.sel = i
                self.fix_scroll()
                break

    def export_selected(self):
        """Copy a level file (description included) to your Desktop so you can share it."""
        if self.state != "mylevels" or self.my_page != "list" or not self.items:
            return
        it = self.items[self.sel]
        if it.get("type") != "custom" or not it.get("path"):
            return
        home = os.path.expanduser("~")
        dest_dir = os.path.join(home, "Desktop")
        if not os.path.isdir(dest_dir):
            dest_dir = home
        dest = unique_level_path(it["name"], dest_dir)
        try:
            data = it["data"]
            data.author = self.account or ""             # your account name goes with it
            j = data.to_json(embed_music=True)          # ...and so does its song
            with open(dest, "w") as f:
                json.dump(j, f)
        except OSError:
            self.say("Couldn't export the level")
            return
        msg = "Exported to " + os.path.join(os.path.basename(dest_dir), os.path.basename(dest))
        if not self.account:
            msg += "  (sign in to put your name on it)"
        self.say(msg)

    def card_buttons(self, slot):
        r = self.card_rect(slot)
        return {"copy": pygame.Rect(r.right - 176, r.bottom - 34, 76, 24),
                "export": pygame.Rect(r.right - 94, r.bottom - 34, 78, 24)}

    def open_folder(self, path):
        try:
            os.makedirs(path, exist_ok=True)
            if sys.platform == "darwin":
                subprocess.Popen(["open", path])
            elif sys.platform.startswith("win"):
                os.startfile(path)
            else:
                subprocess.Popen(["xdg-open", path])
            return True
        except Exception:
            self.say("Couldn't open the folder: " + path)
            return False

    def import_level(self, path):
        """Copy a level .json (e.g. dragged onto the window) into the Other Levels folder."""
        try:
            if not path.lower().endswith(".json"):
                raise ValueError("not a .json file")
            with open(path) as f:
                j = json.load(f)
            if not isinstance(j, dict) or not ({"cells", "portals", "start_mode"} & set(j)):
                raise ValueError("not a Python Dash level")
            data = LevelData.from_json(j)
            os.makedirs(OTHER_DIR, exist_ok=True)
            base = slugify(data.name)
            dest = os.path.join(OTHER_DIR, base + ".json")
            i = 2
            while os.path.exists(dest):
                dest = os.path.join(OTHER_DIR, "%s-%d.json" % (base, i))
                i += 1
            with open(dest, "w") as f:
                json.dump(data.to_json(), f)
        except Exception:
            self.say("Couldn't import that file")
            return
        self.say("Imported: " + data.name)
        if self.state == "select":
            self.go_select(0, DOWNLOADED_TAB)     # show it on the Downloaded Levels tab
        elif self.state == "mylevels" and self.my_page == "templates":
            self.go_mylevels("templates")

    def open_editor(self, data, named):
        self.editor = Editor(self, data, named)
        self.state = "editor"

    def list_activate(self, i):
        if not (0 <= i < len(self.items)):
            return
        if self.state == "select":
            if self.tab == ONLINE_TAB:
                self.online_activate(i)
            else:
                self.start_level(i)
            return
        it = self.items[i]
        if it.get("type") == "admin_folder":
            self.open_folder(MAIN_DIR)
            return
        if it.get("type") in ("admin_level", "admin_builtin"):
            self.open_main_setup(it)
            return
        t = it["type"]
        if t == "setting":
            key = it["key"]
            if key == "merge_guest":
                self.merge_guest()
                self.items = self.settings_items()
                self.sel = min(self.sel, len(self.items) - 1)
                return
            if key == "account":
                if self.account:
                    self.sign_out()
                    self.open_settings(self.settings_return)
                else:
                    self.open_account("signin", back="settings")
                return
            self.settings[key] = not self.settings[key]
            if key == "fullscreen":
                self.apply_fullscreen()
            self.save_settings()
            self.items = self.settings_items()
            return
        if t == "new":
            self.open_editor(LevelData("My Level"), named=False)
        elif t == "templates":
            self.go_mylevels("templates")
        elif t == "custom":
            self.open_editor(it["data"], named=True)
        elif t == "template":
            data = level_to_data(Level(it["level"]), ("Copy of " + it["level"].name)[:28])
            self.open_editor(data, named=False)
            self.editor.dirty = True

    def list_back(self):
        if self.state == "settings":
            self.close_settings()
        elif self.state == "mylevels" and self.my_page == "templates":
            self.go_mylevels("list")
        elif self.state == "admin":
            self.go_home()
        else:
            self.go_home()

    def delete_selected(self):
        """DELETE twice removes a level file (yours or imported) - never a built-in."""
        if self.state not in ("select", "mylevels") or not (0 <= self.sel < len(self.items)):
            return
        if self.state == "mylevels" and self.my_page != "list":
            return
        path = self.items[self.sel].get("path")
        if not path:
            return
        if self.confirm_del == self.sel:
            try:
                os.remove(path)
            except OSError:
                pass
            self.say("Level deleted")
            if self.state == "select":
                self.go_select(max(0, self.sel - 1))
            else:
                self.go_mylevels("list", self.sel - 1)
        else:
            self.confirm_del = self.sel

    # ---- level flow ---------------------------------------------------------------
    def begin_play(self, level):
        self.level = level
        self.palette = list(level.palette)
        self.paused = False
        self.new_unlocks = []
        self.attempt = 1
        self.particles = []
        self.state = "play"
        first = level.sections[0][0]
        self.bg = list(BG[first])
        self.accent = list(ACCENT[first])
        self.input_lock = True          # ignore the key that started the level

    def start_level(self, idx):
        self.level_idx = idx
        self.practice = self.settings["default_practice"]
        self.playtest = False
        self.playtest_sec, self.playtest_x = 0, None
        self.assisted = False
        self.begin_play(Level(self.levels[idx]))
        self.spawn(0)

    def start_playtest(self, data, from_x=None):
        defn = LevelDef(data.name or "Untitled", "CUSTOM", "", lambda lv, d=data: d.build(lv))
        level = Level(defn)
        self.playtest = True
        self.practice = True
        sec, px = 0, None
        if from_x is not None:
            px = max(float(from_x), 3.0 * B)
            sec = max(0, bisect.bisect_right(level.starts_px, px) - 1)
        self.playtest_sec, self.playtest_x = sec, px
        self.assisted = False
        self.begin_play(level)
        self.spawn(sec)

    def back_from_play(self):
        self.particles = []
        self.stop_music()
        if self.playtest:
            self.state = "editor"
        else:
            self.go_select(self.level_idx)

    def spawn(self, sec):
        self.cp_section = sec
        self.finished = False
        p = self.player
        kept = p.coins
        p.respawn(self.level, sec)
        if self.playtest_x is not None and sec == self.playtest_sec:
            p.x = self.playtest_x
            p.speed_mult = self.level.speed_at(p.x)
        p.wave_hold = self.settings["wave_hold"]
        if self.practice:          # practice keeps the coins you got before the checkpoint
            p.coins = frozenset(k for k in kept if k[0] * B < p.x)
        self.level.reset_runtime(p.x)
        self.start_level_music()

    # ---- music ----------------------------------------------------------------------
    def mixer_ready(self):
        if self.music_ok is None:
            try:
                if not pygame.mixer.get_init():
                    pygame.mixer.init()
                self.music_ok = True
            except pygame.error:
                self.music_ok = False
        return self.music_ok

    def play_music(self, path, start=0.0, force=False):
        if not path or not (force or self.settings["music"]) or not self.mixer_ready():
            return False
        try:
            if self.music_on != path:
                pygame.mixer.music.load(path)
                self.music_on = path
            try:
                pygame.mixer.music.play(start=max(0.0, start))
            except pygame.error:                     # some formats can't seek
                pygame.mixer.music.play()
            return True
        except pygame.error:
            self.music_on = None
            self.say("Couldn't play the song")
            return False

    def start_level_music(self):
        if self.level and self.level.music and self.settings["music"]:
            self.play_music(self.level.music, self.level.time_at(self.player.x))
        else:
            self.stop_music()

    def stop_music(self):
        if self.music_on and self.music_ok:
            try:
                pygame.mixer.music.stop()
            except pygame.error:
                pass

    def pause_music(self):
        if self.music_on and self.music_ok:
            try:
                pygame.mixer.music.pause()
            except pygame.error:
                pass

    def resume_music(self):
        if self.music_on and self.music_ok:
            try:
                pygame.mixer.music.unpause()
            except pygame.error:
                pass

    @staticmethod
    def clipboard_text():
        try:
            if hasattr(pygame, "scrap"):
                if not pygame.scrap.get_init():
                    pygame.scrap.init()
                t = pygame.scrap.get_text() if hasattr(pygame.scrap, "get_text") else None
                if t is None:
                    raw = pygame.scrap.get("text/plain;charset=utf-8") or \
                        pygame.scrap.get(pygame.SCRAP_TEXT)
                    t = raw.decode("utf-8", "ignore") if raw else ""
                return t.replace("\x00", "").strip()
        except Exception:
            pass
        return ""

    def respawn(self):
        self.attempt += 1
        self.assisted = False               # a fresh attempt starts clean
        self.spawn(self.cp_section if self.practice else self.playtest_sec)

    def progress_pct(self):
        total = self.level.end_col * B
        return max(0, min(100, int(self.player.x / total * 100)))

    def record_best(self, pct):
        # practice runs, editor playtests and assisted attempts (noclip / warping)
        # never count toward best % or completion
        if self.practice or self.playtest or self.assisted:
            return
        key = self.levels[self.level_idx].key
        if pct > self.save.get(key, 0):
            self.save[key] = pct
            write_save(self.save)

    def record_coins(self):
        """Coins only count when you finish the level in normal mode."""
        if self.practice or self.playtest or self.assisted or not self.player.coins:
            return
        key = self.levels[self.level_idx].key + "#coins"
        have = {tuple(c) for c in self.save.get(key, [])}
        new = have | set(self.player.coins)
        if new != have:
            self.save[key] = sorted(list(c) for c in new)
            write_save(self.save)
            self.say("Coins saved: %d / %d" % (len(new), len(self.level.coins)))

    def burst(self, x, y, color, n=10):
        for _ in range(n):
            ang = random.uniform(0, math.tau)
            spd = random.uniform(1.5, 5)
            self.particles.append([x, y, math.cos(ang) * spd, math.sin(ang) * spd,
                                   random.randint(12, 20), color])

    def kill(self):
        p = self.player
        if self.noclip or not p.alive:
            return
        p.alive = False
        self.dead_timer = 40
        self.stop_music()
        self.record_best(self.progress_pct())
        col = ACCENT[p.mode]
        for _ in range(36):
            ang = random.uniform(0, math.tau)
            spd = random.uniform(2, 9)
            self.particles.append([p.x, p.y, math.cos(ang) * spd,
                                   math.sin(ang) * spd - 2,
                                   random.randint(25, 45), col])

    def is_held(self):
        keys = pygame.key.get_pressed()
        raw = bool(keys[pygame.K_SPACE] or keys[pygame.K_UP] or keys[pygame.K_w]
                   or pygame.mouse.get_pressed()[0])
        if self.input_lock:
            if raw:
                return False
            self.input_lock = False
        return raw

    # ---- events -----------------------------------------------------------------
    def handle_event(self, e):
        if e.type == pygame.QUIT:
            self.quit()
        if e.type == pygame.DROPFILE:               # drag a level .json onto the window
            if self.state == "admin" and e.file.lower().endswith(".json"):
                self.admin_import(e.file)
            elif self.state == "editor" and e.file.lower().endswith(MUSIC_EXTS):
                if self.editor.attach_music(e.file) and self.editor.modal == "songs":
                    self.editor.rescan_songs()
            elif e.file.lower().endswith(MUSIC_EXTS):
                self.say("Open a level in the editor, then drop a song on it to attach it")
            else:
                self.import_level(e.file)
            return
        if e.type == pygame.KEYDOWN and self.is_fullscreen_hotkey(e):
            self.toggle_fullscreen()
            return
        if (e.type == pygame.MOUSEBUTTONDOWN and e.button == 1 and self.state != "play"
                and FS_BUTTON.collidepoint(e.pos)):
            self.toggle_fullscreen()
            return
        st = self.state
        if st == "home":
            self.home_event(e)
        elif st == "mainsetup":
            self.msetup_event(e)
        elif st in ("select", "mylevels", "settings", "admin"):
            self.list_event(e)
        elif st == "editor":
            self.editor.handle(e)
        elif st == "skins":
            self.skins_event(e)
        elif st == "account":
            self.account_event(e)
        else:
            self.play_event(e)

    def home_rect(self, i):
        r = pygame.Rect(0, 0, 340, 42)
        r.midtop = (W // 2, 188 + i * 48)
        return r

    def home_activate(self, i):
        if i == 0:
            self.go_select()
        elif i == 1:
            self.go_mylevels()
        elif i == 2:
            self.open_skins()
        elif i == 3:
            if self.open_folder(MUSIC_DIR):
                self.say("Put .mp3 / .ogg / .wav files in this folder, then pick them "
                         "in the editor with SONGS")
        elif i == 4:
            self.open_settings("home")
        else:
            self.quit()

    def account_buttons(self):
        """Top-left of the home screen: SIGN IN + SIGN UP, or SIGN OUT when signed in."""
        if self.account:
            b = {"signout": pygame.Rect(12, 8, 110, 32)}
            if self.is_admin():
                b["admin"] = pygame.Rect(128, 8, 140, 32)
            return b
        return {"signin": pygame.Rect(12, 8, 104, 32), "signup": pygame.Rect(122, 8, 104, 32)}

    def home_event(self, e):
        n = len(HOME_BUTTONS)
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for key, r in self.account_buttons().items():
                if r.collidepoint(e.pos):
                    if key == "signout":
                        self.sign_out()
                    elif key == "admin":
                        self.go_admin()
                    else:
                        self.open_account(key)
                    return
        if e.type == pygame.KEYDOWN:
            if e.key in (pygame.K_UP, pygame.K_w):
                self.sel = (self.sel - 1) % n
            elif e.key in (pygame.K_DOWN, pygame.K_s):
                self.sel = (self.sel + 1) % n
            elif e.key in (pygame.K_RETURN, pygame.K_KP_ENTER, pygame.K_SPACE):
                self.home_activate(self.sel)
            elif e.key == pygame.K_ESCAPE:
                self.quit()
        elif e.type == pygame.MOUSEMOTION:
            for i in range(n):
                if self.home_rect(i).collidepoint(e.pos):
                    self.sel = i
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for i in range(n):
                if self.home_rect(i).collidepoint(e.pos):
                    self.home_activate(i)

    def card_geom(self):
        """(top, card height, gap): the level-select screen has a tab bar above its cards."""
        return (134, 64, 4) if self.state == "select" else (CARD_TOP, CARD_H, CARD_GAP)

    def card_rect(self, slot):
        top, h, gap = self.card_geom()
        return pygame.Rect(CARD_X, top + slot * (h + gap), CARD_W, h)

    def card_at(self, pos):
        for slot in range(VISIBLE_CARDS):
            i = self.scroll + slot
            if i < len(self.items) and self.card_rect(slot).collidepoint(pos):
                return i
        return None

    def tab_rect(self, i):
        w = (W - 100) // len(TAB_NAMES)
        return pygame.Rect(50 + i * w, 98, w - 6, 28)

    def migrate_accounts(self):
        """Copy accounts made before accounts went online (on this computer, or in a folder
        picked by hand in an older version) into the shared folder, with their progress.
        A name that already exists online is left alone."""
        self.known_salts = {}
        sources = [(_read_local_accounts()["users"], None)]
        old = self.settings.get("accounts_folder")
        old_root = online_root(old) if old else None
        if old_root and os.path.abspath(old_root) != os.path.abspath(self.acc_root):
            sources.append((load_accounts(old_root)["users"], old_root))
        try:
            for sub in ("users", "progress"):
                os.makedirs(os.path.join(self.acc_root, sub), exist_ok=True)
        except OSError:
            return
        online = load_accounts(self.acc_root)
        for users, src_root in sources:
            for key, u in users.items():
                if not _user_ok(u):
                    continue
                self.known_salts.setdefault(key, set()).add(u["salt"])
                if key in online["users"]:
                    continue
                online["users"][key] = u
                if save_new_account(online, key, self.acc_root):
                    continue
                src = account_save_path(u, src_root)
                dst = account_save_path(u, self.acc_root)
                try:
                    if os.path.isfile(src) and not os.path.exists(dst):
                        with open(src, "rb") as fi, open(dst, "wb") as fo:
                            fo.write(fi.read())
                except OSError:
                    pass
        for key, u in online["users"].items():          # accounts already online
            self.known_salts.setdefault(key, set()).add(u["salt"])

    NEED_ONLINE = ("Accounts only work when Python Dash is in a shared online folder "
                   "(Google Drive, Dropbox or OneDrive) - move python_dash.py there")

    def list_event(self, e):
        n = len(self.items)
        if e.type == pygame.KEYDOWN:
            k = e.key
            if k in (pygame.K_DELETE, pygame.K_BACKSPACE):
                self.delete_selected()
            else:
                self.confirm_del = None
                sel_state = self.state == "select"
                if k == pygame.K_ESCAPE or (k == pygame.K_TAB and self.state == "settings"):
                    self.list_back()
                elif sel_state and k in (pygame.K_LEFT, pygame.K_a):
                    self.set_tab((self.tab - 1) % len(TAB_NAMES))
                elif sel_state and k in (pygame.K_RIGHT, pygame.K_d, pygame.K_TAB):
                    self.set_tab((self.tab + 1) % len(TAB_NAMES))
                elif sel_state and k == pygame.K_o:
                    self.open_folder(OTHER_DIR)
                elif self.state == "mylevels" and k == pygame.K_c:
                    self.copy_selected()
                elif self.state == "mylevels" and k == pygame.K_e:
                    self.export_selected()
                elif n == 0:
                    pass
                elif k in (pygame.K_UP, pygame.K_w):
                    self.sel = (self.sel - 1) % n
                elif k in (pygame.K_DOWN, pygame.K_s):
                    self.sel = (self.sel + 1) % n
                elif k in (pygame.K_RETURN, pygame.K_KP_ENTER, pygame.K_SPACE):
                    self.list_activate(self.sel)
                elif sel_state and self.tab == ONLINE_TAB and k == pygame.K_r:
                    self.fetch_online(force=True)
                    self.go_select(0, ONLINE_TAB)
                elif sel_state and self.tab == ONLINE_TAB:
                    pass
                elif sel_state and pygame.K_1 <= k <= pygame.K_9 and k - pygame.K_1 < n:
                    self.start_level(k - pygame.K_1)
            if self.state in ("select", "mylevels", "settings"):
                self.fix_scroll()
        elif e.type == pygame.MOUSEMOTION:
            i = self.card_at(e.pos)
            if i is not None:
                if i != self.sel:
                    self.confirm_del = None
                self.sel = i
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            if self.state == "select":
                for t in range(len(TAB_NAMES)):
                    if self.tab_rect(t).collidepoint(e.pos):
                        self.set_tab(t)
                        return
            if self.state == "mylevels" and self.my_page == "list":
                for slot in range(VISIBLE_CARDS):
                    i = self.scroll + slot
                    if i < n and self.items[i].get("type") == "custom":
                        btn = self.card_buttons(slot)
                        if btn["copy"].collidepoint(e.pos):
                            self.sel = i
                            self.copy_selected()
                            return
                        if btn["export"].collidepoint(e.pos):
                            self.sel = i
                            self.export_selected()
                            return
            i = self.card_at(e.pos)
            if i is not None:
                self.sel = i
                self.list_activate(i)
        elif e.type == pygame.MOUSEWHEEL:
            self.scroll = max(0, min(self.scroll - e.y, max(0, n - VISIBLE_CARDS)))

    # ---- pause menu ---------------------------------------------------------------------
    def pause_labels(self):
        return ["RESUME", "RETURN TO EDITOR" if self.playtest else "RETURN TO LEVEL SELECT"]

    def pause_rect(self, i):
        r = pygame.Rect(0, 0, 400, 56)
        r.midtop = (W // 2, 250 + i * 72)
        return r

    def pause(self):
        if self.finished or self.paused:
            return
        self.paused = True
        self.pause_sel = 0
        self.pause_music()

    def resume(self):
        self.paused = False
        self.input_lock = True          # the click / key that resumed isn't a jump
        if self.player.alive:
            self.resume_music()

    def pause_activate(self, i):
        if i == 0:
            self.resume()
        else:
            self.paused = False
            self.back_from_play()

    def pause_event(self, e):
        n = len(self.pause_labels())
        if e.type == pygame.KEYDOWN:
            if e.key in (pygame.K_ESCAPE, pygame.K_p):
                self.resume()
            elif e.key in (pygame.K_UP, pygame.K_w):
                self.pause_sel = (self.pause_sel - 1) % n
            elif e.key in (pygame.K_DOWN, pygame.K_s, pygame.K_TAB):
                self.pause_sel = (self.pause_sel + 1) % n
            elif e.key in (pygame.K_RETURN, pygame.K_KP_ENTER, pygame.K_SPACE):
                self.pause_activate(self.pause_sel)
        elif e.type == pygame.MOUSEMOTION:
            for i in range(n):
                if self.pause_rect(i).collidepoint(e.pos):
                    self.pause_sel = i
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for i in range(n):
                if self.pause_rect(i).collidepoint(e.pos):
                    self.pause_activate(i)
                    return

    def draw_pause(self):
        s = self.screen
        veil = pygame.Surface((W, H), pygame.SRCALPHA)
        veil.fill((70, 72, 82, 170))                   # translucent grey
        s.blit(veil, (0, 0))
        name = self.big.render(self.level.name, True, (255, 255, 255))
        if name.get_width() > W - 40:
            name = pygame.transform.smoothscale(
                name, (W - 40, int(name.get_height() * (W - 40) / name.get_width())))
        shadow = self.big.render(self.level.name, True, (20, 20, 30))
        if shadow.get_size() != name.get_size():
            shadow = pygame.transform.smoothscale(shadow, name.get_size())
        s.blit(shadow, (W // 2 - name.get_width() // 2 + 3, 63))
        s.blit(name, (W // 2 - name.get_width() // 2, 60))
        sub = self.mid.render("PAUSED", True, (225, 228, 240))
        s.blit(sub, (W // 2 - sub.get_width() // 2, 140))
        info = self.font.render("%d%%   attempt %d   %s" % (
            self.progress_pct(), self.attempt, "practice" if self.practice else "normal"),
            True, (205, 210, 225))
        s.blit(info, (W // 2 - info.get_width() // 2, 186))
        mx, my = pygame.mouse.get_pos()
        for i, label in enumerate(self.pause_labels()):
            r = self.pause_rect(i)
            on = i == self.pause_sel
            colr = (90, 230, 120) if i == 0 else (255, 210, 90)
            pygame.draw.rect(s, (52, 56, 72) if on else (36, 38, 50), r, border_radius=14)
            pygame.draw.rect(s, colr if on else (150, 152, 165), r, 4 if on else 2,
                             border_radius=14)
            t = self.mid.render(label, True, colr if on else (235, 236, 245))
            s.blit(t, (r.centerx - t.get_width() // 2, r.centery - t.get_height() // 2))
        h = self.small.render("ESC: resume    UP/DOWN + ENTER, or click", True, (200, 204, 220))
        s.blit(h, (W // 2 - h.get_width() // 2, H - 34))

    def draw_pause_button(self):
        r = PAUSE_BUTTON
        hov = r.collidepoint(pygame.mouse.get_pos())
        pygame.draw.rect(self.screen, (40, 46, 90) if hov else (16, 19, 42), r, border_radius=6)
        pygame.draw.rect(self.screen, (200, 205, 230), r, 2, border_radius=6)
        for dx in (-5, 3):
            pygame.draw.rect(self.screen, (230, 232, 245), (r.centerx + dx, r.y + 7, 4, r.h - 14))

    def play_event(self, e):
        if self.paused:
            self.pause_event(e)
            return
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            if PAUSE_BUTTON.collidepoint(e.pos) and not self.finished:
                self.pause()
                return
            self.player.buffer = BUFFER_FRAMES
        if e.type == pygame.KEYDOWN:
            if e.key == pygame.K_ESCAPE:
                if self.finished:
                    self.back_from_play()
                else:
                    self.pause()
            elif e.key in (pygame.K_SPACE, pygame.K_UP, pygame.K_w):
                self.player.buffer = BUFFER_FRAMES
            elif e.key in (pygame.K_RETURN, pygame.K_KP_ENTER) and self.finished:
                self.back_from_play()
            elif e.key == pygame.K_p:
                self.practice = not self.practice
            elif e.key == pygame.K_h:
                self.show_hitboxes = not self.show_hitboxes
                self.save_settings()
            elif e.key == pygame.K_TAB:
                self.open_settings("play")
            elif e.key == pygame.K_n:
                self.say("Noclip is in Settings (TAB)")
            elif e.key == pygame.K_r:
                self.attempt += 1
                self.assisted = False
                self.spawn(self.playtest_sec)
            elif pygame.K_1 <= e.key <= pygame.K_9:
                idx = e.key - pygame.K_1
                if not self.settings["warp"]:
                    self.say("Level warping is off - enable it in Settings (TAB)")
                elif idx < len(self.level.sections):
                    self.spawn(idx)
                    self.assisted = True        # warped: this attempt won't count

    # ---- update -------------------------------------------------------------------
    def update(self):
        self.menu_t += 1
        if (self.state == "select" and self.tab == ONLINE_TAB
                and self.items and self.items[0].get("type") == "online_msg"
                and self.online["status"] in ("ok", "error")
                and self.items[0].get("name") != self.online_items()[0].get("name")):
            self.go_select(self.sel, ONLINE_TAB)
        if self.toast_t > 0:
            self.toast_t -= 1
        if self.state == "admin":             # notice files dropped into the folder
            self.admin_scan += 1
            if self.admin_scan % 60 == 0 and len(load_custom_levels(MAIN_DIR)) != self.admin_files:
                self.go_admin(self.sel)
        if self.state == "editor":
            self.editor.update()
            return
        if self.state != "play" or self.paused:
            return
        for pt in self.particles:
            pt[0] += pt[2]
            pt[1] += pt[3]
            pt[3] += 0.4
            pt[4] -= 1
        self.particles = [pt for pt in self.particles if pt[4] > 0]
        if self.finished:
            return
        p = self.player
        if not p.alive:
            self.dead_timer -= 1
            if self.dead_timer <= 0:
                self.respawn()
            return
        if self.noclip:
            self.assisted = True            # any noclip use taints the attempt
        self.level.update(p.x)
        p.step(self.is_held(), self)
        if p.alive and p.x >= self.level.end_col * B:
            self.finished = True
            if not self.practice:
                locked = {(m, sk["id"]) for m in MODE_ORDER for sk in SKINS[m]
                          if not self.skin_unlocked(sk)}
                self.record_best(100)
                self.record_coins()
                self.check_top1()
                new = [(m, sk) for m in MODE_ORDER for sk in SKINS[m]
                       if (m, sk["id"]) in locked and self.skin_unlocked(sk)]
                self.new_unlocks = new
                if new:
                    self.say("Unlocked: " + ", ".join("%s (%s)" % (sk["name"], m)
                                                      for m, sk in new) + " - see SKINS")

    # ---- drawing: shared pieces -----------------------------------------------------
    def col(self, c):
        return tuple(int(v) for v in c)

    def draw_menu_bg(self):
        s = self.screen
        s.fill((10, 12, 30))
        off = (self.menu_t * 1.5) % 80
        for i in range(-1, W // 80 + 2):
            x = int(i * 80 - off)
            pygame.draw.line(s, (20, 24, 52), (x, 0), (x, H), 1)
        for y in range(0, H, 80):
            pygame.draw.line(s, (20, 24, 52), (0, y), (W, y), 1)

    def draw_mode_portal(self, mode, x, label_y):
        s = self.screen
        if -60 < x < W + 60:
            r = pygame.Rect(0, 0, 30, FLOOR - CEIL)
            r.midtop = (int(x), CEIL)
            pygame.draw.ellipse(s, ACCENT[mode], r, 5)
            pygame.draw.ellipse(s, BG[mode], r.inflate(-12, -24))
            txt = self.small.render("MINI WAVE" if mode == "miniwave" else mode.upper(),
                                    True, ACCENT[mode])
            s.blit(txt, (x - txt.get_width() // 2, label_y))

    # ---- drawing: home -----------------------------------------------------------------
    def draw_home(self):
        s = self.screen
        self.draw_menu_bg()
        gy = 482
        pygame.draw.rect(s, (8, 8, 20), (0, gy, W, H - gy))
        pygame.draw.line(s, ACCENT["cube"], (0, gy), (W, gy), 3)
        t = self.menu_t
        phase = t % 72
        for k in range(-1, 4):               # scrolling spikes the cube hops over
            sx = 200 + (38 - phase) * 5 + k * 360
            pts = [(sx - 20, gy), (sx, gy - 40), (sx + 20, gy)]
            pygame.draw.polygon(s, (6, 6, 14), pts)
            pygame.draw.polygon(s, (255, 255, 255), pts, 2)
        hop, rot = 0.0, 0.0
        if 20 <= phase < 56:
            u = (phase - 20) / 36.0
            hop, rot = 4 * u * (1 - u) * 90, -360 * u
        dummy = Player()
        dummy.mode = "cube"
        spr = pygame.transform.rotozoom(make_sprite(dummy, self.skin_for("cube")), rot, 1.0)
        s.blit(spr, spr.get_rect(center=(200, int(gy - 18 - hop))))

        title = "PYTHON DASH"
        shadow = self.huge.render(title, True, (6, 8, 20))
        main = self.huge.render(title, True, (255, 255, 255))
        x = W // 2 - main.get_width() // 2
        s.blit(shadow, (x + 5, 47))
        s.blit(main, (x, 42))
        sub = self.small.render("a Geometry Dash-style runner  -  play it, then build your own",
                                True, (150, 160, 210))
        s.blit(sub, (W // 2 - sub.get_width() // 2, 160))

        for i, (label, colr) in enumerate(HOME_BUTTONS):
            r = self.home_rect(i)
            sel = i == self.sel
            pygame.draw.rect(s, (34, 40, 80) if sel else (16, 19, 42), r, border_radius=14)
            pygame.draw.rect(s, colr, r, 4 if sel else 2, border_radius=14)
            txt = self.mid.render(label, True, colr if sel else (220, 225, 245))
            s.blit(txt, (r.centerx - txt.get_width() // 2, r.centery - txt.get_height() // 2))
        mx, my = pygame.mouse.get_pos()
        for key, r in self.account_buttons().items():
            label = {"signin": "SIGN IN", "signup": "SIGN UP", "signout": "SIGN OUT",
                     "admin": "MAIN LEVELS"}[key]
            colr = {"signup": (90, 230, 120), "admin": (255, 210, 90)}.get(key, (120, 230, 255))
            hov = r.collidepoint((mx, my))
            pygame.draw.rect(s, (34, 40, 80) if hov else (16, 19, 42), r, border_radius=8)
            pygame.draw.rect(s, colr, r, 3 if hov else 2, border_radius=8)
            tt = self.font.render(label, True, colr)
            s.blit(tt, (r.centerx - tt.get_width() // 2, r.centery - tt.get_height() // 2))
        who = ("Signed in as " + self.account) if self.account else (
            "Playing as Guest" if self.acc_root else "Guest - accounts need an online folder")
        wt = self.small.render(who, True, (190, 200, 235))
        last = max(r.right for r in self.account_buttons().values())
        s.blit(wt, (last + 12, 16))
        hint = self.small.render("UP/DOWN + ENTER, or click      F11: fullscreen", True,
                                 (110, 120, 170))
        s.blit(hint, (W // 2 - hint.get_width() // 2, H - 26))
        self.present()

    # ---- drawing: card lists (level select / my levels) ------------------------------
    def draw_tabs(self):
        s = self.screen
        for i, name in enumerate(TAB_NAMES):
            r = self.tab_rect(i)
            on = i == self.tab
            hover = r.collidepoint(pygame.mouse.get_pos())
            pygame.draw.rect(s, (40, 46, 90) if (on or hover) else (16, 19, 42), r,
                             border_radius=8)
            pygame.draw.rect(s, (255, 230, 90) if on else (60, 68, 120), r, 3 if on else 2,
                             border_radius=8)
            col = (255, 255, 255) if on else (160, 170, 210)
            label = name if i == ONLINE_TAB else "%s (%d)" % (name, len(self.tab_lists[i]))
            if self.small.size(label)[0] > r.w - 8:
                label = name
            f = self.small if self.small.size(label)[0] <= r.w - 8 else self.tiny
            t = f.render(label, True, col)
            s.blit(t, (r.centerx - t.get_width() // 2, r.centery - t.get_height() // 2))

    def draw_list(self, title, subtitle, hint):
        s = self.screen
        self.draw_menu_bg()
        t = self.big.render(title, True, (255, 255, 255))
        s.blit(t, (W // 2 - t.get_width() // 2, 16))
        sub = self.small.render(subtitle, True, (150, 160, 200))
        s.blit(sub, (W // 2 - sub.get_width() // 2, 78))
        if self.state == "select":
            self.draw_tabs()
        top, ch, gap = self.card_geom()

        for slot in range(VISIBLE_CARDS):
            i = self.scroll + slot
            if i >= len(self.items):
                break
            it = self.items[i]
            r = self.card_rect(slot)
            sel = i == self.sel
            dcol = it["col"]
            warn = self.confirm_del == i
            border = (255, 80, 80) if warn else (dcol if sel else (50, 56, 100))
            pygame.draw.rect(s, (28, 32, 66) if sel else (16, 19, 42), r, border_radius=10)
            pygame.draw.rect(s, border, r, 3 if (sel or warn) else 2, border_radius=10)
            num = self.mid.render(str(i + 1) if self.state == "select" else ">", True, dcol)
            s.blit(num, (r.x + 16, r.y + (ch - num.get_height()) // 2))
            s.blit(self.mid.render(it["name"], True, (255, 255, 255)), (r.x + 56, r.y + 4))
            sub = ("Press DELETE again to permanently delete this level (any other key cancels)"
                   if warn else it["sub"])
            coins = it.get("coins")
            room = (r.right - 210 - (coins[1] * 18 if coins and coins[1] else 0)) - (r.x + 66)
            if not warn and self.small.size(sub)[0] > room:       # keep clear of the coins
                while sub and self.small.size(sub + "...")[0] > room:
                    sub = sub[:-1]
                sub = sub.rstrip(" -") + "..."
            s.blit(self.small.render(sub, True, (255, 150, 150) if warn else (160, 170, 210)),
                   (r.x + 56, r.y + 30))
            if it.get("sub2"):                  # Ranks tab: a second info line
                s.blit(self.small.render(it["sub2"], True, (255, 215, 120)),
                       (r.x + 56, r.y + ch - 20))
            else:
                for j, mode in enumerate(it["modes"][:30]):
                    pygame.draw.rect(s, ACCENT[mode], (r.x + 56 + j * 20, r.y + ch - 14, 16, 9),
                                     border_radius=3)
            tag = self.font.render(it["tag"], True, dcol)
            s.blit(tag, (r.right - tag.get_width() - 16, r.y + 6))
            if it.get("type") == "custom":                   # copy / export buttons
                for label, rect in (("COPY", self.card_buttons(slot)["copy"]),
                                    ("EXPORT", self.card_buttons(slot)["export"])):
                    hov = rect.collidepoint(pygame.mouse.get_pos())
                    pygame.draw.rect(s, (40, 46, 90) if hov else (20, 24, 52), rect,
                                     border_radius=6)
                    pygame.draw.rect(s, (255, 230, 90) if hov else (90, 100, 160), rect, 2,
                                     border_radius=6)
                    bt = self.small.render(label, True, (255, 255, 255))
                    s.blit(bt, (rect.centerx - bt.get_width() // 2,
                                rect.centery - bt.get_height() // 2))
            coins = it.get("coins")
            if coins and coins[1]:
                got, tot = coins
                cx0 = r.right - 210 - tot * 18
                for k in range(tot):
                    cc = (cx0 + k * 18, r.y + ch - 27)
                    pygame.draw.circle(s, (255, 205, 50) if k < got else (60, 60, 80), cc, 7)
                    pygame.draw.circle(s, (255, 250, 200) if k < got else (110, 110, 140), cc,
                                       7, 1)
            best = it["best"]
            if best is not None:
                bar = pygame.Rect(r.right - 196, r.y + ch - 32, 180, 10)
                pygame.draw.rect(s, (8, 8, 20), bar, border_radius=5)
                if best:
                    fill = bar.copy()
                    fill.width = max(6, int(bar.width * best / 100))
                    pygame.draw.rect(s, (90, 230, 120) if best >= 100 else dcol, fill,
                                     border_radius=5)
                txt = "COMPLETE" if best >= 100 else "best %d%%" % best
                bt = self.small.render(txt, True, (200, 210, 240))
                s.blit(bt, (r.right - bt.get_width() - 16, r.y + ch - 20))

        if not self.items and self.empty_lines:          # an empty tab explains itself
            y = top + 70
            for n, line in enumerate(self.empty_lines):
                col = (255, 255, 255) if n == 0 else (160, 170, 210)
                f = self.mid if n == 0 else self.small
                tl = f.render(line, True, col)
                s.blit(tl, (W // 2 - tl.get_width() // 2, y))
                y += 44 if n == 0 else 26

        if self.scroll > 0:                              # more cards above / below
            pygame.draw.polygon(s, (200, 200, 230), [(14, top + 22), (38, top + 22),
                                                     (26, top + 8)])
        if self.scroll + VISIBLE_CARDS < len(self.items):
            yb = top + VISIBLE_CARDS * (ch + gap) - gap
            pygame.draw.polygon(s, (200, 200, 230), [(14, yb - 22), (38, yb - 22),
                                                     (26, yb - 8)])
        h = self.small.render(hint, True, (130, 140, 180))
        s.blit(h, (W // 2 - h.get_width() // 2, H - 26))
        self.present()

    # ---- drawing: gameplay -----------------------------------------------------------
    def draw(self):
        st = self.state
        if st == "home":
            self.draw_home()
            return
        if st == "admin":
            self.draw_list("MAIN LEVELS", "AugmentedMagic only: rename, re-rate or hide any main "
                           "level - and add new ones through the folder",
                           "ENTER / click: set up    ESC: back")
            return
        if st == "select":
            if self.tab == ONLINE_TAB:
                self.draw_list("SELECT A LEVEL", "online levels from github.com/" + REPO,
                               "LEFT/RIGHT: tab   UP/DOWN: choose   ENTER: download / play   "
                               "R: refresh   ESC: back")
            else:
                self.draw_list("SELECT A LEVEL", "built-in levels, levels you built, and levels "
                               "you downloaded",
                               "LEFT/RIGHT: tab   UP/DOWN: choose   ENTER: play   DELETE: remove "
                               "(yours / downloaded)   O: levels folder   ESC: back")
            return
        if st == "settings":
            self.draw_list("SETTINGS", "noclip or warping marks an attempt as assisted: it won't "
                           "count toward your best %",
                           "ENTER / click: change    UP/DOWN or mouse wheel: scroll    "
                           "ESC or TAB: back")
            return
        if st == "mylevels":
            if self.my_page == "list":
                self.draw_list("BUILD LEVELS", "create a new level or edit one of yours",
                               "ENTER: edit   C: copy   E: export to Desktop   DELETE: remove   ESC: back")
            else:
                self.draw_list("COPY A LEVEL", "pick a built-in or imported level to use as a "
                               "template",
                               "ENTER / click: copy into the editor    drag a .json here to "
                               "import it    ESC: back")
            return
        if st == "editor":
            self.editor.draw()
            return
        if st == "skins":
            self.draw_skins()
            return
        if st == "account":
            self.draw_account()
            return
        if st == "mainsetup":
            self.draw_msetup()
            return

        s = self.screen
        p = self.player
        cam = p.x - CAM_OFFSET

        tb, ta = BG[p.mode], ACCENT[p.mode]
        for i in range(3):
            self.bg[i] += (tb[i] - self.bg[i]) * 0.06
            self.accent[i] += (ta[i] - self.accent[i]) * 0.06
        bg = self.col(self.bg)
        acc = self.col(self.accent)
        s.fill(bg)

        if self.level.theme == "underwater":
            self.draw_underwater(cam)
        elif self.level.theme == "ocean":
            self.draw_ocean(cam)
        elif self.level.theme == "city":
            self.draw_city(cam)
        elif self.level.theme == "crystal":
            self.draw_crystal(cam)
        elif self.level.theme == "backyard":
            self.draw_backyard(cam)
        # parallax grid
        grid = tuple(min(255, v + 14) for v in bg)
        off = (cam * 0.4) % 80
        for i in range(-1, W // 80 + 2):
            if self.level.theme:
                break                          # themes draw their own scenery
            x = int(i * 80 - off)
            pygame.draw.line(s, grid, (x, 0), (x, FLOOR), 1)
        for y in range(0, FLOOR, 80):
            if self.level.theme:
                break
            pygame.draw.line(s, grid, (0, y), (W, y), 1)

        # ceiling (every mode has one)
        secs = self.level.sections
        lv = self.level
        pygame.draw.rect(s, (8, 8, 20), (0, 0, W, CEIL))
        pygame.draw.line(s, acc, (0, CEIL), (W, CEIL), 3)

        # background layer (decoration - drawn behind everything, never collides)
        c0 = int(cam // B) - 1
        c1 = c0 + W // B + 3
        for c in range(c0, c1):
            for o in lv.bg_cols.get(c, ()):
                if not o.hidden:
                    self.draw_obj(o, cam, acc, layer="bg")
        for o in lv.bg_dyn:
            if not o.hidden and -B < o.rect.x - cam < W + B:
                self.draw_obj(o, cam, acc, layer="bg")

        # ground
        pygame.draw.rect(s, (8, 8, 20), (0, FLOOR, W, H - FLOOR))
        pygame.draw.line(s, acc, (0, FLOOR), (W, FLOOR), 3)
        goff = cam % B
        for i in range(W // B + 2):
            x = int(i * B - goff)
            pygame.draw.line(s, (22, 22, 44), (x, FLOOR + 3), (x, H), 1)

        # level objects
        for c in range(c0, c1):
            for o in lv.cols.get(c, ()):
                if not o.hidden:
                    self.draw_obj(o, cam, acc)
        for o in lv.dyn:
            if not o.hidden and -B < o.rect.x - cam < W + B:
                self.draw_obj(o, cam, acc)
        for t in lv.texts:
            if not t.hidden and c0 - 8 <= t.col + t.ox / B <= c1 + 8:
                self.draw_text_obj(t, cam)

        # mode portals + labels
        for mode, col in secs[1:]:
            self.draw_mode_portal(mode, col * B - cam, FLOOR + 14)

        # finish line
        fx = self.level.end_col * B - cam
        if -40 < fx < W:
            for i in range(0, FLOOR, 20):
                for j in range(2):
                    colr = (255, 255, 255) if (i // 20 + j) % 2 == 0 else (30, 30, 30)
                    pygame.draw.rect(s, colr, (fx + j * 20, i, 20, 20))

        # wave trail
        if len(p.trail) >= 2:
            pts = [(tx - cam, ty) for tx, ty in p.trail]
            pygame.draw.lines(s, (20, 20, 40), False, pts, 8)
            pygame.draw.lines(s, self.skin_for("wave")["b"], False, pts, 4)

        # player
        if p.alive:
            spr = make_sprite(p, self.skin_for(p.mode))
            if p.mini:                                  # the mini wave is drawn smaller
                spr = pygame.transform.rotozoom(spr, 0, 0.7)
            if p.mode in FLIPPABLE and p.g == -1:
                spr = pygame.transform.flip(spr, False, True)
            ang = p.angle()
            if abs(ang) > 0.01:
                spr = pygame.transform.rotozoom(spr, ang, 1.0)
            s.blit(spr, spr.get_rect(center=(int(p.x - cam), int(p.y))))
            if self.show_hitboxes:
                r = p.rect().move(-int(cam), 0)
                pygame.draw.rect(s, (0, 255, 0), r, 1)

        # particles
        for x, y, _, _, life, colr in self.particles:
            sz = max(2, life // 6)
            pygame.draw.rect(s, colr, (x - cam - sz / 2, y - sz / 2, sz, sz))

        self.draw_light(p.x - cam, p.y)
        self.draw_hud(acc)
        if self.paused:
            self.draw_pause()
        elif not self.finished:
            self.draw_pause_button()
        self.present()

    # ---- skins -------------------------------------------------------------------------
    def level_beaten(self, name):
        for d in LEVELS:
            if d.name == name:
                return self.save.get(d.key, 0) >= 100
        return False

    def skin_unlocked(self, sk):
        if sk["unlock"] == "TOP1":
            return self.crown_earned()
        return sk["unlock"] is None or self.level_beaten(sk["unlock"])

    def crown_earned(self):
        """The Crown is kept for good once earned, even if the Top 1 demon changes."""
        u = self.save.get("__unlocks__")
        return isinstance(u, dict) and bool(u.get("crown"))

    def check_top1(self):
        """Beating whatever level is the Top 1 demon right now earns the Crown."""
        if TOP_DEMONS and self.level_beaten(TOP_DEMONS[0]) and not self.crown_earned():
            u = self.save.get("__unlocks__")
            u = dict(u) if isinstance(u, dict) else {}
            u["crown"] = True
            self.save["__unlocks__"] = u
            write_save(self.save)

    @staticmethod
    def unlock_text(sk):
        if sk["unlock"] == "TOP1":
            return "the Top 1 demon (now: %s)" % (TOP_DEMONS[0] if TOP_DEMONS else "none")
        return sk["unlock"]

    def skin_for(self, mode):
        sk = find_skin(mode, self.skins.get(mode, "classic"))
        return sk if self.skin_unlocked(sk) else SKINS[mode][0]

    def open_skins(self):
        self.state = "skins"
        self.skin_mode = 0
        self.skin_sel = [s["id"] for s in SKINS["cube"]].index(self.skin_for("cube")["id"])

    def skin_tab_rect(self, i):
        return pygame.Rect(24 + i * 114, 96, 108, 30)

    def skin_card_rect(self, i):
        return pygame.Rect(24 + i * 114, 150, 108, 132)

    def set_skin_mode(self, i):
        self.skin_mode = i % len(MODE_ORDER)
        m = MODE_ORDER[self.skin_mode]
        self.skin_sel = [s["id"] for s in SKINS[m]].index(self.skin_for(m)["id"])

    def equip_skin(self, i):
        m = MODE_ORDER[self.skin_mode]
        sk = SKINS[m][i]
        self.skin_sel = i
        if not self.skin_unlocked(sk):
            self.say("Locked - beat %s to unlock %s" % (self.unlock_text(sk), sk["name"]))
            return
        self.skins[m] = sk["id"]
        self.save["__skins__"] = dict(self.skins)
        write_save(self.save)

    def skins_event(self, e):
        m = MODE_ORDER[self.skin_mode]
        n = len(SKINS[m])
        if e.type == pygame.KEYDOWN:
            k = e.key
            if k == pygame.K_ESCAPE:
                self.go_home()
                self.sel = 2
            elif k in (pygame.K_LEFT, pygame.K_a):
                self.skin_sel = (self.skin_sel - 1) % n
            elif k in (pygame.K_RIGHT, pygame.K_d):
                self.skin_sel = (self.skin_sel + 1) % n
            elif k in (pygame.K_UP, pygame.K_w) or (k == pygame.K_TAB and e.mod & pygame.KMOD_SHIFT):
                self.set_skin_mode(self.skin_mode - 1)
            elif k in (pygame.K_DOWN, pygame.K_s, pygame.K_TAB):
                self.set_skin_mode(self.skin_mode + 1)
            elif k in (pygame.K_RETURN, pygame.K_KP_ENTER, pygame.K_SPACE):
                self.equip_skin(self.skin_sel)
            elif pygame.K_1 <= k <= pygame.K_8:
                self.set_skin_mode(k - pygame.K_1)
        elif e.type == pygame.MOUSEMOTION:
            for i in range(n):
                if self.skin_card_rect(i).collidepoint(e.pos):
                    self.skin_sel = i
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for i in range(len(MODE_ORDER)):
                if self.skin_tab_rect(i).collidepoint(e.pos):
                    self.set_skin_mode(i)
                    return
            for i in range(n):
                if self.skin_card_rect(i).collidepoint(e.pos):
                    self.equip_skin(i)
                    return

    def draw_skins(self):
        s = self.screen
        self.draw_menu_bg()
        t = self.big.render("SKINS", True, (255, 255, 255))
        s.blit(t, (W // 2 - t.get_width() // 2, 16))
        sub = self.small.render("a different look for every game mode - some are unlocked by "
                                "beating levels", True, (150, 160, 200))
        s.blit(sub, (W // 2 - sub.get_width() // 2, 72))
        mx, my = pygame.mouse.get_pos()
        for i, mode in enumerate(MODE_ORDER):            # one tab per game mode
            r = self.skin_tab_rect(i)
            on = i == self.skin_mode
            hov = r.collidepoint((mx, my))
            pygame.draw.rect(s, (40, 46, 90) if (on or hov) else (16, 19, 42), r,
                             border_radius=8)
            pygame.draw.rect(s, ACCENT[mode] if on else (60, 68, 120), r, 3 if on else 2,
                             border_radius=8)
            tt = self.font.render(mode.upper(), True, (255, 255, 255) if on else (160, 170, 210))
            s.blit(tt, (r.centerx - tt.get_width() // 2, r.centery - tt.get_height() // 2))
        m = MODE_ORDER[self.skin_mode]
        equipped = self.skin_for(m)["id"]
        dummy = Player()
        dummy.mode, dummy.anim, dummy.on_ground = m, self.menu_t, True
        for i, sk in enumerate(SKINS[m]):
            r = self.skin_card_rect(i)
            sel, eq = i == self.skin_sel, sk["id"] == equipped
            ok = self.skin_unlocked(sk)
            pygame.draw.rect(s, (34, 40, 80) if sel else (16, 19, 42), r, border_radius=10)
            pygame.draw.rect(s, (255, 230, 90) if eq else ACCENT[m] if sel else (50, 56, 100),
                             r, 3 if (sel or eq) else 2, border_radius=10)
            spr = make_sprite(dummy, sk)
            if not ok:
                spr.fill((40, 40, 60, 255), special_flags=pygame.BLEND_RGBA_MIN)
            s.blit(spr, spr.get_rect(center=(r.centerx, r.y + 46)))
            if not ok:                                      # padlock
                lx, ly = r.centerx, r.y + 48
                pygame.draw.arc(s, (230, 230, 240), (lx - 9, ly - 20, 18, 22), 0, math.pi, 3)
                pygame.draw.rect(s, (230, 230, 240), (lx - 12, ly - 8, 24, 18), border_radius=3)
                pygame.draw.circle(s, (40, 40, 60), (lx, ly), 3)
            nf = self.small if self.small.size(sk["name"])[0] <= r.w - 8 else self.tiny
            nm = nf.render(sk["name"], True, (255, 255, 255) if ok else (140, 140, 170))
            s.blit(nm, (r.centerx - nm.get_width() // 2, r.y + 86))
            tag = "EQUIPPED" if eq else ("" if ok else "LOCKED")
            if tag:
                tg = self.tiny.render(tag, True, (255, 230, 90) if eq else (255, 120, 120))
                s.blit(tg, (r.centerx - tg.get_width() // 2, r.y + 108))
        sk = SKINS[m][self.skin_sel]
        # big preview of the highlighted skin
        dummy.anim = self.menu_t
        big = pygame.transform.rotozoom(make_sprite(dummy, sk), 0, 2.4)
        if not self.skin_unlocked(sk):
            big.fill((40, 40, 60, 255), special_flags=pygame.BLEND_RGBA_MIN)
        s.blit(big, big.get_rect(center=(W // 2 - 150, 390)))
        lines = [sk["name"] + "  -  " + m.upper()]
        if self.skin_unlocked(sk):
            lines.append("Equipped" if sk["id"] == equipped else "Click or ENTER to equip")
        else:
            lines.append("Beat  %s  to unlock it" % self.unlock_text(sk))
        for j, ln in enumerate(lines):
            f = self.mid if j == 0 else self.font
            img = f.render(ln, True, (255, 255, 255) if j == 0 else
                           ((150, 230, 160) if self.skin_unlocked(sk) else (255, 150, 150)))
            s.blit(img, (W // 2 - 40, 350 + j * 44))
        h = self.small.render("LEFT/RIGHT: choose   ENTER: equip   UP/DOWN or TAB: game mode   "
                              "ESC: back", True, (130, 140, 180))
        s.blit(h, (W // 2 - h.get_width() // 2, H - 26))
        self.present()

    # ---- backyard theme: a sunny garden full of puppies ----------------------------------
    def make_yard(self):
        sky = pygame.Surface((W, FLOOR))
        for y in range(FLOOR):
            u = y / FLOOR
            pygame.draw.line(sky, (int(105 + 70 * u), int(170 + 50 * u), int(235 - 5 * u)),
                             (0, y), (W, y))
        pygame.draw.circle(sky, (255, 240, 170), (820, 96), 46)       # sun
        pygame.draw.circle(sky, (255, 250, 210), (820, 96), 34)
        rnd = random.Random(4)
        trees = pygame.Surface((1600, FLOOR), pygame.SRCALPHA)      # trees + a doghouse
        x = 40
        n = 0
        while x < 1500:
            if n % 4 == 2:                                          # doghouse
                base = FLOOR - 52
                pygame.draw.rect(trees, (170, 95, 60, 200), (x, base - 50, 80, 50))
                pygame.draw.polygon(trees, (190, 60, 50, 210),
                                    [(x - 10, base - 48), (x + 40, base - 88), (x + 90, base - 48)])
                pygame.draw.ellipse(trees, (60, 35, 30, 220), (x + 26, base - 34, 28, 34))
                x += 160
            else:                                                   # a leafy tree
                th = rnd.randint(120, 200)
                pygame.draw.rect(trees, (120, 85, 55, 190), (x + 30, FLOOR - th + 40, 16, th))
                for _ in range(6):
                    cx = x + 38 + rnd.randint(-40, 40)
                    cy = FLOOR - th + 30 + rnd.randint(-30, 30)
                    pygame.draw.circle(trees, (80 + rnd.randint(0, 40), 160 + rnd.randint(0, 40),
                                               80, 175), (cx, cy), rnd.randint(28, 42))
                x += rnd.randint(150, 230)
            n += 1
        fence = pygame.Surface((240, FLOOR), pygame.SRCALPHA)       # one tile of fence
        top = FLOOR - 70
        pygame.draw.rect(fence, (230, 205, 160, 220), (0, top + 18, 240, 10))
        pygame.draw.rect(fence, (230, 205, 160, 220), (0, top + 48, 240, 10))
        for px in range(6, 240, 30):
            pygame.draw.rect(fence, (240, 220, 180, 230), (px, top, 22, 70))
            pygame.draw.polygon(fence, (240, 220, 180, 230),
                                [(px, top), (px + 11, top - 10), (px + 22, top)])
            pygame.draw.line(fence, (200, 175, 135, 230), (px + 21, top), (px + 21, FLOOR), 2)
        return sky, trees, fence

    def draw_backyard(self, cam):
        s = self.screen
        if self.yard is None:
            self.yard = self.make_yard()
        sky, trees, fence = self.yard
        s.blit(sky, (0, 0))
        t = self.menu_t
        for i in range(5):                                          # drifting clouds
            cx = (i * 260 + t * 0.15 - cam * 0.05) % (W + 300) - 150
            cy = 70 + (i * 37) % 110
            for dx, dy, r in ((0, 0, 24), (24, -10, 28), (50, 0, 22), (26, 8, 22)):
                pygame.draw.circle(s, (250, 252, 255), (int(cx + dx), int(cy + dy)), r)
        ox = (cam * 0.2) % trees.get_width()
        s.blit(trees, (-ox, 0))
        s.blit(trees, (trees.get_width() - ox, 0))
        fx = (cam * 0.4) % fence.get_width()
        for k in range(-1, W // fence.get_width() + 2):
            s.blit(fence, (k * fence.get_width() - fx, 0))
        pygame.draw.rect(s, (110, 185, 90), (0, FLOOR - 14, W, 14))     # lawn
        # puppies chasing tennis balls (faded so they never look like you)
        pack = pygame.Surface((W, FLOOR), pygame.SRCALPHA)
        coats = [((205, 150, 85), None), ((90, 70, 55), None), ((240, 240, 235), (50, 40, 35)),
                 ((180, 180, 185), None), ((230, 190, 120), (150, 100, 60)), ((60, 55, 60), None)]
        span = W + 300
        for i, (coat, spots) in enumerate(coats):
            d = -1 if i % 3 == 1 else 1
            speed = 1.3 + (i % 3) * 0.5
            x = (i * 210 + d * t * speed - cam * 0.45) % span - 150
            hop = abs(math.sin(t * 0.12 + i)) * (22 if i % 2 else 8)
            y = FLOOR - 28 - hop - (i % 2) * 6
            draw_dog(pack, x, y, 1.0 + (i % 3) * 0.2, coat, t + i * 9, flip=d < 0, spots=spots)
            if i % 2 == 0:                                          # the ball it's chasing
                bx = x + d * (60 + 20 * math.sin(t * 0.05 + i))
                by = FLOOR - 24 - abs(math.sin(t * 0.09 + i * 2)) * 70
                pygame.draw.circle(pack, (210, 240, 70), (int(bx), int(by)), 6)
                pygame.draw.arc(pack, (250, 255, 255), (bx - 5, by - 5, 10, 10), 0.5, 2.6, 1)
        pack.set_alpha(185)
        s.blit(pack, (0, 0))

    # ---- crystal theme: a glowing cavern ---------------------------------------------
    @staticmethod
    def make_crystals(width, seed, size, colors, alpha):
        """A wide strip of crystal clusters growing up from the floor and down from the
        ceiling.  Returns the strip and where its brightest crystals are (for glows)."""
        rnd = random.Random(seed)
        strip = pygame.Surface((width, FLOOR), pygame.SRCALPHA)
        glows = []
        x = rnd.randint(0, 60)
        while x < width - 80:
            col = colors[rnd.randrange(len(colors))]
            from_top = rnd.random() < 0.45
            for _ in range(rnd.randint(2, 4)):          # a cluster of a few crystals
                w = rnd.randint(10, 22) * size
                h = rnd.randint(40, 140) * size
                cx = x + rnd.randint(-18, 18) * size
                lean = rnd.uniform(-0.35, 0.35) * h
                base = CEIL if from_top else FLOOR
                d = 1 if from_top else -1
                pts = [(cx - w / 2, base), (cx - w / 2 + lean * 0.1, base + d * h * 0.75),
                       (cx + lean * 0.3, base + d * h), (cx + w / 2 + lean * 0.1,
                                                         base + d * h * 0.75),
                       (cx + w / 2, base)]
                pygame.draw.polygon(strip, col + (alpha,), pts)
                light = tuple(min(255, v + 70) for v in col) + (alpha,)
                pygame.draw.polygon(strip, light, [pts[0], pts[1], pts[2],
                                                   ((pts[0][0] + pts[4][0]) / 2, base)])
                pygame.draw.line(strip, (255, 255, 255, alpha), pts[2],
                                 ((pts[0][0] + pts[4][0]) / 2, base), 1)
                if rnd.random() < 0.4:
                    glows.append((cx + lean * 0.3, base + d * h * 0.8, col))
            x += rnd.randint(90, 200)
        return strip, glows

    def draw_crystal(self, cam):
        s = self.screen
        if self.cave is None:
            bg = pygame.Surface((W, FLOOR))
            for y in range(FLOOR):
                u = abs(y / FLOOR - 0.5) * 2          # darker towards floor and ceiling
                c = (int(26 - 14 * u), int(14 - 8 * u), int(52 - 28 * u))
                pygame.draw.line(bg, c, (0, y), (W, y))
            # kept dim and see-through so scenery never looks like real spikes
            far, _ = self.make_crystals(1500, 5, 0.8, [(60, 45, 120), (35, 75, 110),
                                                        (90, 45, 100)], 110)
            near, glows = self.make_crystals(1700, 9, 1.2, [(105, 70, 170), (65, 150, 160),
                                                             (150, 70, 140)], 130)
            self.cave = (bg, far, near, glows)
        bg, far, near, glows = self.cave
        s.blit(bg, (0, 0))
        t = self.menu_t
        ox = (cam * 0.15) % far.get_width()
        s.blit(far, (-ox, 0))
        s.blit(far, (far.get_width() - ox, 0))
        nx = (cam * 0.35) % near.get_width()
        glow = pygame.Surface((W, FLOOR), pygame.SRCALPHA)        # pulsing crystal light
        for i, (gx, gy, col) in enumerate(glows):
            for off in (0, near.get_width()):
                px = gx - nx + off
                if -60 < px < W + 60:
                    r = 34 + 8 * math.sin(t * 0.05 + i)
                    pygame.draw.circle(glow, col + (40,), (int(px), int(gy)), int(r))
                    pygame.draw.circle(glow, col + (40,), (int(px), int(gy)), int(r * 0.55))
        s.blit(glow, (0, 0))
        s.blit(near, (-nx, 0))
        s.blit(near, (near.get_width() - nx, 0))
        for i in range(30):                                       # drifting sparkles
            x = (i * 97 + t * (0.3 + (i % 4) * 0.15) - cam * 0.45) % W
            y = CEIL + 20 + (i * 53 + math.sin(t * 0.02 + i) * 30) % (FLOOR - CEIL - 40)
            if (t // 7 + i) % 5:
                c = ((200, 170, 255), (160, 255, 245), (255, 180, 240))[i % 3]
                pygame.draw.circle(s, c, (int(x), int(y)), 1 + (i % 3 == 0))

    # ---- city theme: a night skyline with helicopters ---------------------------------
    @staticmethod
    def make_skyline(width, seed, base_h, var_h, body, lit, win_chance):
        """One wide strip of buildings (tiles seamlessly) with some windows lit."""
        rnd = random.Random(seed)
        strip = pygame.Surface((width, FLOOR), pygame.SRCALPHA)
        antennas = []
        x = 0
        while x < width:
            bw = rnd.choice((40, 56, 64, 72, 88))
            bw = min(bw, width - x)
            if bw < 24:
                break
            h = base_h + rnd.randint(0, var_h)
            top = FLOOR - h
            pygame.draw.rect(strip, body, (x, top, bw - 4, h))
            if rnd.random() < 0.3:                   # a stepped roof
                pygame.draw.rect(strip, body, (x + bw // 4, top - 18, bw // 2 - 4, 18))
            for wy in range(top + 8, FLOOR - 6, 14):
                for wx in range(x + 6, x + bw - 10, 10):
                    if rnd.random() < win_chance:
                        pygame.draw.rect(strip, lit[rnd.randrange(len(lit))], (wx, wy, 4, 6))
            if rnd.random() < 0.35:                  # rooftop antenna
                ax = x + bw // 2
                pygame.draw.line(strip, body, (ax, top), (ax, top - 30), 2)
                antennas.append((ax, top - 30))
            x += bw
        return strip, antennas

    def draw_heli(self, s, x, y, d, t, size=1.0, beam=False):
        """A background helicopter facing direction d (+1 right, -1 left)."""
        body = (30, 32, 55)

        def P(px, py):
            return int(x + px * d * size), int(y + py * size)
        if beam:                                         # searchlight sweeping below
            sw = math.sin(t * 0.02) * 40
            cone = pygame.Surface((W, FLOOR), pygame.SRCALPHA)
            pygame.draw.polygon(cone, (255, 250, 200, 34),
                                [P(6, 8), P(-30 + sw / size, 260), P(50 + sw / size, 260)])
            s.blit(cone, (0, 0))
        pygame.draw.line(s, body, P(-12, 0), P(-36, -3), max(2, int(4 * size)))   # tail
        tr = int(6 * abs(math.cos(t * 1.2)) * size) + 1
        pygame.draw.line(s, body, (P(-36, -3)[0], P(-36, -3)[1] - tr),
                         (P(-36, -3)[0], P(-36, -3)[1] + tr), 2)
        pygame.draw.ellipse(s, body, (min(P(-14, -9)[0], P(16, 9)[0]), P(-14, -9)[1],
                                      int(30 * size), int(18 * size)))
        pygame.draw.ellipse(s, (255, 220, 120), (min(P(4, -6)[0], P(13, 1)[0]), P(4, -6)[1],
                                                 int(9 * size), int(7 * size)))   # cockpit
        pygame.draw.line(s, body, P(-10, 11), P(12, 11), 2)                  # skid
        pygame.draw.line(s, body, P(0, -9), P(0, -13), 2)
        bw = int(30 * abs(math.cos(t * 0.9)) * size) + 3
        pygame.draw.line(s, (90, 95, 120), (P(0, -13)[0] - bw, P(0, -13)[1]),
                         (P(0, -13)[0] + bw, P(0, -13)[1]), 2)
        if (t // 20) % 2:                                                    # nav lights
            pygame.draw.circle(s, (255, 60, 60), P(-36, -3), 2)
            pygame.draw.circle(s, (80, 255, 120), P(14, 2), 2)

    def draw_city(self, cam):
        s = self.screen
        if self.city is None:
            sky = pygame.Surface((W, FLOOR))
            for y in range(FLOOR):
                u = y / FLOOR                       # deep night above, warm glow below
                c = (int(16 + 70 * u ** 2), int(14 + 26 * u ** 2), int(48 + 40 * u))
                pygame.draw.line(sky, c, (0, y), (W, y))
            rnd = random.Random(7)
            for _ in range(70):                     # stars
                sx, sy = rnd.randrange(W), rnd.randrange(FLOOR // 2)
                sky.set_at((sx, sy), (200, 200, 230))
            pygame.draw.circle(sky, (245, 240, 215), (760, 92), 26)        # moon
            far, _ = self.make_skyline(1600, 3, 110, 150, (34, 30, 70),
                                       [(120, 110, 70), (90, 100, 140)], 0.18)
            near, ants = self.make_skyline(1800, 11, 60, 190, (16, 14, 36),
                                           [(255, 215, 110), (255, 240, 170), (140, 200, 255)],
                                           0.28)
            self.city = (sky, far, near, ants)
        sky, far, near, ants = self.city
        s.blit(sky, (0, 0))
        t = self.menu_t
        ox = (cam * 0.12) % far.get_width()
        s.blit(far, (-ox, 0))
        s.blit(far, (far.get_width() - ox, 0))
        # helicopters weave between the two layers of buildings
        span = W + 400
        for i in range(5):
            d = 1 if i % 2 == 0 else -1
            speed = 1.4 + (i % 3) * 0.5
            x = (i * 260 + d * t * speed - cam * 0.2) % span - 200
            y = 70 + (i * 67) % 200 + math.sin(t * 0.03 + i * 2) * 10
            self.draw_heli(s, x, y, d, t + i * 11, 0.8 + (i % 3) * 0.25, beam=(i == 1))
        nx = (cam * 0.3) % near.get_width()
        s.blit(near, (-nx, 0))
        s.blit(near, (near.get_width() - nx, 0))
        if (t // 30) % 2 == 0:                      # blinking antenna lights
            for ax, ay in ants:
                for off in (0, near.get_width()):
                    px = ax - nx + off
                    if -5 < px < W + 5:
                        pygame.draw.circle(s, (255, 70, 70), (int(px), ay), 3)

    # ---- ocean theme: open blue water with dolphins ----------------------------------
    def draw_ocean(self, cam):
        s = self.screen
        if self.sea is None:                        # bright near the surface, deep below
            self.sea = pygame.Surface((W, FLOOR))
            for y in range(FLOOR):
                u = y / FLOOR
                c = (int(40 - 25 * u), int(150 - 90 * u), int(220 - 100 * u))
                pygame.draw.line(self.sea, c, (0, y), (W, y))
        s.blit(self.sea, (0, 0))
        t = self.menu_t
        # the surface shimmering just under the ceiling
        for i in range(-1, W // 60 + 2):
            x = i * 60 - (cam * 0.3 + t * 0.6) % 60
            y = CEIL + 8 + math.sin(t * 0.05 + i) * 3
            pygame.draw.arc(s, (150, 220, 255), (x, y, 60, 14), 0.3, 2.8, 2)
        rays = pygame.Surface((W, FLOOR), pygame.SRCALPHA)
        for i in range(6):
            x = (i * 190 - cam * 0.12) % (W + 260) - 130 + math.sin(t * 0.012 + i) * 25
            pygame.draw.polygon(rays, (210, 245, 255, 26),
                                [(x, 0), (x + 50, 0), (x + 190, FLOOR), (x + 110, FLOOR)])
        s.blit(rays, (0, 0))
        # sandy dunes on the sea floor
        pts = [(0, FLOOR)]
        for x in range(0, W + 41, 40):
            wx = x + cam * 0.4
            pts.append((x, FLOOR - 26 - 14 * math.sin(wx * 0.011) - 6 * math.sin(wx * 0.031)))
        pts.append((W, FLOOR))
        pygame.draw.polygon(s, (60, 110, 140), pts)
        # dolphins: a pod swimming past, some leaping in arcs (faded so they never look
        # like your own dolphin)
        haze = pygame.Surface((W, FLOOR), pygame.SRCALPHA)
        span = W + 360
        for i in range(7):
            d = -1 if i % 3 == 2 else 1
            speed = 1.1 + (i % 3) * 0.35
            x = (i * 173 + d * t * speed - cam * 0.3) % span - 180
            ph = t * 0.035 + i * 1.3
            y = 120 + (i * 53) % 230 + math.sin(ph) * 26
            ang = math.degrees(math.atan2(-math.cos(ph) * 26 * 0.035, speed)) * d
            size = 0.75 + (i % 3) * 0.25
            spr = pygame.Surface((int(90 * size) + 20, int(60 * size) + 20), pygame.SRCALPHA)
            draw_dolphin(spr, spr.get_width() // 2, spr.get_height() // 2, size,
                         (130, 165, 200), (210, 225, 240), t + i * 17, flip=d < 0)
            spr = pygame.transform.rotate(spr, ang)
            haze.blit(spr, spr.get_rect(center=(int(x), int(y))))
        haze.set_alpha(125)
        s.blit(haze, (0, 0))
        for i in range(18):                         # a few bubbles
            x = (i * 107 - cam * 0.5) % W + math.sin((t + i * 40) * 0.05) * 5
            y = FLOOR - ((t * (0.7 + (i % 3) * 0.3) + i * 71) % (FLOOR + 40))
            pygame.draw.circle(s, (210, 245, 255), (int(x), int(y)), 2 + i % 3, 1)

    # ---- underwater theme ------------------------------------------------------------------
    def draw_underwater(self, cam):
        s = self.screen
        if self.ocean is None:                      # vertical gradient, made once
            self.ocean = pygame.Surface((W, FLOOR))
            for y in range(FLOOR):
                u = y / FLOOR
                c = (int(20 + 10 * (1 - u)), int(120 - 70 * u), int(160 - 70 * u))
                pygame.draw.line(self.ocean, c, (0, y), (W, y))
        s.blit(self.ocean, (0, 0))
        t = self.menu_t
        rays = pygame.Surface((W, FLOOR), pygame.SRCALPHA)      # sun rays from above
        for i in range(5):
            x = (i * 230 - cam * 0.1) % (W + 300) - 150 + math.sin(t * 0.01 + i) * 30
            pygame.draw.polygon(rays, (180, 240, 255, 22),
                                [(x, 0), (x + 70, 0), (x + 220, FLOOR), (x + 120, FLOOR)])
        s.blit(rays, (0, 0))
        # far rocks / kelp silhouettes
        for i in range(-1, W // 120 + 3):
            base = i * 120 - (cam * 0.35) % 120
            h = 60 + (int(cam * 0.35 // 120) + i) * 37 % 70
            for j in range(3):
                sw = math.sin(t * 0.03 + i + j) * 8
                x0 = base + j * 22
                pts = [(x0, FLOOR), (x0 + sw * 0.5, FLOOR - h * 0.5), (x0 + sw, FLOOR - h)]
                pygame.draw.lines(s, (20, 110, 90), False, pts, 5)
        # axolotls swimming about in the distance (faded, so they never look like you)
        span = W + 300
        haze = pygame.Surface((W, FLOOR), pygame.SRCALPHA)
        for i in range(6):
            speed = 0.5 + (i % 3) * 0.25
            d = -1 if i % 2 else 1
            x = (i * 197 + d * t * speed - cam * 0.25) % span - 150
            y = 90 + (i * 61) % 260 + math.sin(t * 0.03 + i) * 12
            colr = [(255, 150, 200), (255, 190, 220), (250, 220, 240), (190, 150, 255),
                    (255, 170, 160), (255, 150, 200)][i]
            draw_axolotl(haze, x, y, 0.8 + (i % 3) * 0.2, colr, (255, 90, 150), t + i * 20,
                         flip=i % 2 == 1)
        haze.fill((170, 190, 230, 255), special_flags=pygame.BLEND_RGBA_MIN)
        haze.set_alpha(120)
        s.blit(haze, (0, 0))
        # bubbles
        for i in range(26):
            x = (i * 83 - cam * 0.5) % W
            y = FLOOR - ((t * (0.6 + (i % 4) * 0.3) + i * 57) % (FLOOR + 40))
            x += math.sin((t + i * 30) * 0.05) * 6
            r = 2 + i % 4
            pygame.draw.circle(s, (200, 245, 255), (int(x), int(y)), r, 1)

    def draw_text_obj(self, t, cam):
        s = self.screen
        cx = t.col * B + t.ox - cam + B / 2
        cy = FLOOR - (t.row + 1) * B + t.oy + B / 2
        img = self.font.render(t.text, True, (255, 255, 255))
        sh = self.font.render(t.text, True, (0, 0, 0))
        x, y = int(cx - img.get_width() / 2), int(cy - img.get_height() / 2)
        s.blit(sh, (x + 2, y + 2))
        s.blit(img, (x, y))

    def draw_light(self, px, py):
        """Darkness from light triggers, with a circle of light around the player."""
        light = self.level.light
        if not light.active():
            return
        dark = light.darkness()
        surf = pygame.Surface((W, H), pygame.SRCALPHA)
        if light.radius is not None:
            surf.fill((0, 0, 0, 250))
            rad = light.radius
            hole_a = int(220 * dark)        # lights off inside the circle too
            for i in range(6, -1, -1):      # soft edge
                a = int(hole_a + (250 - hole_a) * i / 7)
                pygame.draw.circle(surf, (0, 0, 0, a), (int(px), int(py)), int(rad + i * 5))
            pygame.draw.circle(surf, (0, 0, 0, hole_a), (int(px), int(py)), int(rad))
        else:
            surf.fill((0, 0, 0, int(225 * dark)))
            if dark > 0.5:                  # a faint glow so you can still see yourself
                for i, a in ((70, 160), (50, 110), (34, 60)):
                    pygame.draw.circle(surf, (0, 0, 0, int(a * dark)), (int(px), int(py)), i)
        self.screen.blit(surf, (0, 0))

    def draw_obj_at(self, kind, x, y, rgb):
        """Draw one object at screen (x, y) in a given colour (colour editor preview)."""
        old = self.palette
        self.palette = [rgb] * len(DEFAULT_PALETTE)
        o = Obj(kind, 0, 0, color=1)
        o.oy = y - (FLOOR - B)                         # row 0 normally sits on the floor
        try:
            self.draw_obj(o, -x, (255, 255, 255))
        finally:
            self.palette = old

    def draw_obj(self, o, cam, acc, layer="main"):
        s = self.screen
        sx = o.col * B + o.ox - cam
        sy = int(FLOOR - (o.row + 1) * B + o.oy)
        k = o.kind
        ghost = o.flip and k in ("pad", "dpad", "orb", "dorb")      # an invisible object
        if ghost and self.state != "editor":
            k = None          # never drawn while playing (hitboxes mode still shows it)
        if layer == "bg":     # background layer: soft, outline-free decoration
            fill = bg_fill(acc, o.color, self.palette)
            if k == "block":
                pygame.draw.rect(s, fill, (int(sx), sy, B, B))
            elif k in SPIKES:
                pygame.draw.polygon(s, fill, spike_points(k, sx, sy, o.flip))
            elif k in RAMPS:
                w, h = ramp_size(k)
                pygame.draw.polygon(s, fill, ramp_points(k, int(sx), sy - (h - 1) * B,
                                                         w * B, h * B))
            return
        if o.color and k in COLORABLE:                 # an object with its own colour
            line = slot_color(self.palette, o.color, acc)
            fillc = tuple(int(v * 0.18) + 8 for v in line)
        else:
            line, fillc = acc, (12, 14, 32)
        if k == "block":
            r = pygame.Rect(int(sx), sy, B, B)
            pygame.draw.rect(s, fillc, r)
            pygame.draw.rect(s, line, r, 2)
            pygame.draw.rect(s, tuple(v // 2 for v in line), r.inflate(-16, -16), 1)
        elif k in RAMPS:
            w, h = ramp_size(k)
            pts = ramp_points(k, int(sx), sy - (h - 1) * B, w * B, h * B)
            pygame.draw.polygon(s, fillc, pts)
            pygame.draw.polygon(s, line, pts, 2)
        elif k == "coin":
            got = self.state == "play" and (o.col, o.row) in self.player.coins
            if not got:
                cx, cy = int(sx + B / 2), sy + B // 2
                wob = abs(math.cos(pygame.time.get_ticks() * 0.004))
                wd = max(4, int(26 * wob))
                pygame.draw.ellipse(s, (255, 205, 50), (cx - wd // 2, cy - 13, wd, 26))
                pygame.draw.ellipse(s, (255, 250, 200), (cx - wd // 2, cy - 13, wd, 26), 2)
                if wd > 10:
                    pygame.draw.ellipse(s, (200, 140, 20),
                                        (cx - wd // 4, cy - 7, max(2, wd // 2), 14), 2)
        elif k in SPIKES:
            pts = spike_points(k, sx, sy, o.flip)
            colored = o.color and line is not acc
            pygame.draw.polygon(s, fillc if colored else (6, 6, 14), pts)
            pygame.draw.polygon(s, line if colored else (255, 255, 255), pts, 2)
        elif k == "pad":
            pygame.draw.ellipse(s, (255, 230, 40), (sx + 3, sy + B - 12, B - 6, 14))
            pygame.draw.ellipse(s, (255, 255, 255), (sx + 3, sy + B - 12, B - 6, 14), 2)
        elif k == "dpad":
            pygame.draw.ellipse(s, (80, 140, 255), (sx + 3, sy - 2, B - 6, 14))
            pygame.draw.ellipse(s, (255, 255, 255), (sx + 3, sy - 2, B - 6, 14), 2)
        elif k in ("orb", "dorb"):
            cx, cy = int(sx + B / 2), sy + B // 2
            used = (o.col, o.row) in self.player.used_orbs and self.state == "play"
            pulse = 17 + int(2 * math.sin(pygame.time.get_ticks() * 0.01))
            if k == "orb":
                col = (120, 120, 60) if used else (255, 230, 40)
            else:
                col = (50, 70, 120) if used else (80, 140, 255)
            pygame.draw.circle(s, col, (cx, cy), 11)
            pygame.draw.circle(s, (255, 255, 255) if not used else (140, 140, 140),
                               (cx, cy), pulse, 2)
            d = 1 if k == "dorb" else -1          # arrow shows the bounce direction
            pygame.draw.polygon(s, (255, 255, 255) if not used else (140, 140, 140),
                                [(cx - 5, cy - 3 * d), (cx + 5, cy - 3 * d), (cx, cy + 4 * d)])
        elif k == "speed":
            colr = SPEED_COLOR.get(o.val, (255, 255, 255))
            r = pygame.Rect(0, 0, 26, FLOOR - CEIL)
            r.midtop = (int(sx + B / 2), CEIL)
            pygame.draw.ellipse(s, colr, r, 4)
            cx, cy = r.centerx, (FLOOR + CEIL) // 2
            n = max(1, SPEED_VALUES.index(o.val) if o.val in SPEED_VALUES else 1)
            step = max(5, min(10, 20 // n))        # more chevrons = faster
            for i in range(n):
                x0 = cx - 3 - (n - 1) * step // 2 + i * step
                pygame.draw.lines(s, colr, False, [(x0, cy - 8), (x0 + 5, cy), (x0, cy + 8)], 2)
            lab = self.small.render("%gx" % o.val, True, colr)
            lr = pygame.Rect(0, 0, lab.get_width() + 8, lab.get_height() + 4)
            lr.midtop = (cx, CEIL + 6)
            pygame.draw.rect(s, (8, 8, 20), lr, border_radius=4)
            s.blit(lab, (lr.x + 4, lr.y + 2))
        elif k == "grav":
            colr = (255, 225, 30) if o.up else (60, 170, 255)
            r = pygame.Rect(0, 0, 26, FLOOR - CEIL)
            r.midtop = (int(sx + B / 2), CEIL)
            pygame.draw.ellipse(s, colr, r, 4)
            cy = (FLOOR + CEIL) // 2
            d = -1 if o.up else 1
            cx = r.centerx
            pygame.draw.polygon(s, colr, [(cx - 8, cy - 8 * d), (cx + 8, cy - 8 * d),
                                          (cx, cy + 10 * d)])
        if ghost and self.state == "editor":
            draw_dashed_rect(s, pygame.Rect(int(sx), sy, B, B), (255, 255, 255), 5, 4, 1)
        if self.show_hitboxes and k != "block":
            pygame.draw.rect(s, (255, 60, 60), o.rect.move(-int(cam), 0), 1)

    def draw_hud(self, acc):
        s = self.screen
        p = self.player
        total = self.level.end_col * B
        pct = self.progress_pct()

        # progress bar with section ticks
        pygame.draw.rect(s, (0, 0, 0), (0, 0, W, 8))
        pygame.draw.rect(s, acc, (0, 0, int(W * min(1.0, p.x / total)), 8))
        for mode, col in self.level.sections[1:]:
            pygame.draw.line(s, (255, 255, 255), (int(W * col * B / total), 0),
                             (int(W * col * B / total), 8), 2)

        info = "%s - %s   attempt %d   %d%%" % (self.level.name,
                                                 "MINI WAVE" if p.mini else p.mode.upper(),
                                                 self.attempt, pct)
        it = self.font.render(info, True, (255, 255, 255))
        s.blit(it, (12, 14))
        if self.level.coins:
            x = 12 + it.get_width() + 16
            for o in self.level.coins:
                got = (o.col, o.row) in p.coins
                pygame.draw.circle(s, (255, 205, 50) if got else (50, 50, 70), (x, 23), 7)
                pygame.draw.circle(s, (255, 250, 200) if got else (110, 110, 140), (x, 23), 7, 1)
                x += 18
        flags = ["PRACTICE" if self.practice else "NORMAL"]
        if self.playtest:
            flags.insert(0, "PLAYTEST")
        if self.noclip:
            flags.append("NOCLIP")
        if abs(p.speed_mult - 1.0) > 1e-6:
            flags.append("%gx" % p.speed_mult)
        t = self.font.render("  ".join(flags), True, acc)
        s.blit(t, (W - t.get_width() - 12, 14))
        counts = not self.practice and not self.playtest
        if self.assisted and counts:
            t3 = self.small.render("ASSISTED - this attempt won't count", True, (255, 120, 120))
            s.blit(t3, (W - t3.get_width() - 12, 38))
        help_txt = ("SPACE/click: action   P: practice   H: hitboxes   R: restart   "
                    + ("1-9: warp   " if self.settings["warp"] else "")
                    + "TAB: settings   ESC: pause")
        if not self.paused:
            h = self.small.render(help_txt, True, (150, 150, 180))
            s.blit(h, (W // 2 - h.get_width() // 2, H - 30))

        if self.finished:
            veil = pygame.Surface((W, H), pygame.SRCALPHA)
            veil.fill((0, 0, 0, 130))
            s.blit(veil, (0, 0))
            head = "LEVEL COMPLETE!" if not self.practice else "PRACTICE COMPLETE"
            t = self.big.render(head, True, (255, 255, 255))
            s.blit(t, (W // 2 - t.get_width() // 2, H // 2 - 60))
            msg = "Attempts: %d      R: replay     ENTER: %s" % (
                self.attempt, "back to editor" if self.playtest else "level select")
            if self.practice and not self.playtest:
                msg += "     (P for normal mode)"
            t2 = self.font.render(msg, True, acc)
            s.blit(t2, (W // 2 - t2.get_width() // 2, H // 2 + 20))
            if getattr(self, "new_unlocks", None) and not self.practice:
                m, sk = self.new_unlocks[0]
                spr = make_sprite(type("P", (), {"mode": m, "anim": self.menu_t,
                                                 "on_ground": True})(), sk)
                spr = pygame.transform.rotozoom(spr, 0, 1.6)
                s.blit(spr, spr.get_rect(center=(W // 2, H // 2 + 112)))
                t5 = self.font.render("NEW SKIN UNLOCKED: %s %s - equip it in SKINS" % (
                    sk["name"], m.upper()), True, (255, 150, 220))
                s.blit(t5, (W // 2 - t5.get_width() // 2, H // 2 + 156))
            if self.assisted and counts:
                t4 = self.font.render("Noclip / warping was used - this run doesn't count",
                                      True, (255, 120, 120))
                s.blit(t4, (W // 2 - t4.get_width() // 2, H // 2 + 52))

    # ---- main loop -----------------------------------------------------------------------
    def run(self):
        while True:
            for e in pygame.event.get():
                self.handle_event(e)
            self.update()
            self.draw()
            self.clock.tick(FPS)


if __name__ == "__main__":
    Game().run()
