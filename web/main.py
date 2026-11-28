# Python Dash in the browser - built with pygbag (see web/README.md).
#
# On launch this:
#   1. puts back your saves (progress, settings, your levels, downloads) from the
#      browser's storage - a web page can't keep files, so they live there
#   2. downloads the newest python_dash.py from GitHub, so the game updates itself on
#      every launch (offline - or if the download is broken - it uses the copy that
#      was built into this page)
#   3. runs the game, and every couple of seconds saves anything that changed back into
#      the browser's storage
import asyncio
import base64
import importlib.util
import os
import sys
import time

import platform as jsp          # (pygbag: the browser's window)

import pygame                   # noqa: F401  (pygbag installs what main.py imports - the
#                                 game itself is loaded from a file below)

GAME_URL = "https://raw.githubusercontent.com/adventure-car/python_dash/main/python_dash.py"
HERE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(os.path.expanduser("~"), ".python_dash")
STORE = "pd:"                    # browser-storage keys: "pd:" + path inside DATA_DIR
SKIP = ("music", "live")        # songs and the game file can be downloaded again
MAX_FILE = 900 * 1024            # (the browser only keeps a few MB for a page)


# ---- saves <-> the browser's storage -------------------------------------------------
def storage():
    return jsp.window.localStorage


def restore_saves():
    """Put the files saved in the browser back where the game looks for them."""
    st = storage()
    n = 0
    for i in range(int(st.length)):
        key = str(st.key(i))
        if not key.startswith(STORE):
            continue
        rel = key[len(STORE):]
        if ".." in rel.split("/"):
            continue
        path = os.path.join(DATA_DIR, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "wb") as f:
            f.write(base64.b64decode(str(st.getItem(key))))
        n += 1
    print("restored %d saved files" % n)


class Saver:
    """Copies changed save files into the browser's storage, now and then."""

    def __init__(self):
        self.seen = {}
        self.next = time.time() + 2
        self.scan(write=False)               # (what's there now is already stored)

    def files(self):
        for root, dirs, names in os.walk(DATA_DIR):
            rel_root = os.path.relpath(root, DATA_DIR)
            if rel_root.split(os.sep)[0] in SKIP:
                dirs[:] = []
                continue
            for n in names:
                path = os.path.join(root, n)
                yield os.path.relpath(path, DATA_DIR).replace(os.sep, "/"), path

    def scan(self, write=True):
        st = storage()
        now = {}
        for rel, path in self.files():
            try:
                sig = (os.path.getsize(path), os.path.getmtime(path))
            except OSError:
                continue
            now[rel] = sig
            if write and self.seen.get(rel) != sig and sig[0] <= MAX_FILE:
                with open(path, "rb") as f:
                    try:
                        st.setItem(STORE + rel, base64.b64encode(f.read()).decode("ascii"))
                    except Exception as ex:          # storage full
                        print("couldn't save", rel, ex)
        if write:
            for rel in set(self.seen) - set(now):    # deleted in the game
                st.removeItem(STORE + rel)
        self.seen = now

    def tick(self):
        if time.time() >= self.next:
            self.next = time.time() + 2
            self.scan()


# ---- the newest game from GitHub ------------------------------------------------------
_JS_GET = """
window.pd_get = function (url) {
    var x = new XMLHttpRequest();
    try { x.open("GET", url, false); x.send(null); } catch (e) { return ""; }
    return x.status === 200 ? x.responseText : "";
};
"""


def newest_game():
    """The path of the game file to run: the newest one from GitHub, or the built-in."""
    built_in = os.path.join(HERE, "python_dash.py")
    try:
        jsp.window.eval(_JS_GET)
        src = str(jsp.window.pd_get(GAME_URL + "?t=%d" % int(time.time())))
        if src and "async def run_async" not in src:
            print("the newest game on GitHub can't run in a browser yet - using the "
                  "built-in one")
            src = ""
        if src:
            compile(src, "python_dash.py", "exec")    # (never run a broken download)
            live = os.path.join(DATA_DIR, "live")
            os.makedirs(live, exist_ok=True)
            path = os.path.join(live, "python_dash.py")
            with open(path, "w", encoding="utf-8") as f:
                f.write(src)
            print("running the newest game from GitHub")
            return path
    except Exception as ex:
        print("couldn't get the newest game, using the built-in one:", ex)
    return built_in


def load_game(path):
    spec = importlib.util.spec_from_file_location("python_dash", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["python_dash"] = mod
    spec.loader.exec_module(mod)
    return mod


async def main():
    os.makedirs(DATA_DIR, exist_ok=True)
    try:
        restore_saves()
    except Exception as ex:
        print("couldn't restore saves:", ex)
    try:
        game_mod = load_game(newest_game())
    except Exception as ex:                           # (a bad newest copy: built-in)
        print("the newest game didn't start, using the built-in one:", ex)
        game_mod = load_game(os.path.join(HERE, "python_dash.py"))
    saver = Saver()
    await game_mod.Game().run_async(every_frame=saver.tick)


asyncio.run(main())
