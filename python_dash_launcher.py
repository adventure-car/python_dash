#!/usr/bin/env python3
"""
Python Dash launcher + auto-updater.

What it does
------------
* Opens a small menu with a Play button and an Update button.
* When the menu opens (and every time Update is pressed) it:
    1. Downloads the latest python_dash.py from GitHub and compares it with the
       version the player has. If it is different, it replaces the player's copy.
       If the player has no copy, it is saved in their user (home) folder.
    2. Runs Update(), which makes the installed script smaller.
* Play launches the game.
* Hosts the Python Dash server: on the computer that has python_dash_server.py (in
  your home folder, ~/PythonDash, or next to this launcher) it starts the server in
  the background when the launcher opens, if it isn't running already.  It keeps
  running after the launcher and the game close.  Switch it ON / OFF for players on
  its review page (http://localhost:8766) - while it's off, games go to the backup
  servers in python_dash.py.  Your own game talks to it on this computer.
  Later, to use an AWS server instead: copy python_dash_server.py there, put its
  address in SERVER_URL in python_dash.py, and switch this one off (or delete it).

Usage
-----
    python python_dash_launcher.py                      # pick the location from the menu
    python python_dash_launcher.py --path ~/Games       # skip the picker (folder or file)

The first time it runs, a file browser opens so the player can find their copy of
python_dash.py (or choose the folder it should be installed into). The choice is
remembered, and the "Change Location" button reopens the browser any time.

Requires: pygame-ce (or pygame).  Everything else is standard library.
"""

import argparse
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
from pathlib import Path

# --------------------------------------------------------------------------
# CONFIG - edit these to point at your repository
# --------------------------------------------------------------------------
GITHUB_OWNER = "adventure-car"
GITHUB_REPO = "python_dash"
GITHUB_BRANCH = "main"
GAME_FILENAME = "python_dash.py"

# Where the game goes if the player doesn't have it yet (their user folder).
DEFAULT_INSTALL_DIR = Path.home()

# For a private repo, set a token in the GITHUB_TOKEN environment variable.
RAW_URL = (
    f"https://raw.githubusercontent.com/"
    f"{GITHUB_OWNER}/{GITHUB_REPO}/{GITHUB_BRANCH}/{GAME_FILENAME}"
)

# The Python Dash server (python_dash_server.py) - hosted from here if you have it.
SERVER_FILENAME = "python_dash_server.py"
SERVER_PLACES = [Path.home(), Path.home() / "PythonDash", Path(__file__).resolve().parent]
SERVER_PORT = 8765                                   # API_PORT in python_dash_server.py
SERVER_DATA = Path.home() / ".python_dash_server"
SERVER_PID = SERVER_DATA / "server.pid"
SERVER_LOG = SERVER_DATA / "server.log"
LOCAL_SERVER = f"http://127.0.0.1:{SERVER_PORT}"

CONFIG_FILE = Path(__file__).with_name("launcher_config.json")
VERSION_FILE_NAME = ".python_dash_version"  # sits next to the game file
NETWORK_TIMEOUT = 15


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------
def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def atomic_write(path: Path, data: bytes) -> None:
    """Write via a temp file so a crash never leaves a half-written game."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=".pd_tmp_")
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
        os.replace(tmp, path)
    except BaseException:
        if os.path.exists(tmp):
            os.remove(tmp)
        raise


def resolve_game_path(raw: str | None) -> Path:
    """Turn what the player typed into the full path of python_dash.py."""
    if not raw:
        return DEFAULT_INSTALL_DIR / GAME_FILENAME
    p = Path(raw).expanduser()
    if p.is_dir() or p.suffix == "":
        p = p / GAME_FILENAME
    return p


def load_config() -> dict:
    try:
        return json.loads(CONFIG_FILE.read_text())
    except (OSError, ValueError):
        return {}


def save_config(cfg: dict) -> None:
    try:
        CONFIG_FILE.write_text(json.dumps(cfg, indent=2))
    except OSError:
        pass


# --------------------------------------------------------------------------
# Checking GitHub and installing
# --------------------------------------------------------------------------
def fetch_remote() -> bytes:
    headers = {"User-Agent": "python-dash-launcher"}
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"token {token}"
    req = urllib.request.Request(RAW_URL, headers=headers)
    with urllib.request.urlopen(req, timeout=NETWORK_TIMEOUT) as resp:
        data = resp.read()
    # Sanity check: never install something that isn't valid Python.
    ast.parse(data.decode("utf-8"))
    return data


def check_and_install(game_path: Path) -> str:
    """Compare GitHub's copy with the player's; replace/install if different.

    The local file gets shrunk by Update(), so its hash will never match
    GitHub's. We therefore remember the hash of the GitHub version we last
    installed (in a small sidecar file) and compare GitHub against that.
    """
    remote = fetch_remote()
    remote_hash = sha256(remote)
    version_file = game_path.with_name(VERSION_FILE_NAME)

    try:
        recorded = version_file.read_text().strip()
    except OSError:
        recorded = None

    if not game_path.exists():
        atomic_write(game_path, remote)
        version_file.write_text(remote_hash)
        return f"Installed Python Dash to {game_path.parent}"

    if recorded is None:
        # A copy we've never managed: compare it directly.
        if sha256(game_path.read_bytes()) == remote_hash:
            version_file.write_text(remote_hash)
            return "Already up to date"
        atomic_write(game_path, remote)
        version_file.write_text(remote_hash)
        return "Updated to the latest version"

    if recorded != remote_hash:
        atomic_write(game_path, remote)
        version_file.write_text(remote_hash)
        return "Updated to the latest version"

    return "Already up to date"


# --------------------------------------------------------------------------
# Hosting the Python Dash server
# --------------------------------------------------------------------------
def find_server() -> Path | None:
    """python_dash_server.py, if this computer has it (only the host does)."""
    for place in SERVER_PLACES:
        p = place / SERVER_FILENAME
        if p.is_file():
            return p
    return None


def server_status() -> dict | None:
    """The local server's status ({"ok", "hosting"}), or None if it isn't running."""
    try:
        with urllib.request.urlopen(LOCAL_SERVER + "/api/status", timeout=1.5) as r:
            j = json.loads(r.read().decode("utf-8"))
            return j if isinstance(j, dict) and j.get("ok") else None
    except Exception:
        return None


def server_running() -> bool:
    return server_status() is not None


def start_server(path: Path) -> str:
    if server_running():
        return "The server is already running"
    SERVER_DATA.mkdir(parents=True, exist_ok=True)
    log = open(SERVER_LOG, "ab")
    kwargs = {}
    if sys.platform.startswith("win"):        # keep running after the launcher closes
        kwargs["creationflags"] = (subprocess.CREATE_NEW_PROCESS_GROUP
                                   | getattr(subprocess, "DETACHED_PROCESS", 0x8))
    else:
        kwargs["start_new_session"] = True
    try:
        proc = subprocess.Popen([sys.executable, str(path)], cwd=str(path.parent),
                                stdout=log, stderr=subprocess.STDOUT,
                                stdin=subprocess.DEVNULL, **kwargs)
    except OSError as e:
        return f"Couldn't start the server ({e.strerror or e})"
    finally:
        log.close()
    SERVER_PID.write_text(str(proc.pid))
    for _ in range(20):                        # wait up to ~5 s for it to answer
        if server_running():
            return "Server started - players can sign in and upload"
        if proc.poll() is not None:
            return f"The server stopped straight away - see {SERVER_LOG}"
        time.sleep(0.25)
    return f"Server starting... (if it doesn't come on, see {SERVER_LOG})"


# --------------------------------------------------------------------------
# Update(): make the installed script smaller
# --------------------------------------------------------------------------
def _strip_docstrings(tree: ast.AST) -> None:
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef)):
            body = node.body
            if (body and isinstance(body[0], ast.Expr)
                    and isinstance(body[0].value, ast.Constant)
                    and isinstance(body[0].value.value, str)):
                node.body = body[1:] or [ast.Pass()]


def _minify(source: str) -> str:
    """Remove comments, docstrings, blank lines and extra spacing."""
    tree = ast.parse(source)
    _strip_docstrings(tree)
    base = ast.unparse(tree)  # drops comments and normalises spacing

    # Shrink 4-space indents to 1 space - but only keep it if the code
    # still parses to the exact same syntax tree.
    squeezed = re.sub(
        r"(?m)^(?: {4})+",
        lambda m: " " * (len(m.group(0)) // 4),
        base,
    )
    try:
        if ast.dump(ast.parse(squeezed)) == ast.dump(ast.parse(base)):
            return squeezed
    except SyntaxError:
        pass
    return base


def Update(game_path: Path | None = None) -> str:
    """Make the player's copy of python_dash.py smaller.

    Safe by design: if anything goes wrong, or the result isn't smaller,
    the file is left untouched.
    """
    game_path = game_path or resolve_game_path(load_config().get("path"))
    if not game_path.exists():
        return "Nothing to shrink yet"
    try:
        original = game_path.read_text(encoding="utf-8")
        smaller = _minify(original)
        compile(smaller, str(game_path), "exec")  # final safety check
    except (SyntaxError, ValueError, OSError) as e:
        return f"Skipped shrinking ({type(e).__name__})"

    before = len(original.encode("utf-8"))
    smaller += "\n"
    after = len(smaller.encode("utf-8"))
    if after >= before:
        return "Already as small as it gets"
    atomic_write(game_path, smaller.encode("utf-8"))
    return f"Shrunk {before:,} -> {after:,} bytes"


# --------------------------------------------------------------------------
# Menu (pygame)
# --------------------------------------------------------------------------
class State:
    def __init__(self):
        self.status = "Starting..."
        self.busy = False
        self.lock = threading.Lock()

    def set(self, text: str) -> None:
        with self.lock:
            self.status = text


def run_update_async(state: State, game_path: Path) -> None:
    """Check GitHub, install if needed, then run Update() - off the UI thread."""
    with state.lock:
        if state.busy:
            return
        state.busy = True

    def worker():
        try:
            state.set("Checking GitHub...")
            try:
                msg = check_and_install(game_path)
            except urllib.error.HTTPError as e:
                msg = f"GitHub error {e.code} - using your copy"
            except (urllib.error.URLError, TimeoutError):
                msg = "Offline - using your copy"
            except (OSError, SyntaxError, UnicodeDecodeError) as e:
                msg = f"Update failed ({type(e).__name__})"
            shrink = Update(game_path)
            state.set(f"{msg}. {shrink}.")
        finally:
            with state.lock:
                state.busy = False

    threading.Thread(target=worker, daemon=True).start()


def browse_for_game(screen, start: Path) -> Path | None:
    """In-window file browser.

    Click folders to open them, click a .py file to choose it, or press
    "Use this folder" to pick the folder itself (python_dash.py is then
    installed there if it isn't already). Returns None if cancelled.
    """
    import pygame

    clock = pygame.time.Clock()
    font = pygame.font.Font(None, 28)
    small = pygame.font.Font(None, 22)
    w, h = screen.get_size()
    row_h, list_top, list_bottom = 32, 56, h - 76
    use_btn = pygame.Rect(w - 380, h - 58, 210, 44)
    cancel_btn = pygame.Rect(w - 150, h - 58, 130, 44)

    cur = start if start.is_dir() else start.parent
    if not cur.is_dir():
        cur = Path.home()

    def list_rows(d: Path):
        rows = []
        if d.parent != d:
            rows.append(("..  (up one folder)", d.parent, "dir"))
        try:
            items = sorted(d.iterdir(), key=lambda q: q.name.lower())
        except OSError:
            return rows
        for q in items:
            if q.name.startswith("."):
                continue
            try:
                if q.is_dir():
                    rows.append((q.name + "/", q, "dir"))
            except OSError:
                continue
        for q in items:
            try:
                if q.is_file() and q.suffix == ".py":
                    rows.append((q.name, q, "file"))
            except OSError:
                continue
        return rows

    def shorten(text, f, width):
        while f.size(text)[0] > width and len(text) > 4:
            text = "..." + text[4:]
        return text

    rows, scroll = list_rows(cur), 0
    result, done = None, False
    while not done:
        max_scroll = max(0, len(rows) * row_h - (list_bottom - list_top))
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.event.post(pygame.event.Event(pygame.QUIT))
                done = True
            elif event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
                done = True
            elif event.type == pygame.MOUSEWHEEL:
                scroll = max(0, min(max_scroll, scroll - event.y * row_h))
            elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                x, y = event.pos
                if cancel_btn.collidepoint(x, y):
                    done = True
                elif use_btn.collidepoint(x, y):
                    result, done = cur, True
                elif list_top <= y < list_bottom:
                    i = (y - list_top + scroll) // row_h
                    if 0 <= i < len(rows):
                        _, target, kind = rows[i]
                        if kind == "file":
                            result, done = target, True
                        else:
                            cur, rows, scroll = target, list_rows(target), 0

        screen.fill((24, 24, 32))
        head_txt = font.render(shorten(str(cur), font, w - 30), True, (255, 220, 60))
        screen.blit(head_txt, (15, 16))
        mouse = pygame.mouse.get_pos()
        screen.set_clip(pygame.Rect(0, list_top, w, list_bottom - list_top))
        for i, (label, _, kind) in enumerate(rows):
            r = pygame.Rect(10, list_top + i * row_h - scroll, w - 20, row_h - 2)
            if r.bottom < list_top or r.top > list_bottom:
                continue
            if r.collidepoint(mouse) and list_top <= mouse[1] < list_bottom:
                pygame.draw.rect(screen, (50, 55, 75), r, border_radius=6)
            color = (140, 200, 255) if kind == "dir" else (180, 255, 180)
            screen.blit(font.render(shorten(label, font, w - 50), True, color),
                        (r.x + 10, r.y + 6))
        if not rows:
            screen.blit(small.render("(empty)", True, (120, 120, 135)), (20, list_top + 6))
        screen.set_clip(None)

        pygame.draw.line(screen, (60, 60, 75), (0, list_bottom + 4), (w, list_bottom + 4))
        screen.blit(small.render("Click your python_dash.py, or open its folder", True,
                                 (120, 120, 135)), (15, h - 50))
        screen.blit(small.render("and press Use this folder.", True, (120, 120, 135)),
                    (15, h - 30))
        for rect, label in ((use_btn, "Use this folder"), (cancel_btn, "Cancel")):
            col = (60, 160, 255) if rect.collidepoint(mouse) else (40, 120, 220)
            pygame.draw.rect(screen, col, rect, border_radius=10)
            t = font.render(label, True, (255, 255, 255))
            screen.blit(t, t.get_rect(center=rect.center))

        pygame.display.flip()
        clock.tick(30)

    return result


def run_menu(game_path: Path | None) -> None:
    import pygame

    pygame.init()
    server_file = find_server()                  # None for everyone but the host
    extra = 30 if server_file else 0
    screen = pygame.display.set_mode((640, 440 + extra))
    pygame.display.set_caption("Python Dash Launcher")
    clock = pygame.time.Clock()
    title_font = pygame.font.Font(None, 72)
    btn_font = pygame.font.Font(None, 44)
    small_font = pygame.font.Font(None, 24)

    play_btn = pygame.Rect(0, 0, 280, 60)
    update_btn = pygame.Rect(0, 0, 280, 60)
    loc_btn = pygame.Rect(0, 0, 280, 52)
    play_btn.center = (320, 150)
    update_btn.center = (320, 222)
    loc_btn.center = (320, 292)

    state = State()
    hosting = {"on": False, "players": True, "note": ""}   # is the server running?

    def host_server():
        """Start the server if it isn't running, then keep an eye on it."""
        if not server_running():
            hosting["note"] = start_server(server_file)
        while True:
            st = server_status()
            hosting["on"] = st is not None
            hosting["players"] = bool(st and st.get("hosting", True))
            time.sleep(2)

    if server_file:
        threading.Thread(target=host_server, daemon=True).start()

    def choose_location(start: Path) -> Path | None:
        """Open the browser; returns the chosen game path (or None)."""
        picked = browse_for_game(screen, start)
        if picked is None:
            return None
        chosen = resolve_game_path(str(picked))
        cfg = load_config()
        cfg["path"] = str(chosen)
        save_config(cfg)
        return chosen

    # First run (no saved location): let the player find their copy.
    if game_path is None:
        game_path = choose_location(Path.home()) or resolve_game_path(None)

    run_update_async(state, game_path)  # menu just opened -> update

    def draw_button(rect, label, enabled=True, font=btn_font):
        hover = enabled and rect.collidepoint(pygame.mouse.get_pos())
        color = (70, 70, 80) if not enabled else (60, 160, 255) if hover else (40, 120, 220)
        pygame.draw.rect(screen, color, rect, border_radius=12)
        text = font.render(label, True, (255, 255, 255))
        screen.blit(text, text.get_rect(center=rect.center))

    def shorten(text, font, width):
        while font.size(text)[0] > width and len(text) > 4:
            text = "..." + text[4:]
        return text

    running = True
    while running:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                if state.busy:
                    continue
                if update_btn.collidepoint(event.pos):
                    run_update_async(state, game_path)
                elif loc_btn.collidepoint(event.pos):
                    new_path = choose_location(game_path)
                    if new_path is not None:
                        game_path = new_path
                        run_update_async(state, game_path)
                elif play_btn.collidepoint(event.pos):
                    if game_path.exists():
                        env = dict(os.environ)
                        if server_file and hosting["on"]:
                            # the host's own game uses the server on this computer
                            env["PYTHON_DASH_SERVER"] = LOCAL_SERVER
                        subprocess.Popen(
                            [sys.executable, str(game_path)],
                            cwd=str(game_path.parent), env=env,
                        )
                        running = False
                    else:
                        state.set("Not installed yet - press Update")

        screen.fill((24, 24, 32))
        title = title_font.render("Python Dash", True, (255, 220, 60))
        screen.blit(title, title.get_rect(center=(320, 70)))
        draw_button(play_btn, "Play", enabled=not state.busy)
        draw_button(update_btn, "Update", enabled=not state.busy)
        draw_button(loc_btn, "Change Location", enabled=not state.busy, font=small_font)
        if server_file:
            if hosting["on"]:
                text = ("Server ON for players" if hosting["players"] else
                        "Server switched OFF for players") + "  -  switch: localhost:8766"
            else:
                text = hosting["note"] or "Starting the server..."
            dot = ((90, 230, 120) if hosting["players"] else (255, 200, 60)) \
                if hosting["on"] else (220, 80, 90)
            st = small_font.render(shorten(text, small_font, 560), True, (200, 200, 210))
            r = st.get_rect(center=(330, 345))
            screen.blit(st, r)
            pygame.draw.circle(screen, dot, (r.left - 14, r.centery), 6)

        with state.lock:
            status = state.status
        msg = small_font.render(shorten(status, small_font, 600), True, (200, 200, 210))
        screen.blit(msg, msg.get_rect(center=(320, 360 + extra)))
        path_txt = small_font.render(
            shorten(str(game_path), small_font, 600), True, (120, 120, 135))
        screen.blit(path_txt, path_txt.get_rect(center=(320, 395 + extra)))

        pygame.display.flip()
        clock.tick(30)

    pygame.quit()


# --------------------------------------------------------------------------
def main() -> None:
    parser = argparse.ArgumentParser(description="Python Dash launcher/updater")
    parser.add_argument("--path", help="Folder (or file) where python_dash.py lives "
                                       "(skips the location picker)")
    args = parser.parse_args()

    cfg = load_config()
    raw = args.path or cfg.get("path")
    game_path = resolve_game_path(raw) if raw else None  # None -> picker opens

    if game_path is not None:
        cfg["path"] = str(game_path)
        save_config(cfg)

    run_menu(game_path)


if __name__ == "__main__":
    main()
