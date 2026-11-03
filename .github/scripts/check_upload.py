#!/usr/bin/env python3
"""
Checks the files in an upload (pull request) to the Python Dash repo and writes a
report for the admins, in Markdown.

    python check_upload.py changed.txt <upload folder> <main branch folder>

changed.txt lists the uploaded files.  The uploaded files are only READ as data;
the game code used for the checks always comes from the main branch.
"""
import glob
import json
import os
import signal
import sys

MAX_LEVEL_MB = 25          # level files (a level can carry its song inside it)
MAX_SONG_MB = 20
MUSIC_EXTS = (".mp3", ".ogg", ".wav", ".flac", ".opus")
SOLVE_SECONDS = 600        # longest we spend checking one level is beatable


def admins(base):
    """The admins' GitHub names, from CODEOWNERS (the /levels/ line)."""
    try:
        with open(os.path.join(base, ".github", "CODEOWNERS")) as f:
            for line in f:
                parts = line.split()
                if parts and parts[0].rstrip("/") == "/levels":
                    return [p for p in parts[1:] if p.startswith("@")]
    except OSError:
        pass
    return []


def load_game(base):
    """Import python_dash (and verify_levels, if it's there) from the main branch."""
    found = glob.glob(os.path.join(base, "**", "python_dash.py"), recursive=True)
    if not found:
        return None, None
    sys.path.insert(0, os.path.dirname(found[0]))
    try:
        import python_dash as pd
    except Exception:
        return None, None
    try:
        import verify_levels as vl
    except Exception:
        vl = None
    return pd, vl


class TooSlow(Exception):
    pass


def _alarm(*_):
    raise TooSlow()


def check_level(path, pd, vl, existing_names):
    """(ok, list of report lines) for one level file."""
    lines = []
    size = os.path.getsize(path) / 1e6
    if size > MAX_LEVEL_MB:
        return False, ["- File is %.1f MB - the limit is %d MB" % (size, MAX_LEVEL_MB)]
    try:
        with open(path, encoding="utf-8") as f:
            j = json.load(f)
    except Exception as ex:
        return False, ["- Not a valid level file (couldn't read it as JSON: %s)" % ex]
    if not isinstance(j, dict) or not isinstance(j.get("cells"), list):
        return False, ["- Not a Python Dash level (it has no \"cells\" list)"]
    name = str(j.get("name", "")).strip() or "(no name)"
    author = str(j.get("author", "")).strip()
    lines.append("- **%s**%s" % (name, (" by " + author) if author else "  (no author set)"))
    if name.lower() in existing_names:
        lines.append("- Note: a level called \"%s\" is already in the repo" % name)
    if pd is None:
        lines.append("- Couldn't load the game to check it further "
                     "(is python_dash.py in the repo?)")
        return True, lines
    j2 = dict(j)
    j2.pop("music_data", None)
    try:
        data = pd.LevelData.from_json(j2)
    except Exception as ex:
        return False, lines + ["- The game can't load it: %s" % ex]
    dropped = len(j["cells"]) - len(data.cells)
    lines.append("- %d objects, modes: %s" % (data.object_count(), " > ".join(data.mode_list())))
    if dropped:
        lines.append("- %d objects were invalid and would be ignored" % dropped)
    if data.coin_count():
        lines.append("- %d coin%s" % (data.coin_count(), "" if data.coin_count() == 1 else "s"))
    if j.get("music"):
        lines.append("- Song: %s%s" % (j["music"], " (included in the file)"
                                       if j.get("music_data") else ""))
    if vl is not None:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(SOLVE_SECONDS)
        try:
            lv = pd.Level(pd.custom_def(data))
            ok, pct = vl.solve(lv)[:2]
            lines.append("- Beatable: **yes**" if ok else
                         "- Beatable: **NO** - every possible run dies at about %d%%" % pct)
        except TooSlow:
            lines.append("- Beatable: not checked (took longer than %d minutes)"
                         % (SOLVE_SECONDS // 60))
        except Exception as ex:
            lines.append("- Beatable: couldn't check (%s)" % ex)
        finally:
            signal.alarm(0)
    return True, lines


def main(changed_txt, upload, base):
    with open(changed_txt) as f:
        changed = [ln.strip() for ln in f if ln.strip()]
    pd, vl = load_game(base)
    existing = set()
    for p in glob.glob(os.path.join(base, "levels", "*.json")):
        try:
            with open(p, encoding="utf-8") as f:
                existing.add(str(json.load(f).get("name", "")).strip().lower())
        except Exception:
            pass
    out, problems, warnings = [], 0, []
    for rel in changed:
        path = os.path.join(upload, rel)
        low = rel.lower()
        if low.startswith("levels/") and low.endswith(".json"):
            if not os.path.isfile(path):
                continue
            ok, lines = check_level(path, pd, vl, existing - {""})
            problems += not ok
            out += ["", "### %s `%s`" % ("✅" if ok else "❌", rel)] + lines
        elif low.startswith("music/") and low.endswith(MUSIC_EXTS):
            size = os.path.getsize(path) / 1e6 if os.path.isfile(path) else 0
            ok = size <= MAX_SONG_MB
            problems += not ok
            out += ["", "### %s `%s`" % ("✅" if ok else "❌", rel)]
            out.append("- Song, %.1f MB%s" % (size, "" if ok else
                                                " - the limit is %d MB" % MAX_SONG_MB))
        else:
            warnings.append(rel)
    who = os.environ.get("UPLOADER", "someone")
    head = ["## New upload from @%s needs approval" % who, ""]
    names = admins(base)
    if names:
        head.append("%s - please review this upload. **Approve** it and merge it to add it "
                    "to the game, or close it to turn it down." % " ".join(names))
    else:
        head.append("Admins: please review this upload.")
    head.append("")
    if problems:
        head.append("❌ **%d file%s ha%s problems** - see below." % (
            problems, "" if problems == 1 else "s", "s" if problems == 1 else "ve"))
        head.append("")
    if warnings:
        head.append("⚠️ **This upload also changes files outside `levels/` and `music/`** - "
                    "look at these carefully before approving:")
        head += ["- `%s`" % w for w in warnings]
        head.append("")
    print("\n".join(head + out))


if __name__ == "__main__":
    main(*sys.argv[1:4])
