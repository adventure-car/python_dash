# Python Dash on phones (the web version)

Play in any browser - iPhone, Android, tablet or computer - with nothing to install:

**https://adventure-car.github.io/python_dash/**

Tap the page once to start (browsers only allow sound after a tap). On a phone, turn
it sideways. "Add to Home Screen" (Safari: Share button; Chrome: menu) puts it on your
home screen like an app.

## How it works
- It's the same `python_dash.py` as the desktop game, run in the browser by
  [pygbag](https://pygame-web.github.io/).
- **It updates itself on every launch:** `main.py` downloads the newest
  `python_dash.py` from GitHub and runs it. Offline - or if the newest copy can't run in
  a browser - it uses the copy built into the page.
- The page itself is rebuilt and put on GitHub Pages automatically whenever
  `python_dash.py` or this folder changes on `main` (`.github/workflows/web.yml`).
- **Saves** (progress, settings, levels you build or download) are kept in the browser,
  on that phone. Sign in to sync progress through the server instead.
- Online levels, the hardest-levels list and songs download from GitHub as usual.

## Limits
- Touch works for playing and the menus (tap = click), and the pause screen has RETRY.
  The level **editor** needs a keyboard and right-clicks, so it's best on a computer.
- Typing (sign in, search) needs a keyboard too.
- Signing in and syncing need the server to be on **https** (a web page on https can't
  talk to an `http://` address) - e.g. `https://python-dash.net/server` through a
  Cloudflare Tunnel.
- Songs: browsers play `.ogg` most reliably; some can't play `.mp3`.

## One-time setup (repo owner)
Settings -> Pages -> Build and deployment -> Source: **GitHub Actions**. Then run
Actions -> "Web version" -> Run workflow (or merge a change to the game).

## Building it yourself
```bash
pip install pygbag==0.9.3
mkdir -p build_web && cp web/main.py python_dash.py build_web/
python -m pygbag build_web        # then open http://localhost:8000
```
