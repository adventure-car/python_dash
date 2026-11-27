# Hardest levels & player uploads — admin guide

This explains the two admin-facing systems that the game relies on:

1. **The hardest-levels list** (`hardest_levels.json`) — the official ranks shown in the
   level select's **Ranks** tab. The Top 1 (the `"first"` spot) is the level whose completion earns
   the Crown cube.
2. **Player uploads** — levels players send from inside the game, which an admin reviews and
   adds to the repo.

Reading from GitHub is public and needs no login. **Writing** (changing the ranks, adding a
level) is done by admins through normal Git / pull requests, protected by `CODEOWNERS`.

---

## 1. The hardest-levels list

`hardest_levels.json` lives at the repo root:

```json
{
  "first": "ingame:Velocity Finish",
  "second": "online:grief",
  "third": "ingame:Neon Gauntlet",
  "sixth": "",
  ...
  "twentieth": "",
  "info": {
    "ingame:Velocity Finish": {"maker": "AugmentedMagic", "verifier": "AXO",
                               "victors": ["AXO"], "frame_perfects": "0"},
    "online:grief": {"maker": "AugmentedMagic", "verifier": "AXO",
                     "victors": [], "frame_perfects": "0"}
  }
}
```

- **The spots are the ranking, hardest first:** `"first"` is the Top 1 demon, then
  `"second"` ... up to `"twentieth"`. **Blank spots (`""`) are skipped** - fill the next
  one in to add a level.
- `"ingame:<name>"` is a built-in level or a main level, by its exact name.
- `"online:<level>"` is a level in the repo's `levels/` folder: its file name without
  `.json` (like `grief` for `levels/grief.json`), or its level name. Players who haven't
  downloaded it see it on the Ranks tab with a GET tag; ENTER downloads and plays it.
- `"info"` holds what the Ranks card shows, keyed by the same text as the spot:
  `maker`, `verifier`, `victors`, `frame_perfects`. All optional; missing ones show as
  "unknown" / "none yet".
- (The older `{"ranks": [{"name": ...}, ...]}` list still works.)

The game fetches this file at startup on a background thread. If it's missing, unreachable,
or malformed, the game silently falls back to the ranks built into `python_dash.py`, so a
bad edit can never break the game — but it's still worth validating the JSON before merging.

### To change the ranks

Edit `hardest_levels.json` and open a PR (or commit, if you have direct access). Every
player picks up the change the next time they launch — no new game release needed. Changing
the Top 1 does **not** take the Crown away from anyone who already earned it.

---

## 2. Player uploads

Players press **U** on the *Your Levels* screen to upload a level. The game writes the
level's `.json` (with its song embedded, and the player's account name as `author`) into the
shared online folder:

```
<shared folder>/PythonDashSubmissions/
```

This is a **request**, not a direct add — players never need repository permission. As an
admin you then decide what to do with it.

### Reviewing uploads

Sign in as an admin, open **MAIN LEVELS**, and choose **OPEN UPLOADS FOLDER** (it shows how
many are waiting). Look through the submitted `.json` files.

### Adding an upload to the game

Pick one of these, depending on where the level should appear:

- **As a main level:** drop the `.json` into the **main levels folder** (the MAIN LEVELS
  screen's first entry), then give it a name and difficulty. This is instant and lives in
  the shared folder, so every player sees it.
- **As a downloadable / ranked level in this repo:** add the file under `levels/` and open a
  pull request. The `check_upload` workflow automatically validates it (size, loads cleanly,
  is beatable) and asks an admin to approve. Once merged it appears in the game's **Online**
  tab, and you can add it to `hardest_levels.json` to rank it.

Turn a submission down simply by deleting it from the uploads folder (or closing its PR).
