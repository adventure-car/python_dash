# Hardest levels & player uploads — admin guide

This explains the two admin-facing systems that the game relies on:

1. **The hardest-levels list** (`hardest_levels.json`) — the official ranks shown in the
   level select's **Ranks** tab. The Top 1 (entry `0`) is the level whose completion earns
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
  "ranks": [
    {"name": "Velocity Finish", "maker": "AugmentedMagic", "verifier": "AXO",
     "victors": ["AXO"], "frame_perfects": "0"},
    ...
  ]
}
```

- **Order is the ranking, hardest first.** `ranks[0]` is the Top 1 demon.
- Levels are matched to the game **by `name`** (it must match the level's name exactly —
  built-in levels and main levels are both eligible).
- `maker`, `verifier`, `victors`, `frame_perfects` are shown on the Ranks card. They are
  optional; missing fields show as "unknown" / "none yet".

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
