# Main levels

Level files in this folder are **main levels**: every copy of Python Dash downloads
them and lists them on the Levels tab next to the built-in ones.

Only **AXO** and **AugmentedMagic** may change this folder (see
`.github/CODEOWNERS` and `.github/workflows/protect-main-levels.yml`).

## Adding a level

* Easiest: approve an upload on the review page of `python_dash_server.py` with
  **Approve as main level** - the server puts it here with its difficulty.
* By hand: add the level's `.json` here and give it a difficulty, either with a
  `"difficulty"` field in the file (`TEST`, `EASY`, `NORMAL`, `HARD`, `INSANE` or
  `DEMON`) or in `_main_levels.json`:

```json
{
  "my-level.json": {"name": "My Level", "difficulty": "HARD"}
}
```

`_main_levels.json` wins over the field in the file, and its `name` (optional)
renames the level in the game.
