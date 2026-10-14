#!/usr/bin/env python3
"""Add uncategorized oracle setups to pending. Requires tomlkit."""

from pathlib import Path

import tomlkit


def update_pending(setups_dir, catalog):
    data = tomlkit.loads(catalog.read_text(encoding="utf-8"))
    listed = {
        entry["setup"] for section in data.values() for entry in section["setups"]
    }
    names = {
        path.relative_to(setups_dir).with_suffix("").as_posix()
        for path in setups_dir.rglob("*.lean")
    }
    missing = sorted(names - listed)
    if not missing and "pending" in data:
        return missing
    if "pending" not in data:
        data["pending"] = {"setups": tomlkit.array().multiline(True)}
    for name in missing:
        entry = tomlkit.inline_table()
        entry.update(setup=name, comment="")
        data["pending"]["setups"].append(entry)
    catalog.write_text(tomlkit.dumps(data), encoding="utf-8")
    return missing


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[1]
    added = update_pending(
        root / "LongTails/Setups", root / "scripts/approved_setups.toml"
    )
    print(f"Added {len(added)} pending setups.")
