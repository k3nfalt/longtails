#!/usr/bin/env python3

import argparse
import re
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:
    import tomlkit as tomllib

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run_results_table_prompt import FOOTER, HEADER, split_tables


def create_table(directory, approvals):
    approved = {
        entry["setup"]
        for entry in tomllib.loads(approvals.read_text(encoding="utf-8"))["approved"]["setups"]
    }
    rows = []
    for setup in sorted(approved):
        if not re.fullmatch(r"[A-Za-z0-9_]+", setup):
            raise ValueError(f"invalid setup name: {setup}")
        path = directory / "tables" / f"{setup}.tex"
        if not path.is_file():
            print(f"WARNING: skipping approved setup without a table: {setup}", file=sys.stderr)
            continue
        parts = split_tables(path.read_text(encoding="utf-8"))
        if len(parts) != 1 or parts[0][1] != setup:
            raise ValueError(f"setup filename and label disagree: {path}")
        rows.extend(parts)
    if not rows:
        raise ValueError("no approved tables found; existing results_table.tex preserved")
    rows.sort(key=lambda row: (-row[0], row[1]))
    target = directory / "results_table.tex"
    target.write_text(
        HEADER + "".join(r"\input{tables/" + row[1] + ".tex}\n" for row in rows) + FOOTER,
        encoding="utf-8",
    )
    return target


def main(argv=None):
    scripts = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description="Assemble existing approved tables into results_table.tex.")
    parser.add_argument("--tables-dir", type=Path, default=scripts / "tables",
                        help="Directory containing tables/ and the bibliography (default: scripts/tables)")
    args = parser.parse_args(argv)
    try:
        target = create_table(args.tables_dir.expanduser().resolve(), scripts / "approved_setups.toml")
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.error(str(error))
    print(f"Created {target}")


if __name__ == "__main__":
    main()
