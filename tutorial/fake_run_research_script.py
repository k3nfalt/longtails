"""Fake research step: install the prepared stochastic nonconvex tutorial."""

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main():
    source = ROOT / "tutorial/ToBeDiscovered"
    pending = []
    for path in sorted(source.rglob("*")):
        if path.suffix not in (".lean", ".md") or not path.is_file():
            continue
        destination = ROOT / "LongTails" / path.relative_to(source)
        content = path.read_text().replace(
            "import tutorial.ToBeDiscovered.", "import LongTails."
        )
        if destination.exists() or destination.is_symlink():
            if destination.is_symlink() or destination.read_text() != content:
                raise ValueError(
                    f"Refusing to overwrite {destination.relative_to(ROOT)}"
                )
        else:
            pending.append((destination, content))
    for destination, content in pending:
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("x") as output:
            output.write(content)
        print(f"Added {destination.relative_to(ROOT)}")
    print(
        f"Fake research complete: {len(pending)} files copied. No agents or Git operations were run."
    )


if __name__ == "__main__":
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        main()
    except (OSError, ValueError) as error:
        sys.exit(str(error))
