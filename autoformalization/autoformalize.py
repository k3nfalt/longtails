"""Entrypoint for auto-math's autoformalization workflow."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "src"))
from autoformalize.cli import main

if __name__ == "__main__":
    raise SystemExit(main())
