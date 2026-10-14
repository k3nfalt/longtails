import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def current_commit():
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    ).stdout.strip()


def verified_output(output, check_commit=False):
    if not output.exists():
        return False
    if not check_commit:
        return True
    try:
        saved = json.loads(
            output.with_suffix(output.suffix + ".commit.json").read_text(
                encoding="utf-8"
            )
        )
    except (FileNotFoundError, ValueError):
        return False
    return isinstance(saved, dict) and saved.get("commit") == current_commit()


def write_description(output, text, commit, regenerate_all=False):
    if current_commit() != commit:
        raise ValueError(
            "Commit changed during description generation; output unchanged"
        )
    if not regenerate_all and verified_output(output):
        return
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".descriptions-", dir=output.parent) as tmp:
        draft = Path(tmp) / "description.tex"
        draft.write_text(text, encoding="utf-8")
        draft_record = Path(tmp) / "commit.json"
        draft_record.write_text(
            json.dumps({"commit": commit}, indent=2) + "\n", encoding="utf-8"
        )
        draft.replace(output)
        draft_record.replace(output.with_suffix(output.suffix + ".commit.json"))
