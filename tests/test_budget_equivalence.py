import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = Path("scripts/check_budget_equivalence.py")
TARGET = Path("LongTails/Theorems/Example.lean")
SOURCE = """import LongTails.Helper
namespace OracleTemplate.Example
def budget (p : Nat) := p + offset
theorem result : budget 2 > 0 := by decide
end OracleTemplate.Example
"""


class BudgetEquivalenceTests(unittest.TestCase):
    @unittest.skipUnless(
        os.environ.get("GITHUB_EVENT_NAME") == "pull_request", "requires a PR base"
    )
    def test_edited_pr_budgets(self):
        event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
        base = event["pull_request"]["base"]["sha"]
        subprocess.run([sys.executable, ROOT / SCRIPT, base], cwd=ROOT, check=True)

    def test_git_to_lean_comparison(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, text=True)

            def commit():
                git("add", ".")
                git(
                    "-c",
                    "user.name=Test",
                    "-c",
                    "user.email=test@example.org",
                    "commit",
                    "-qm",
                    "fixture",
                )

            (root / TARGET.parent).mkdir(parents=True)
            (root / SCRIPT.parent).mkdir()
            shutil.copy(ROOT / SCRIPT, root / SCRIPT)
            shutil.copy(ROOT / "lean-toolchain", root)
            (root / ".gitignore").write_text(".lake/\nlake-manifest.json\n")
            (root / "lakefile.toml").write_text(
                'name = "fixture"\n[[lean_lib]]\nname = "LongTails"\n'
            )
            helper = root / "LongTails/Helper.lean"
            helper.write_text("def offset := 1\n")
            (root / TARGET).write_text(SOURCE)
            git("init", "-q")
            commit()
            base = git("rev-parse", "HEAD").strip()

            # A new module is outside this check even when an existing target is edited.
            (root / TARGET.parent / "New.lean").write_text(
                '#error "must not build an unrelated target"'
            )
            commit()
            skipped = subprocess.check_output(
                [sys.executable, SCRIPT, base], cwd=root, text=True
            )
            self.assertIn("No existing public theorem files changed", skipped)

            for case, revised, expected in [
                (
                    "factored budget",
                    SOURCE.replace("p + offset", "let a := offset; p + a"),
                    "Lean proved equality",
                ),
                (
                    "different budget with a valid proof",
                    SOURCE.replace("p + offset", "p + 2"),
                    "rfl",
                ),
                (
                    "different claim with the same budget",
                    SOURCE.replace("budget 2 > 0", "budget 2 = 3"),
                    "rfl",
                ),
                (
                    "changed imported constant",
                    SOURCE + "\n",
                    "baseline import LongTails/Helper.lean also changed",
                ),
                ("deleted public theorem", None, "removed or replaced"),
            ]:
                with self.subTest(case=case):
                    if revised is None:
                        (root / TARGET).unlink()
                    else:
                        (root / TARGET).write_text(revised)
                    if case == "changed imported constant":
                        helper.write_text("def offset := 2\n")
                    commit()
                    result = subprocess.run(
                        [sys.executable, SCRIPT, base],
                        cwd=root,
                        text=True,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,
                    )
                    self.assertEqual(
                        result.returncode == 0, case == "factored budget", result.stdout
                    )
                    self.assertIn(expected, result.stdout)
