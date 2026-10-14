import unittest
from types import SimpleNamespace
from unittest.mock import patch

from server.Theorems.create_theorem_description import ROOT, extract_theorems


class ExtractorTest(unittest.TestCase):
    def test_imports_precede_commands(self):
        with patch(
            "server.Theorems.create_theorem_description.subprocess.run",
            return_value=SimpleNamespace(returncode=0, stdout="[]"),
        ) as run:
            extract_theorems([ROOT / "LongTails/Theorems/AcceleratedConvex.lean"])
        program = run.call_args.kwargs["input"]
        seen_command = False
        for line in program.splitlines():
            if line.startswith("import "):
                self.assertFalse(seen_command, line)
            elif line.strip():
                seen_command = True
        self.assertIn("set_option format.width 120", program)


if __name__ == "__main__":
    unittest.main()
