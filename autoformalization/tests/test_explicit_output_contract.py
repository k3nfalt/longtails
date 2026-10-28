"""Regression checks for self-contained packets and non-waivable output review."""

import copy
import sys
import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from autoformalize import engine  # noqa: E402
from autoformalize.common import WorkflowError  # noqa: E402
from autoformalize.contracts import validate_review  # noqa: E402
from autoformalize.interface_contract import BEGIN, END, validate_template_contract  # noqa: E402
from autoformalize.output_contract import output_checks  # noqa: E402


@contextmanager
def temporary_workspace():
    parent = (ROOT / "tests").resolve()
    work = tempfile.TemporaryDirectory(dir=parent, prefix="contract-test-")
    target = Path(work.name).resolve()
    if target.parent != parent:
        raise RuntimeError("Temporary test directory escaped its workspace")
    try:
        yield str(target)
    finally:
        work.cleanup()


class ExplicitOutputContractTests(unittest.TestCase):
    def setUp(self):
        self.contract = (ROOT / "OUTPUT_CONTRACT.md").read_text(encoding="utf-8")
        self.template = self.contract.split(BEGIN, 1)[1].split(END, 1)[0]

    def test_exact_template_and_line_endings(self):
        validate_template_contract(self.contract, self.template + "\n")
        validate_template_contract(self.contract.replace("\n", "\r\n"), self.template)

    def test_interface_drift_is_rejected(self):
        with self.assertRaisesRegex(WorkflowError, "differs"):
            validate_template_contract(
                self.contract,
                self.template.replace("numOracles : ℕ := 1", "numOracles : ℕ := 2", 1),
            )

    def test_missing_or_duplicate_template_is_rejected(self):
        for text in ("No embedded API", self.contract + "\n" + self.contract):
            with self.assertRaisesRegex(WorkflowError, "exactly one"):
                validate_template_contract(text, self.template)

    def test_policy_is_fingerprinted(self):
        self.assertIn("OUTPUT_CONTRACT.md", engine.policy_documents())
        before = engine.controller_version()
        with temporary_workspace() as tmp:
            p = Path(tmp) / "contract.md"
            p.write_text(self.contract + "\nChanged policy.\n", encoding="utf-8")
            documents = engine.policy_documents()
            documents["OUTPUT_CONTRACT.md"] = p
            with patch.object(engine, "policy_documents", return_value=documents):
                self.assertNotEqual(before, engine.controller_version())

    def packet_run(self, project, pending=None):
        for relative, text in {
            "AGENTS.md": "Run-local instructions only.",
            "LongTails/Template.lean": self.template,
            "server/Theorems/BudgetLatex.lean": "-- renderer fixture\n",
        }.items():
            p = project / relative
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text, encoding="utf-8")
        run = engine.Run.__new__(engine.Run)
        run.root = project
        run.compiler = SimpleNamespace(project=project)
        run.state = {
            "phase": "graph",
            "target": "source target",
            "last_review": None,
            "repository": "/read-only/source",
            "repository_commit": "revision",
            "pending": pending,
            "source": "source",
            "evidence": "evidence",
            "formalizer": "formalizer",
            "reviewer": "reviewer",
            "graph": None,
        }
        run.get = lambda key: {"fixture": key}
        return run

    def test_both_roles_receive_complete_contract_and_actual_api(self):
        for pending, role in [
            (None, "FORMALIZER.md"),
            ({"packet": "review"}, "REVIEWER.md"),
        ]:
            with self.subTest(role=role), temporary_workspace() as tmp:
                packet = self.packet_run(Path(tmp), pending).next()
                self.assertEqual(packet["policy"]["OUTPUT_CONTRACT.md"], self.contract)
                self.assertIn(role, packet["policy"])
                self.assertEqual(
                    packet["repository_interfaces"]["LongTails/Template.lean"],
                    self.template,
                )

    def test_packet_blocks_interface_drift(self):
        with temporary_workspace() as tmp:
            run = self.packet_run(Path(tmp))
            (Path(tmp) / "LongTails/Template.lean").write_text(
                self.template + "\n-- changed\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(WorkflowError, "differs"):
                run.next()

    def test_checks_are_generated_per_public_result_and_unit(self):
        plan = {
            "output_contract": {
                "public_results": [
                    {"node": "T1", "unit": "public1", "setup_unit": "setup"},
                    {"node": "T2", "unit": "public2", "setup_unit": "setup"},
                ],
                "setups": [{"unit": "setup", "results": ["T1", "T2"]}],
            }
        }
        for prefix in [
            "parameter_roles",
            "accuracy_contract",
            "explicit_budget",
            "source_adaptation",
        ]:
            self.assertIn(f"output:{prefix}:T1", output_checks(plan))
            self.assertIn(f"output:{prefix}:T2", output_checks(plan))
            self.assertIn(f"output:{prefix}:T1", output_checks(plan, "public1"))
            self.assertNotIn(f"output:{prefix}:T2", output_checks(plan, "public1"))

    def test_new_checks_cannot_be_missing_waived_or_failed(self):
        ids = [
            f"output:{name}:T1"
            for name in [
                "parameter_roles",
                "accuracy_contract",
                "explicit_budget",
                "source_adaptation",
            ]
        ]
        packet = {
            "basis": "basis",
            "required_checks": ids,
            "source_ids": ["source"],
            "candidate_ids": ["candidate"],
        }
        review = {
            "basis": "basis",
            "reviewer": "reviewer",
            "checks": [
                {
                    "id": key,
                    "verdict": "match",
                    "source": ["source"],
                    "candidate": ["candidate"],
                    "comparison": "Concrete fixture evidence.",
                }
                for key in ids
            ],
            "blockers": [],
            "notes": [],
        }
        self.assertTrue(validate_review(review, packet, "reviewer"))
        missing = copy.deepcopy(review)
        missing["checks"].pop()
        with self.assertRaisesRegex(WorkflowError, "every required"):
            validate_review(missing, packet, "reviewer")
        for key in ids:
            for verdict in ["not_applicable", "mismatch", "unresolved"]:
                with self.subTest(key=key, verdict=verdict):
                    changed = copy.deepcopy(review)
                    next(c for c in changed["checks"] if c["id"] == key)["verdict"] = (
                        verdict
                    )
                    if verdict == "not_applicable":
                        with self.assertRaisesRegex(
                            WorkflowError, "cannot be inapplicable"
                        ):
                            validate_review(changed, packet, "reviewer")
                    else:
                        self.assertFalse(validate_review(changed, packet, "reviewer"))


if __name__ == "__main__":
    unittest.main()
