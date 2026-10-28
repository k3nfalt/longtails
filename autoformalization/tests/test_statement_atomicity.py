"""Fault injection through the real submit_statement/transaction/save paths."""

import copy
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from autoformalize import engine
from autoformalize.common import WorkflowError, digest, write_json
from autoformalize.lean import repository_files
from autoformalize.project import MANIFEST, sync_index
from test_explicit_output_contract import temporary_workspace
from test_interface_enforcement import fixture


class StatementAtomicityTests(unittest.TestCase):
    def setup_run(self, directory):
        plan, graph, inventories = fixture()
        plan["units"].append(
            {
                "id": "Downstream",
                "file": "outputs/Proofs/Downstream.lean",
                "mode": "new",
                "declarations": ["outputs.Proofs.Downstream.proof"],
                "nodes": [],
                "clauses": [],
                "depends_on": ["Public"],
            }
        )
        run = engine.Run.__new__(engine.Run)
        run.root = Path(directory)
        project = run.root / "project"
        project.mkdir()
        for u in plan["units"]:
            p = project / u["file"]
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("-- original " + u["id"] + "\n", encoding="utf-8")
        dependency = b"-- pinned dependency\n"
        write_json(
            project / MANIFEST,
            {
                "repository_files": {
                    "LongTails/FaultDependency.lean": digest(dependency)
                }
            },
        )
        sync_index(project)
        run.compiler = SimpleNamespace(
            project=project,
            sync_index=lambda: sync_index(project),
            topology=lambda _: {},
            inspect=lambda *_: inventories["Public"],
            catalog=lambda _: {"status": "passed", "rows": []},
            source_style=lambda: sync_index(project),
            declaration_lint=lambda: None,
        )

        def build(**_):
            self.assertFalse((project / "outputs/Proofs/Downstream.lean").exists())
            self.assertEqual(
                (project / "outputs/Theorems/Public.lean").read_text(),
                "-- replacement\n",
            )
            sync_index(project)

        run.compiler.build = build
        run.state = {
            "schema": 1,
            "phase": "statements",
            "controller": engine.controller_version(),
            "target": "fixture",
            "source": run.put({"source": "fixture"}),
            "evidence": run.put({"s": "source evidence"}),
            "graph": run.put(graph),
            "plan": run.put(plan),
            "environment": {},
            "repository_commit": "fixture",
            "formalizer": "f",
            "reviewer": "r",
            "pending": None,
            "composition": None,
            "freeze": None,
            "final": None,
            "proofs": {},
            "units": {},
            "base_files": {
                p: digest((project / p).read_bytes())
                for p in [MANIFEST, "outputs.lean"]
            },
        }
        for u in plan["units"]:
            row = {
                "accepted": True,
                "review": run.put({"review": u["id"]}),
                "candidate": run.put(
                    {
                        "holes": [],
                        "providers": [],
                        "code": (project / u["file"]).read_text(),
                    }
                ),
                "inventory": run.put(
                    inventories.get(u["id"], {"declarations": [], "providers": []})
                ),
            }
            run.state["units"][u["id"]] = row
        run.save("fixture_created")
        run.verify(environment=False)
        submission = {
            "unit": "Public",
            "code": "-- replacement\n",
            "holes": [],
            "providers": [],
        }

        def materialize(*_):
            p = project / "LongTails/FaultDependency.lean"
            p.parent.mkdir(exist_ok=True)
            p.write_bytes(dependency)
            return {"LongTails/FaultDependency.lean": digest(dependency)}

        return run, submission, materialize

    def patches(self, stack, materialize):
        stack.enter_context(
            patch.object(engine, "materialize", side_effect=materialize)
        )
        for name in [
            "check_holes",
            "public_layout",
            "audit",
            "declaration_contract",
            "lint_public_budget",
        ]:
            stack.enter_context(patch.object(engine, name, return_value=None))
        stack.enter_context(
            patch.object(engine, "catalog_contract", return_value={"status": "passed"})
        )

    def assert_restored(self, run, state, raw_state, source_files):
        self.assertEqual(run.state, state)
        self.assertEqual((run.root / "state.json").read_bytes(), raw_state)
        self.assertEqual(repository_files(run.compiler.project), source_files)
        self.assertFalse((run.root / "transaction.json").exists())
        self.assertFalse(
            (run.compiler.project / "LongTails/FaultDependency.lean").exists()
        )
        run.verify(environment=False)

    def test_failure_after_deletion_and_late_packet_steps_restores_everything(self):
        for outer in [False, True]:
            for stage in [
                "source_style",
                "declaration_lint",
                "build",
                "interrupt",
                "inspect",
                "catalog",
                "topology",
                "design",
                "packet_size",
                "save",
            ]:
                with (
                    self.subTest(outer=outer, stage=stage),
                    temporary_workspace() as tmp,
                    ExitStack() as stack,
                ):
                    run, submission, materialize = self.setup_run(tmp)
                    self.patches(stack, materialize)
                    state = copy.deepcopy(run.state)
                    raw = (run.root / "state.json").read_bytes()
                    files = repository_files(run.compiler.project)
                    if stage in [
                        "source_style",
                        "declaration_lint",
                        "build",
                        "interrupt",
                        "inspect",
                        "catalog",
                        "topology",
                    ]:
                        method = "build" if stage == "interrupt" else stage
                        original = getattr(run.compiler, method)

                        def fail(*a, _original=original, **kw):
                            _original(*a, **kw)
                            if stage == "interrupt":
                                raise KeyboardInterrupt("injected interrupt")
                            raise WorkflowError("injected " + stage)

                        stack.enter_context(
                            patch.object(run.compiler, method, side_effect=fail)
                        )
                    elif stage == "design":
                        stack.enter_context(
                            patch(
                                "autoformalize.review_evidence.observed_design",
                                side_effect=WorkflowError("injected design failure"),
                            )
                        )
                    elif stage == "packet_size":
                        stack.enter_context(
                            patch("autoformalize.review_evidence.MAX_PACKET_BYTES", 1)
                        )
                    else:
                        original = engine.write_json
                        failed = []

                        def fail_save(path, *a, **kw):
                            if Path(path) == run.root / "state.json" and not failed:
                                failed.append(True)
                                raise OSError("injected state save failure")
                            return original(path, *a, **kw)

                        stack.enter_context(
                            patch.object(engine, "write_json", side_effect=fail_save)
                        )
                    with self.assertRaises((WorkflowError, OSError, KeyboardInterrupt)):
                        if outer:
                            with run.transaction():
                                run.submit_statement(submission)
                        else:
                            run.submit_statement(submission)
                    self.assert_restored(run, state, raw, files)

    def test_oversized_journal_fails_before_mutation(self):
        with temporary_workspace() as tmp:
            run, submission, _ = self.setup_run(tmp)
            state = copy.deepcopy(run.state)
            raw = (run.root / "state.json").read_bytes()
            files = repository_files(run.compiler.project)
            with patch.object(engine, "canonical", return_value="x" * 64_000_000):
                with self.assertRaisesRegex(WorkflowError, "Rollback journal exceeds"):
                    run.submit_statement(submission)
            self.assert_restored(run, state, raw, files)

    def test_success_saves_deleted_descendants_consistently(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            run, submission, materialize = self.setup_run(tmp)
            self.patches(stack, materialize)
            run.submit_statement(submission)
            self.assertFalse(
                (run.compiler.project / "outputs/Proofs/Downstream.lean").exists()
            )
            self.assertFalse(run.state["units"]["Downstream"]["accepted"])
            self.assertIsNotNone(run.state["pending"])
            self.assertFalse((run.root / "transaction.json").exists())
            run.verify(environment=False)

    def test_swallowed_inner_error_cannot_commit_partial_outer_transaction(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            run, submission, materialize = self.setup_run(tmp)
            self.patches(stack, materialize)
            state = copy.deepcopy(run.state)
            raw = (run.root / "state.json").read_bytes()
            files = repository_files(run.compiler.project)
            stack.enter_context(
                patch.object(
                    run.compiler, "build", side_effect=WorkflowError("compile failed")
                )
            )
            with self.assertRaisesRegex(WorkflowError, "aborted"):
                with run.transaction():
                    try:
                        run.submit_statement(submission)
                    except WorkflowError:
                        self.assert_restored(run, state, raw, files)
            self.assert_restored(run, state, raw, files)

    def test_interrupted_journal_recovery_restores_aggregate_and_descendant(self):
        import base64

        with temporary_workspace() as tmp:
            run, _, _ = self.setup_run(tmp)
            state = copy.deepcopy(run.state)
            files = {
                u["file"]: base64.b64encode(
                    (run.compiler.project / u["file"]).read_bytes()
                ).decode()
                for u in run.units()
            }
            files["outputs.lean"] = base64.b64encode(
                (run.compiler.project / "outputs.lean").read_bytes()
            ).decode()
            write_json(run.root / "transaction.json", {"state": state, "files": files})
            (run.compiler.project / "outputs/Proofs/Downstream.lean").unlink()
            (run.compiler.project / "outputs.lean").write_text("-- interrupted index\n")
            with self.assertRaisesRegex(WorkflowError, "Interrupted"):
                with run.transaction():
                    pass
            run.recover()
            run.verify(environment=False)


if __name__ == "__main__":
    unittest.main()
