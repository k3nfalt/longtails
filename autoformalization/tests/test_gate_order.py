"""Regression tests for stage ordering, freeze evidence and transactional repair."""

import copy
import unittest
from contextlib import ExitStack
from unittest.mock import patch

import test_statement_atomicity as atomicity
from autoformalize import engine
from autoformalize.common import WorkflowError, require
from autoformalize.lean import repository_files
from autoformalize.project import sync_index
from test_explicit_output_contract import temporary_workspace


class GateOrderTests(unittest.TestCase):
    def fixture(self, tmp, stack):
        helper = atomicity.StatementAtomicityTests()
        run, submission, materialize = helper.setup_run(tmp)
        helper.patches(stack, materialize)
        return helper, run, submission

    def trace(self, stack, obj, name, events):
        original = getattr(obj, name)

        def call(*args, **kwargs):
            events.append(name)
            return original(*args, **kwargs)

        stack.enter_context(patch.object(obj, name, side_effect=call))

    def test_statement_formats_and_structure_finish_before_review_packet(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            _, run, submission = self.fixture(tmp, stack)
            events = []
            for name in (
                "source_style",
                "build",
                "declaration_lint",
                "inspect",
                "catalog",
                "topology",
            ):
                self.trace(stack, run.compiler, name, events)
            for name in ("packet", "queue"):
                self.trace(stack, run, name, events)
            run.submit_statement(submission)
            self.assertEqual(
                events,
                [
                    "source_style",
                    "build",
                    "declaration_lint",
                    "inspect",
                    "catalog",
                    "topology",
                    "packet",
                    "queue",
                ],
            )
            packet = run.get(run.state["pending"]["packet"])
            self.assertEqual(
                packet["candidate"]["statement_checks"]["source_style"], "passed"
            )

    def test_trailing_space_stops_before_compiler_or_reviewer_and_restores_files(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            helper, run, submission = self.fixture(tmp, stack)
            state = copy.deepcopy(run.state)
            raw = (run.root / "state.json").read_bytes()
            files = repository_files(run.compiler.project)
            submission["code"] = "-- candidate \n"

            def native_style_failure():
                sync_index(run.compiler.project)
                code = (run.compiler.project / run.unit("Public")["file"]).read_text()
                require(
                    not any(line.endswith(" ") for line in code.splitlines()),
                    "native trailing whitespace",
                )

            stack.enter_context(
                patch.object(
                    run.compiler, "source_style", side_effect=native_style_failure
                )
            )
            build = stack.enter_context(patch.object(run.compiler, "build"))
            packet = stack.enter_context(patch.object(run, "packet"))
            with self.assertRaisesRegex(WorkflowError, "trailing whitespace"):
                run.submit_statement(submission)
            build.assert_not_called()
            packet.assert_not_called()
            helper.assert_restored(run, state, raw, files)

    def test_budget_syntax_failure_precedes_compilation_and_review(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            _, run, submission = self.fixture(tmp, stack)
            stack.enter_context(
                patch.object(
                    engine,
                    "lint_public_budget",
                    side_effect=WorkflowError("bad budget"),
                )
            )
            build = stack.enter_context(patch.object(run.compiler, "build"))
            packet = stack.enter_context(patch.object(run, "packet"))
            with self.assertRaisesRegex(WorkflowError, "bad budget"):
                run.submit_statement(submission)
            build.assert_not_called()
            packet.assert_not_called()

    def test_compiled_format_failures_never_queue_semantic_review(self):
        for stage in ("declaration_lint", "catalog", "topology"):
            with (
                self.subTest(stage=stage),
                temporary_workspace() as tmp,
                ExitStack() as stack,
            ):
                _, run, submission = self.fixture(tmp, stack)
                stack.enter_context(
                    patch.object(run.compiler, stage, side_effect=WorkflowError(stage))
                )
                queue = stack.enter_context(patch.object(run, "queue"))
                with self.assertRaisesRegex(WorkflowError, stage):
                    run.submit_statement(submission)
                queue.assert_not_called()
                self.assertIsNone(run.state["pending"])
                run.verify(environment=False)

    def composition_fixture(self, tmp, stack):
        helper, run, _ = self.fixture(tmp, stack)
        inventory = {"declarations": [], "providers": []}
        for row in run.state["units"].values():
            inv = run.get(row["inventory"])
            for decl in inv["declarations"]:
                decl["type_repr"] = decl["type_text"]
            row["inventory"] = run.put(inv)
            inventory["declarations"].extend(inv["declarations"])
        stack.enter_context(
            patch.object(run.compiler, "inspect", return_value=inventory)
        )
        stack.enter_context(
            patch.object(
                run.compiler,
                "build",
                side_effect=lambda **_: sync_index(run.compiler.project),
            )
        )
        stack.enter_context(
            patch.object(engine, "validate_graph", return_value={"clauses": []})
        )
        stack.enter_context(patch.object(engine, "validate_plan"))
        stack.enter_context(patch.object(engine, "graph_checks", return_value=[]))
        stack.enter_context(patch.object(run, "check_public_designs"))
        return helper, run, inventory

    def accept_composition(self, run):
        packet_key = run.state["pending"]["packet"]
        packet = run.get(packet_key)
        review = run.put({"basis": packet["basis"]})
        # Test fixture represents an independently accepted composition verdict.
        run.state.update(
            composition=review,
            phase="ready_to_freeze",
            pending=None,
            last_review={"packet": packet_key, "review": review, "accepted": True},
        )
        run.save("fixture_composition_accepted")

    def test_composition_gates_bind_receipt_before_review_and_freeze(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            _, run, _ = self.composition_fixture(tmp, stack)
            events = []
            for name in (
                "source_style",
                "build",
                "declaration_lint",
                "topology",
                "catalog",
            ):
                self.trace(stack, run.compiler, name, events)
            self.trace(stack, run, "queue", events)
            run.compose()
            self.assertEqual(
                events,
                [
                    "source_style",
                    "build",
                    "declaration_lint",
                    "catalog",
                    "topology",
                    "queue",
                ],
            )
            receipt = run.get(run.state["statement_validation"])
            self.assertEqual(receipt["checks"], engine.STATEMENT_GATE_ORDER)
            self.accept_composition(run)
            run.freeze()
            frozen = run.get(run.state["freeze"])
            self.assertEqual(
                frozen["statement_validation"], run.state["statement_validation"]
            )
            self.assertEqual(run.state["phase"], "proofs")
            run.verify(environment=False)

    def test_missing_stale_incomplete_or_unreviewed_receipt_blocks_freeze(self):
        for defect in ("missing", "source", "plan", "checks", "review"):
            with (
                self.subTest(defect=defect),
                temporary_workspace() as tmp,
                ExitStack() as stack,
            ):
                _, run, _ = self.composition_fixture(tmp, stack)
                run.compose()
                self.accept_composition(run)
                receipt = run.get(run.state["statement_validation"])
                if defect == "missing":
                    run.state.pop("statement_validation")
                elif defect == "source":
                    (run.compiler.project / run.unit("Public")["file"]).write_text(
                        "-- changed\n"
                    )
                elif defect == "review":
                    run.state["composition"] = run.put({"basis": "unrelated"})
                else:
                    if defect == "plan":
                        receipt["plan"] = "other"
                    if defect == "checks":
                        receipt["checks"] = receipt["checks"][:-1]
                    run.state["statement_validation"] = run.put(receipt)
                with self.assertRaises(WorkflowError):
                    run.freeze()
                self.assertIsNone(run.state["freeze"])

    def test_composition_failure_rolls_back_without_review_or_receipt(self):
        for stage in ("source_style", "declaration_lint", "catalog", "topology"):
            with (
                self.subTest(stage=stage),
                temporary_workspace() as tmp,
                ExitStack() as stack,
            ):
                helper, run, _ = self.composition_fixture(tmp, stack)
                run.save("fixture_ready")
                state = copy.deepcopy(run.state)
                raw = (run.root / "state.json").read_bytes()
                files = repository_files(run.compiler.project)
                stack.enter_context(
                    patch.object(run.compiler, stage, side_effect=WorkflowError(stage))
                )
                queue = stack.enter_context(patch.object(run, "queue"))
                with self.assertRaises(WorkflowError):
                    run.compose()
                queue.assert_not_called()
                helper.assert_restored(run, state, raw, files)

    def test_reopen_regenerates_index_and_clears_validation_preserving_unrelated_work(
        self,
    ):
        with temporary_workspace() as tmp, ExitStack() as stack:
            _, run, _ = self.fixture(tmp, stack)
            run.state["statement_validation"] = run.put({"status": "old"})
            untouched = (run.compiler.project / run.unit("Alg")["file"]).read_bytes()
            run.reopen("Public", "format repair")
            self.assertNotIn("statement_validation", run.state)
            self.assertFalse(
                (run.compiler.project / run.unit("Downstream")["file"]).exists()
            )
            self.assertEqual(
                (run.compiler.project / run.unit("Alg")["file"]).read_bytes(), untouched
            )
            sync_index(run.compiler.project, check=True)
            run.verify(environment=False)

    def test_reopen_and_graph_restart_failures_restore_index_state_and_descendants(
        self,
    ):
        for action in ("reopen", "restart_graph"):
            for stage in ("index", "save"):
                with (
                    self.subTest(action=action, stage=stage),
                    temporary_workspace() as tmp,
                    ExitStack() as stack,
                ):
                    helper, run, _ = self.fixture(tmp, stack)
                    state = copy.deepcopy(run.state)
                    raw = (run.root / "state.json").read_bytes()
                    files = repository_files(run.compiler.project)
                    obj, name = (
                        (run.compiler, "sync_index")
                        if stage == "index"
                        else (run, "save")
                    )
                    stack.enter_context(
                        patch.object(obj, name, side_effect=WorkflowError(stage))
                    )
                    with self.assertRaises(WorkflowError):
                        if action == "reopen":
                            run.reopen("Public", "repair")
                        else:
                            run.restart_graph("repair")
                    helper.assert_restored(run, state, raw, files)

    def test_graph_restart_saves_consistent_empty_index(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            _, run, _ = self.fixture(tmp, stack)
            run.restart_graph("revised source graph")
            self.assertEqual((run.compiler.project / "outputs.lean").read_text(), "")
            run.verify(environment=False)

    def test_finish_reuses_statement_evidence_only_after_preservation_checks(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            _, run, _ = self.composition_fixture(tmp, stack)
            run.compose()
            self.accept_composition(run)
            run.freeze()
            for name in ("catalog", "topology"):
                stack.enter_context(
                    patch.object(
                        run.compiler,
                        name,
                        side_effect=AssertionError("late statement check"),
                    )
                )
            stack.enter_context(
                patch.object(
                    run.compiler,
                    "environment",
                    return_value=run.state["environment"],
                    create=True,
                )
            )
            stack.enter_context(patch.object(engine, "check_proof_signature"))
            result = run.finish()
            self.assertEqual(result["status"], "proved")
            self.assertEqual(
                result["statement_validation"], run.state["statement_validation"]
            )
            run.verify(environment=False)

    def test_proof_format_error_keeps_freeze_and_rolls_back_without_reopening(self):
        with temporary_workspace() as tmp, ExitStack() as stack:
            helper, run, _ = self.fixture(tmp, stack)
            unit = run.unit("Public")
            name = unit["declarations"][0]
            code = "theorem result : True := by sorry\n"
            hole = {
                "declaration": name,
                "start": code.index("by sorry"),
                "end": len(code) - 1,
            }
            (run.compiler.project / unit["file"]).write_text(code)
            run.state["units"]["Public"]["candidate"] = run.put(
                {"code": code, "holes": [hole], "providers": []}
            )
            run.state.update(phase="proofs", freeze=run.put({"signature": {}}))
            run.save("fixture_frozen")
            state = copy.deepcopy(run.state)
            raw = (run.root / "state.json").read_bytes()
            files = repository_files(run.compiler.project)
            stack.enter_context(patch.object(run.compiler, "parse_proof", create=True))
            stack.enter_context(
                patch.object(
                    run.compiler,
                    "source_style",
                    side_effect=WorkflowError("proof whitespace"),
                )
            )
            build = stack.enter_context(patch.object(run.compiler, "build"))
            with self.assertRaisesRegex(WorkflowError, "proof whitespace"):
                run.prove(name, "by\n  trivial ")
            build.assert_not_called()
            helper.assert_restored(run, state, raw, files)

    def test_final_statement_drift_and_missing_receipt_fail_before_expensive_proof_checks(
        self,
    ):
        for defect in ("source", "receipt"):
            with (
                self.subTest(defect=defect),
                temporary_workspace() as tmp,
                ExitStack() as stack,
            ):
                _, run, _ = self.composition_fixture(tmp, stack)
                run.compose()
                self.accept_composition(run)
                run.freeze()
                if defect == "source":
                    (run.compiler.project / run.unit("Public")["file"]).write_text(
                        "-- changed statement\n"
                    )
                else:
                    frozen = run.get(run.state["freeze"])
                    frozen.pop("statement_validation")
                    run.state["freeze"] = run.put(frozen)
                build = stack.enter_context(patch.object(run.compiler, "build"))
                with self.assertRaises(WorkflowError):
                    run.finish()
                build.assert_not_called()

    def test_style_gate_runs_before_candidate_build_in_compiler_interface(self):
        # source_style may build the linter executable but must not build outputs.
        from pathlib import Path

        from autoformalize.lean import Compiler

        with temporary_workspace() as tmp:
            project = Path(tmp) / "project"
            project.mkdir()
            source = project / ".lake/packages/mathlib/scripts/lint-style.lean"
            source.parent.mkdir(parents=True)
            source.write_text("modulesNotUpperCamelCase opts allModuleNames")
            compiler = Compiler(project, Path(tmp) / "artifacts")
            with patch.object(compiler, "run", return_value="") as execute:
                compiler.source_style()
                self.assertEqual(
                    execute.call_args.args[0], ["lake", "exe", "runOutputStyle"]
                )
                self.assertEqual(execute.call_count, 1)


if __name__ == "__main__":
    unittest.main()
