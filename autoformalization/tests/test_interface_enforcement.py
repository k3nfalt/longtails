"""Negative tests for the five interface gaps and bounded evidence packets."""

import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from autoformalize.common import WorkflowError  # noqa: E402
from autoformalize.contracts import validate_plan, validate_review  # noqa: E402
from autoformalize.engine import Run, evidence_pointers  # noqa: E402
from autoformalize.output_contract import lint_budget_expression, lint_public_budget  # noqa: E402
from autoformalize.public_design import observed_design  # noqa: E402
from autoformalize.review_evidence import (  # noqa: E402
    attach_interface_evidence,
    bounded_packet,
    compact_candidate,
    packet_bytes,
    required_interface_citations,
)
from test_explicit_output_contract import temporary_workspace  # noqa: E402


def fixture():
    def unit(uid, node, cat, decls, deps):
        return {
            "id": uid,
            "nodes": [node],
            "file": f"outputs/{cat}/{uid}.lean",
            "declarations": decls,
            "node_declarations": {node: [decls[0]]},
            "clauses": [node + "/c"],
            "depends_on": deps,
            "mode": "new",
            "detail": {
                "construction": "Concrete fixture.",
                "reuse_decisions": [],
                "edge_cases": [],
                "retrieval": [],
            },
        }

    a = "outputs.Algorithms.Alg"
    s = "outputs.Setups.Setup"
    p = "outputs.Proofs.Proof"
    t = "outputs.Theorems.Public"
    units = [
        unit(
            "Alg",
            "A",
            "Algorithms",
            [a + ".algorithm", a + ".selector", a + ".horizon"],
            [],
        ),
        unit("Setup", "S", "Setups", [s + ".spec", s + ".Params"], ["Alg"]),
        unit("Proof", "P", "Proofs", [p + ".bound"], ["Setup", "Alg"]),
        unit(
            "Public",
            "T",
            "Theorems",
            [t + ".result", t + ".budget"],
            ["Setup", "Proof"],
        ),
    ]
    graph = {
        "nodes": [
            {
                "id": n,
                "role": r,
                "clauses": [{"id": "c"}],
                **(
                    {
                        "result_context": {
                            "setups": ["S"],
                            "hypotheses": ["S/c"],
                            "parameters": ["S/L", "S/ε"],
                        }
                    }
                    if n == "T"
                    else {}
                ),
            }
            for n, r in [
                ("A", "algorithm"),
                ("S", "setup"),
                ("P", "lemma"),
                ("T", "target"),
            ]
        ],
        "edges": [],
        "inventory": {"convergence_results": ["T"]},
    }
    expr = "⌈4 * p.L / p.ε ^ 2⌉₊ + 1"
    proof = [p + ".bound"]
    design = {
        "params": s + ".Params",
        "parameters": [
            {
                "field": "L",
                "role": "problem_data",
                "public": True,
                "justification": "Known bound",
            },
            {
                "field": "ε",
                "role": "accuracy",
                "public": True,
                "justification": "Target",
            },
        ],
        "tuning": [
            {
                "name": "K",
                "declaration": a + ".horizon",
                "expression": expr,
                "uses": ["L", "ε"],
                "proofs": proof,
            }
        ],
        "output": {
            "kind": "random",
            "algorithm": a + ".algorithm",
            "selector": a + ".selector",
            "criterion": "error output ≤ p.ε",
            "probability_mode": "expectation",
            "proofs": proof,
        },
        "budget": {
            "expression": "fun p _ => " + expr,
            "num_oracles": 1,
            "components": [
                {
                    "oracle": 0,
                    "expression": expr,
                    "uses": ["L", "ε"],
                    "accuracy_independent_reason": "",
                    "proofs": proof,
                }
            ],
            "boundary_cases": [
                {"case": "rounding", "reason": "Ceiling suffices", "proofs": proof}
            ],
        },
        "adaptation": {
            "kind": "derived",
            "source_nodes": ["T"],
            "reason": "Apply source bound",
            "proofs": proof,
            "approval": None,
        },
    }
    e = {
        "node": "T",
        "unit": "Public",
        "result": t + ".result",
        "budget": t + ".budget",
        "setup_unit": "Setup",
        "spec": s + ".spec",
        "design": design,
        "cost": {
            "headline": {
                "expression": expr,
                "unit": "template_oracle_calls",
                "domain": "Fin spec.numOracles → Nat",
            },
            "execution": {
                "expression": expr,
                "unit": "template_oracle_calls",
                "domain": "Fin spec.numOracles → Nat",
            },
            "relationship": {
                "kind": "identity",
                "explanation": "Same calls",
                "proofs": proof,
            },
        },
    }
    plan = {
        "units": units,
        "adaptation": {
            k: "Source-preserving fixture"
            for k in [
                "public_information",
                "algorithm_identity",
                "output",
                "cost",
                "probability",
                "source_correspondence",
            ]
        },
        "deferred_obligations": [],
        "output_contract": {
            "schema_version": 3,
            "public_results": [e],
            "setups": [
                {
                    "unit": "Setup",
                    "results": ["T"],
                    "shared_hypotheses": ["S/c"],
                    "shared_parameters": ["S/L", "S/ε"],
                    "compatibility": [
                        {
                            "result": "T",
                            "mode": "identical",
                            "justification": "Same setup",
                            "proofs": [],
                        }
                    ],
                }
            ],
            "counts": {"convergence_results": 1, "public_modules": 1, "setups": 1},
        },
    }
    inventories = {}
    for u in units:
        rows = []
        for n in u["declarations"]:
            r = {
                "name": n,
                "module": u["file"][:-5].replace("/", "."),
                "kind": "theorem"
                if n.endswith((".bound", ".result"))
                else "definition",
                "type_text": "FixtureType",
                "value_repr": "FixtureBody",
                "type_tree": {},
                "used": [],
            }
            if n.endswith(".Params"):
                r.update(kind="inductive", structure_fields=["L", "ε"])
            if n.endswith(".spec"):
                r["used"] = [s + ".Params"]
            rows.append(r)
        inventories[u["id"]] = {
            "declarations": rows,
            "providers": [],
            "unexpanded_dependencies": [],
        }
    return plan, graph, inventories


class EnforcementTests(unittest.TestCase):
    def test_positive_plan_and_observed_design(self):
        plan, graph, invs = fixture()
        validate_plan(plan, graph)
        observed_design(
            plan["output_contract"]["public_results"][0],
            {"declarations": [r for i in invs.values() for r in i["declarations"]]},
        )

    def test_free_counts_helpers_and_disguises_rejected(self):
        for body in [
            "p.K",
            "p.T * p.B",
            "p.calls",
            "p.renamed",
            "(p.foo) * (p.bar)",
            "p.k + 1",
            "2 * p.N",
            "⌈p.N⌉₊",
            "Nat.ceil (2 * p.N + 1)",
            "p.K + 0 * p.ε",
            "horizon p",
            "p./- nested /- comment -/ -/K",
        ]:
            with self.subTest(body=body), self.assertRaises(WorkflowError):
                lint_public_budget(
                    "noncomputable def budget : Params → Fin 1 → ℕ := fun p _ => "
                    + body
                )

    def test_actual_kurtosis_constant_named_K_is_not_a_free_count(self):
        source = (ROOT / "tests/fixtures/KappaFreeSgdPLHessian.lean").read_text(
            encoding="utf-8"
        )
        lint_public_budget(source)
        lint_public_budget(
            source.replace("fun q _ =>", "fun data _ =>").replace("q.", "data.")
        )

    def test_problem_or_family_role_alone_does_not_authorize_a_count(self):
        for role in ["problem_data", "family_setting"]:
            for expression in ["p.k + 1", "2 * p.N", "⌈p.N⌉₊"]:
                with (
                    self.subTest(role=role, expression=expression),
                    self.assertRaises(WorkflowError),
                ):
                    lint_budget_expression(
                        expression,
                        {"accuracy_independent_reason": ""},
                        {"k": role, "N": role, "ε": "accuracy"},
                    )

    def test_mislabeled_accuracy_must_appear_in_success_criterion(self):
        plan, graph, _ = fixture()
        design = plan["output_contract"]["public_results"][0]["design"]
        design["parameters"][0]["role"] = "accuracy"
        with self.assertRaisesRegex(WorkflowError, "success criterion"):
            validate_plan(plan, graph)

    def test_formula_and_justified_dimension_cost(self):
        lint_budget_expression("fun p _ => ⌈4 * p.L / p.ε ^ 2⌉₊ + 1")
        lint_budget_expression(
            "p.n * p.m",
            {"accuracy_independent_reason": "Exact n by m enumeration"},
            {"n": "problem_data", "m": "problem_data"},
        )
        with self.assertRaises(WorkflowError):
            lint_budget_expression(
                "p.n * p.m",
                {"accuracy_independent_reason": ""},
                {"n": "problem_data", "m": "problem_data"},
            )

    def test_comment_cannot_supply_a_fake_budget(self):
        with self.assertRaises(WorkflowError):
            lint_public_budget("-- noncomputable def budget : P := fun p _ => p.n + 1")

    def test_plan_missing_version_design_or_required_structure_rejected(self):
        for edit in [
            lambda p: p["output_contract"].pop("schema_version"),
            lambda p: p["output_contract"]["public_results"][0].pop("design"),
            lambda p: p["output_contract"]["public_results"][0]["design"].update(
                parameters=[]
            ),
            lambda p: p["output_contract"]["public_results"][0]["design"][
                "budget"
            ].update(boundary_cases=[]),
            lambda p: p["output_contract"]["public_results"][0]["design"][
                "adaptation"
            ].update(proofs=[]),
            lambda p: p["output_contract"]["public_results"][0]["design"][
                "output"
            ].update(algorithm="unknown"),
        ]:
            plan, graph, _ = fixture()
            edit(plan)
            with self.assertRaises(WorkflowError):
                validate_plan(plan, graph)

    def test_false_roles_hidden_tuning_and_incomplete_uses_rejected(self):
        for edit in [
            lambda d: d["parameters"][0].update(role="derived_tuning"),
            lambda d: d["parameters"][0].update(role="execution_count"),
            lambda d: d["parameters"][0].update(public=False),
            lambda d: d["tuning"][0].update(uses=["L"]),
            lambda d: d["tuning"][0].update(proofs=["unknown"]),
        ]:
            plan, graph, _ = fixture()
            edit(plan["output_contract"]["public_results"][0]["design"])
            with self.assertRaises(WorkflowError):
                validate_plan(plan, graph)

    def test_generic_old_text_cannot_replace_structured_design(self):
        plan, graph, _ = fixture()
        plan["output_contract"]["public_results"][0]["design"] = {
            "construction": "Implement the source."
        }
        with self.assertRaises(WorkflowError):
            validate_plan(plan, graph)

    def test_missing_parameter_and_fake_proof_rejected_against_compiler(self):
        for mode in ["missing_field", "not_theorem", "missing_decl"]:
            plan, _, invs = fixture()
            rows = [r for inv in invs.values() for r in inv["declarations"]]
            if mode == "missing_field":
                next(r for r in rows if r["name"].endswith(".Params"))[
                    "structure_fields"
                ].append("T")
            if mode == "not_theorem":
                next(r for r in rows if r["name"].endswith(".bound"))["kind"] = (
                    "definition"
                )
            if mode == "missing_decl":
                rows = [r for r in rows if not r["name"].endswith(".selector")]
            with self.subTest(mode=mode), self.assertRaises(WorkflowError):
                observed_design(
                    plan["output_contract"]["public_results"][0], {"declarations": rows}
                )

    def test_actual_budget_cannot_differ_from_plan(self):
        plan, _, _ = fixture()
        e = plan["output_contract"]["public_results"][0]
        with self.assertRaises(WorkflowError):
            lint_public_budget("noncomputable def budget : P := fun p _ => p.L + 1", e)

    def test_multiple_oracles_complete_and_independent_reason_required(self):
        plan, graph, _ = fixture()
        b = plan["output_contract"]["public_results"][0]["design"]["budget"]
        b["num_oracles"] = 2
        with self.assertRaises(WorkflowError):
            validate_plan(plan, graph)
        b["components"].append(
            {
                "oracle": 1,
                "expression": "1",
                "uses": [],
                "accuracy_independent_reason": "",
                "proofs": ["outputs.Proofs.Proof.bound"],
            }
        )
        with self.assertRaises(WorkflowError):
            validate_plan(plan, graph)
        b["components"][1]["accuracy_independent_reason"] = "One initialization call"
        b["expression"] = (
            "fun p i => if i.val = 0 then "
            + b["components"][0]["expression"]
            + " else 1"
        )
        validate_plan(plan, graph)

    def test_policies_explicit_and_noncontradictory(self):
        contract = (ROOT / "OUTPUT_CONTRACT.md").read_text(encoding="utf-8")
        agents = (ROOT / "AGENTS.md").read_text(encoding="utf-8")
        self.assertNotIn(
            "Prop-valued assumption/success definitions are permitted", agents
        )
        self.assertNotIn("or\n  derived tuning", contract)
        for rule in [
            "letI : MeasureSpace",
            "sampleMean",
            "repository_instructions",
            "`η`, `Δ`, and `K`",
            "IsMinOn f Set.univ p.xstar",
        ]:
            self.assertIn(rule, contract)
        for copied in [
            "structure IID",
            "structure Oracle",
            "import outputs.Algorithms",
        ]:
            self.assertNotIn(copied, contract)
        self.assertNotIn("∃ xstar, IsMinOn", contract)
        protocol = (ROOT / "PROTOCOL.md").read_text(encoding="utf-8")
        self.assertIn('"schema_version": 3', protocol)
        self.assertIn('"design": {', protocol)

    def make_run(self, path, inventories):
        run = Run.__new__(Run)
        run.root = path
        run.compiler = SimpleNamespace(project=path / "project")
        run.state = {"units": {}}
        for uid, inv in inventories.items():
            run.state["units"][uid] = {"inventory": run.put(inv)}
        return run

    def test_indirect_algorithm_source_and_full_records_in_evidence(self):
        plan, _, invs = fixture()
        with temporary_workspace() as tmp:
            run = self.make_run(Path(tmp), invs)
            for u in plan["units"]:
                path = run.compiler.project / u["file"]
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("def hiddenOutput := 42\n")
            c = {"unit": plan["units"][-1], "plan": plan, "inventory": invs["Public"]}
            c = attach_interface_evidence(run, c)
            self.assertIn("Alg", c["interface_evidence"]["sources"])
            c = compact_candidate(run, c)
            name = "outputs.Algorithms.Alg.selector"
            entry = c["declaration_evidence"][name]["preferred"]
            self.assertEqual(run.get(entry["artifact"])["value_repr"], "FixtureBody")
            self.assertIn(
                "hiddenOutput", c["interface_evidence"]["sources"]["Alg"]["source"]
            )
            self.assertLess(packet_bytes(c), 64_000_000)

    def test_large_duplicate_inventories_are_referenced_once_and_recoverable(self):
        # Three repeated 22 MB compiler inventories used to exceed the 64 MB limit.
        record = {
            "name": "outputs.Algorithms.A.step",
            "module": "outputs.Algorithms.A",
            "kind": "definition",
            "value_repr": "x" * 22_000_000,
            "type_tree": {},
        }
        inv = {"declarations": [record], "providers": []}
        with temporary_workspace() as tmp:
            run = self.make_run(Path(tmp), {})
            c = compact_candidate(
                run, {"inventory": inv, "accepted_prerequisites": {"a": inv, "b": inv}}
            )
            bounded_packet(c)
            self.assertLess(packet_bytes(c), 100_000)
            refs = c["declaration_evidence"][record["name"]]["records"]
            self.assertEqual(len(refs), 1)
            self.assertEqual(run.get(refs[0]["artifact"]), record)

    def test_size_guard_counts_utf8_and_full_envelope(self):
        p = {"packet": {"x": "ε" * 20}, "policy": {"rule": "x" * 50}}
        with patch("autoformalize.review_evidence.MAX_PACKET_BYTES", packet_bytes(p)):
            with self.assertRaises(WorkflowError):
                bounded_packet(p)
        with patch(
            "autoformalize.review_evidence.MAX_PACKET_BYTES", packet_bytes(p) + 1
        ):
            bounded_packet(p)

    def test_matching_review_requires_implementation_pointer(self):
        candidate = {"interface_evidence": {"results": {"T": {"design": "fixture"}}}}
        required = required_interface_citations(candidate)
        packet = {
            "basis": "b",
            "required_checks": list(required),
            "source_ids": ["s"],
            "candidate_ids": evidence_pointers(candidate),
            "required_candidate_evidence": required,
        }
        review = {
            "basis": "b",
            "reviewer": "r",
            "checks": [
                {
                    "id": k,
                    "verdict": "match",
                    "source": ["s"],
                    "candidate": ["candidate"],
                    "comparison": "Evidence",
                }
                for k in required
            ],
            "blockers": [],
            "notes": [],
        }
        with self.assertRaises(WorkflowError):
            validate_review(review, packet, "r")
        for c in review["checks"]:
            c["candidate"] = [required[c["id"]]]
        self.assertTrue(validate_review(review, packet, "r"))

    def test_real_packet_builder_and_next_envelope_with_indirect_evidence(self):
        from autoformalize.engine import controller_version

        plan, graph, invs = fixture()
        with temporary_workspace() as tmp:
            run = self.make_run(Path(tmp), invs)
            for u in plan["units"]:
                path = run.compiler.project / u["file"]
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("def sourceWitness := 0\n")
            template = (ROOT.parent / "LongTails/Template.lean").read_text(
                encoding="utf-8"
            )
            for relative, body in {
                "AGENTS.md": "Run guidance",
                "REPOSITORY_AGENTS.md": "Repository guidance",
                "LongTails/Template.lean": template,
                "server/Theorems/BudgetLatex.lean": "-- fixture",
            }.items():
                p = run.compiler.project / relative
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(body, encoding="utf-8")
            run.state.update(
                phase="statements",
                target="test",
                source=run.put({"source": "fixture"}),
                evidence=run.put({"s": "source evidence"}),
                graph=run.put(graph),
                plan=run.put(plan),
                reviewer="reviewer",
                formalizer="formalizer",
                repository=str(Path(tmp)),
                repository_commit="test",
                environment={},
                base_files={},
                controller=controller_version(),
                last_review=None,
                pending=None,
            )
            c = {"unit": plan["units"][-1], "plan": plan, "inventory": invs["Public"]}
            packet = run.packet(
                "statement_review",
                c,
                [],
                extra_checks=list(
                    required_interface_citations(
                        {"interface_evidence": {"results": {"T": {}}}}
                    )
                ),
            )
            run.state["pending"] = {"packet": run.put(packet)}
            envelope = run.next()
            self.assertIn(
                "Alg", envelope["packet"]["candidate"]["interface_evidence"]["sources"]
            )
            self.assertIn("OUTPUT_CONTRACT.md", envelope["policy"])
            self.assertLess(packet_bytes(envelope), 64_000_000)
            with patch(
                "autoformalize.review_evidence.MAX_PACKET_BYTES", packet_bytes(envelope)
            ):
                with self.assertRaises(WorkflowError):
                    run.next()

    def test_completion_rechecks_source_budget_and_parameter_ledger(self):
        plan, _, invs = fixture()
        inv = {"declarations": [r for i in invs.values() for r in i["declarations"]]}
        with temporary_workspace() as tmp:
            run = self.make_run(Path(tmp), invs)
            e = plan["output_contract"]["public_results"][0]
            path = run.compiler.project / plan["units"][-1]["file"]
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                "noncomputable def budget : P := "
                + e["design"]["budget"]["expression"],
                encoding="utf-8",
            )
            run.check_public_designs(plan, inv)
            path.write_text(
                "noncomputable def budget : P := fun p _ => p.K", encoding="utf-8"
            )
            with self.assertRaises(WorkflowError):
                run.check_public_designs(plan, inv)


if __name__ == "__main__":
    unittest.main()
