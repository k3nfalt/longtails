import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SETUP = """import LongTails.Template

namespace LongTails.Setups.ComparatorTest
open OracleTemplate

abbrev spec : Setup where
  Params := Unit
  Public := Unit
  Instance _ := Nat
  Query _ := Unit
  Reply _ := Nat
  Output _ := Nat
  publicInput := id
  valid _ := True
  admissible _ target oracle := ∀ k q seed, oracle.answer k q seed = target
  successful _ target output _ := ∀ seed, output seed = target

end LongTails.Setups.ComparatorTest
"""
ALGORITHM = """noncomputable def algorithm : Algorithm Unit Nat Nat where
  State := Nat
  initial := fun _ => 0
  query := fun _ => (0, ())
  update := fun _ reply => reply
  output := id
"""
PROOF = """by
  refine ⟨fun _ => algorithm, ?_, ?_⟩
  · intro p hp I oracle ho
    dsimp only
    intro seed
    change oracle.answer _ _ _ = I
    exact ho _ _ _
  · intro p hp
    trivial
"""


class ComparatorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="longtails-comparator-test-")
        cls.addClassCleanup(cls.directory.cleanup)
        cls.root = Path(cls.directory.name)
        # Isolate sources and build outputs while reusing the pinned dependencies.
        for name in (
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
            "run_comparator.py",
        ):
            shutil.copy2(ROOT / name, cls.root / name)
        for directory in ("tools", "LongTails/Setups", "LongTails/Theorems", ".lake"):
            (cls.root / directory).mkdir(parents=True, exist_ok=True)
        (cls.root / ".lake/packages").symlink_to(
            ROOT / ".lake/packages", target_is_directory=True
        )
        for name in (
            "tools/ConvergenceMetadata.lean",
            "LongTails/Template.lean",
            "LongTails/TemplateOnline.lean",
        ):
            shutil.copy2(ROOT / name, cls.root / name)
        (cls.root / "LongTails/Setups/ComparatorTest.lean").write_text(SETUP)
        (cls.root / "LongTails/Setups/ComparatorOnlineTest.lean").write_text(
            SETUP.replace("LongTails.Template", "LongTails.TemplateOnline")
            .replace("ComparatorTest", "ComparatorOnlineTest")
            .replace("spec : Setup", "spec : OnlineSetup")
            .replace("publicInput := id", "publicInput := fun _ _ => ()")
            .replace("valid _ :=", "valid _ _ :=")
            .replace("admissible _ target", "admissible _ _ target")
            .replace(
                "successful _ target output _ := ∀ seed, output seed = target",
                "successful _ _ _ _ _ bound := 0 ≤ bound",
            )
        )

    def audit(
        self,
        name,
        *,
        budget="fun _ _ => 1",
        proof=PROOF,
        statement=None,
        extra="",
        rejection=None,
        online=False,
        bound_declaration=None,
    ):
        if statement is None:
            statement = (
                "OnlineConvergence spec budget" if online else "Convergence spec budget"
            )
        source = f"""import LongTails.TemplateOnline
import LongTails.Setups.ComparatorTest
namespace LongTails.Theorems.{name}
open OracleTemplate LongTails.Setups.ComparatorTest
{ALGORITHM}
{extra}
noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → Nat) := {budget}
theorem result : {statement} := {proof}
end LongTails.Theorems.{name}
"""
        if online:
            source = (
                source.replace("ComparatorTest", "ComparatorOnlineTest")
                .replace("budget", "bound")
                .replace("S.Params → Fin S.numOracles → Nat", "S.Params → Horizon → ℝ")
            )
        if bound_declaration is not None:
            source = source.replace(
                "def bound : (let S := spec; S.Params → Horizon → ℝ)",
                f"def bound {bound_declaration}",
            )
        (self.root / f"LongTails/Theorems/{name}.lean").write_text(source)
        result = subprocess.run(
            [sys.executable, "run_comparator.py", f"{name}.lean"],
            cwd=self.root,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=300,
        )
        if rejection is None:
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn(
                "Checked 1 convergence results and their budgets.", result.stdout
            )
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn(rejection, result.stdout)

    def test_online_results(self):
        proof = "by exact ⟨fun _ => algorithm, fun _ _ _ _ _ _ => zero_le_one, fun _ _ _ => trivial⟩"
        for name, budget, body, statement, rejection in (
            (
                "OnlineValid",
                "fun _ _ => 1",
                proof,
                "OnlineConvergence spec budget",
                None,
            ),
            (
                "OnlineMissingProof",
                "fun _ _ => 1",
                "by sorry",
                "OnlineConvergence spec budget",
                "Illegal axiom detected: 'sorryAx'",
            ),
            (
                "OnlineMissingBound",
                "by sorry",
                "by sorry",
                "OnlineConvergence spec budget",
                "Illegal axiom detected: 'sorryAx'",
            ),
            (
                "OnlineExtraHypothesis",
                "fun _ _ => 1",
                "by intro h; exact h.elim",
                "False → OnlineConvergence spec budget",
                "without extra hypotheses",
            ),
        ):
            with self.subTest(name=name):
                self.audit(
                    name,
                    budget=budget,
                    proof=body,
                    statement=statement,
                    rejection=rejection,
                    online=True,
                )

    def test_online_explicit_bound_parameters(self):
        self.audit(
            "OnlineExplicitBound",
            online=True,
            bound_declaration="(_p : Unit) (_T : Horizon) : ℝ",
            budget="1",
            proof="by exact ⟨fun _ => algorithm, fun _ _ _ _ _ _ => zero_le_one, fun _ _ _ => trivial⟩",
        )

    def test_mixed_protocols_fail(self):
        for name, online, statement, budget in (
            (
                "SetupWithOnlineConvergence",
                False,
                "OnlineConvergence spec budget",
                "fun _ _ => 1",
            ),
            (
                "OnlineSetupWithConvergence",
                True,
                "Convergence spec budget",
                "fun _ _ => 1",
            ),
            (
                "SetupWithOnlineBound",
                False,
                None,
                "fun (_ : Unit) (_ : Horizon) => (1 : ℝ)",
            ),
            (
                "OnlineSetupWithOracleBudget",
                True,
                None,
                "fun (_ : Unit) (_ : Fin 1) => (1 : ℕ)",
            ),
        ):
            with self.subTest(name=name):
                self.audit(
                    name,
                    online=online,
                    statement=statement,
                    budget=budget,
                    proof="by sorry",
                    rejection="mismatch",
                )

    def test_online_hidden_axiom_in_bound(self):
        self.audit(
            "OnlineBoundAxiom",
            online=True,
            extra="axiom invented : ℝ",
            budget="fun _ _ => 1 + (invented - invented)",
            proof="""by
  unfold budget
  simp only [sub_self, add_zero]
  exact ⟨fun _ => algorithm, fun _ _ _ _ _ _ => zero_le_one, fun _ _ _ => trivial⟩
""",
            rejection="Illegal axiom detected: 'LongTails.Theorems.OnlineBoundAxiom.invented'",
        )

    def test_valid_one_call_result(self):
        self.audit("Valid")

    def test_valid_two_call_result(self):
        self.audit(
            "ValidTwoCalls",
            budget="fun _ _ => 2",
            proof="""by
  refine ⟨fun _ => algorithm, ?_, ?_⟩
  · intro p hp I oracle ho
    dsimp only
    intro seed
    change oracle.answer _ _ _ = I
    exact ho _ _ _
  · intro p hp
    trivial
""",
        )

    def test_insufficient_budget(self):
        self.audit(
            "InsufficientBudget",
            budget="fun _ _ => 0",
            rejection="not definitionally equal",
        )

    def test_missing_proof(self):
        self.audit(
            "MissingProof",
            proof="by sorry",
            rejection="Illegal axiom detected: 'sorryAx'",
        )

    def test_missing_budget(self):
        self.audit(
            "MissingBudget",
            extra="noncomputable def missing : Nat := by sorry",
            budget="fun _ _ => 1 + (missing - missing)",
            proof=PROOF.replace(
                "by\n",
                "by\n  unfold budget\n  simp only [Nat.sub_self, Nat.add_zero]\n",
                1,
            ),
            rejection="Illegal axiom detected: 'sorryAx'",
        )

    def test_hidden_axiom_in_proof(self):
        self.audit(
            "HiddenAxiom",
            extra="axiom invented : False\nlemma helper : False := invented",
            proof="by exact helper.elim",
            rejection="Illegal axiom detected: 'LongTails.Theorems.HiddenAxiom.invented'",
        )

    def test_hidden_axiom_in_budget(self):
        self.audit(
            "BudgetAxiom",
            extra="axiom invented : Nat",
            budget="fun _ _ => 1 + (invented - invented)",
            proof=PROOF.replace(
                "by\n",
                "by\n  unfold budget\n  simp only [Nat.sub_self, Nat.add_zero]\n",
                1,
            ),
            rejection="Illegal axiom detected: 'LongTails.Theorems.BudgetAxiom.invented'",
        )

    def test_extra_hypothesis(self):
        self.audit(
            "ExtraHypothesis",
            statement="False → Convergence spec budget",
            proof="by intro h; exact h.elim",
            rejection="without extra hypotheses",
        )

    def test_unrelated_theorem(self):
        self.audit(
            "Unrelated",
            statement="True",
            proof="by trivial",
            rejection="expected exactly one convergence theorem, found 0",
        )


if __name__ == "__main__":
    unittest.main()
