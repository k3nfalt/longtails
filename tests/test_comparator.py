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
    change oracle.answer 0 (0, ()) (seed.2 0) = I
    exact ho 0 (0, ()) (seed.2 0)
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
        for name in ("tools/ConvergenceMetadata.lean", "LongTails/Template.lean"):
            shutil.copy2(ROOT / name, cls.root / name)
        (cls.root / "LongTails/Setups/ComparatorTest.lean").write_text(SETUP)

    def audit(
        self,
        name,
        *,
        budget="fun _ _ => 1",
        proof=PROOF,
        statement="Convergence spec budget",
        extra="",
        rejection=None,
    ):
        source = f"""import LongTails.Setups.ComparatorTest
namespace LongTails.Theorems.{name}
open OracleTemplate LongTails.Setups.ComparatorTest
{ALGORITHM}
{extra}
noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → Nat) := {budget}
theorem result : {statement} := {proof}
end LongTails.Theorems.{name}
"""
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
    change oracle.answer 1 (0, ()) (seed.2 1) = I
    exact ho 1 (0, ()) (seed.2 1)
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
