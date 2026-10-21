import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SETUP = """import LongTailsOnline.Template

namespace LongTailsOnline.Setups.ComparatorTest
open OnlineTemplate

abbrev spec : Setup where
  Params := Unit
  Public := Unit
  Instance _ := Unit
  Observation _ := Unit
  Action _ := Unit
  Feedback _ := Unit
  Outcome _ := Unit
  Bound _ := Nat
  publicInput := id
  horizon _ := 1
  valid _ := True
  admissible _ _ _ := True
  successful _ _ b _ := 1 ≤ b

end LongTailsOnline.Setups.ComparatorTest
"""
METHOD = """noncomputable def method : (p : spec.Public) →
    Algorithm (spec.Observation p) (spec.Action p) (spec.Feedback p) := fun _ => {
  State := Nat
  initial := ⟨MeasureTheory.Measure.dirac 0, inferInstance⟩
  choose _ := ProbabilityTheory.Kernel.deterministic (fun s => ((), s.1)) (by fun_prop)
  update _ := ProbabilityTheory.Kernel.deterministic (fun s => s.1) (by fun_prop) }
"""
PROOF = """by
  constructor
  · intro _ _; trivial
  · intro _ _ _ _ _
    constructor
    · exact Filter.Eventually.of_forall (fun _ _ => trivial)
    · exact Nat.le_refl 1
"""


class OnlineComparatorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(
            prefix="longtails-online-comparator-test-"
        )
        cls.addClassCleanup(cls.directory.cleanup)
        cls.root = Path(cls.directory.name)
        for name in (
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
            "run_comparator.py",
            "run_online_comparator.py",
        ):
            shutil.copy2(ROOT / name, cls.root / name)
        for directory in (
            "tools",
            "LongTailsOnline/Setups",
            "LongTailsOnline/Theorems",
            ".lake",
        ):
            (cls.root / directory).mkdir(parents=True, exist_ok=True)
        (cls.root / ".lake/packages").symlink_to(
            ROOT / ".lake/packages", target_is_directory=True
        )
        for name in ("tools/OnlineMetadata.lean", "LongTailsOnline/Template.lean"):
            shutil.copy2(ROOT / name, cls.root / name)
        (cls.root / "LongTailsOnline/Setups/ComparatorTest.lean").write_text(SETUP)

    def audit(
        self,
        name,
        *,
        method=METHOD,
        bound="fun _ => 1",
        proof=PROOF,
        statement="Guarantee spec method bound",
        extra="",
        rejection=None,
    ):
        source = f"""import LongTailsOnline.Setups.ComparatorTest
namespace LongTailsOnline.Theorems.{name}
open OnlineTemplate LongTailsOnline.Setups.ComparatorTest
{extra}
{method}
noncomputable def bound : (p : spec.Params) → spec.Bound p := {bound}
theorem result : {statement} := {proof}
end LongTailsOnline.Theorems.{name}
"""
        (self.root / f"LongTailsOnline/Theorems/{name}.lean").write_text(source)
        result = subprocess.run(
            [sys.executable, "run_online_comparator.py", f"{name}.lean"],
            cwd=self.root,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=300,
        )
        if rejection is None:
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn(
                "Checked 1 online results, algorithms, and bounds.", result.stdout
            )
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn(rejection, result.stdout)

    def test_valid_guarantee(self):
        self.audit("Valid")

    def test_valid_existence_result(self):
        self.audit(
            "Existence",
            statement="Achievable spec bound",
            proof="by\n  refine ⟨method, ?_⟩\n" + PROOF.removeprefix("by\n"),
        )

    def test_missing_proof(self):
        self.audit(
            "MissingProof",
            proof="by sorry",
            rejection="Illegal axiom detected: 'sorryAx'",
        )

    def test_hidden_axiom_in_proof(self):
        self.audit(
            "ProofAxiom",
            extra="axiom invented : False",
            proof="by exact invented.elim",
            rejection="Illegal axiom detected: 'LongTailsOnline.Theorems.ProofAxiom.invented'",
        )

    def test_hidden_axiom_in_bound(self):
        self.audit(
            "BoundAxiom",
            extra="axiom invented : Nat",
            bound="fun _ => 1 + (invented - invented)",
            proof=PROOF.replace("exact Nat.le_refl 1", "simp [spec, bound]"),
            rejection="Illegal axiom detected: 'LongTailsOnline.Theorems.BoundAxiom.invented'",
        )

    def test_hidden_axiom_in_method(self):
        self.audit(
            "MethodAxiom",
            extra="axiom invented : Nat",
            method=METHOD.replace("Measure.dirac 0", "Measure.dirac invented"),
            rejection="Illegal axiom detected: 'LongTailsOnline.Theorems.MethodAxiom.invented'",
        )

    def test_extra_hypothesis(self):
        self.audit(
            "ExtraHypothesis",
            statement="False → Guarantee spec method bound",
            proof="by intro h; exact h.elim",
            rejection="without extra hypotheses",
        )

    def test_unrelated_theorem(self):
        self.audit(
            "Unrelated",
            statement="True",
            proof="by trivial",
            rejection="expected exactly one online theorem, found 0",
        )

    def test_false_bound(self):
        self.audit("FalseBound", bound="fun _ => 0", rejection="Type mismatch")


if __name__ == "__main__":
    unittest.main()
