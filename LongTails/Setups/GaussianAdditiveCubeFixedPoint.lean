import LongTails.Setups.AdditiveCubeFixedPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure

open MeasureTheory OracleTemplate

namespace LongTails.Setups.GaussianAdditiveCubeFixedPoint

open LongTails.Setups.AdditiveCubeFixedPoint

noncomputable def gaussianOracle (p : Params) (T : Cube p → Cube p) (v : NNReal) :
    Oracle (Cube p) (Point p) where
  Seed := fun _ => Point p
  law := ⟨Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin p.d =>
    ProbabilityTheory.gaussianReal 0 v)), inferInstance⟩
  answer := fun _ (_, x) z => (T x).val + z

abbrev spec : Setup := { AdditiveCubeFixedPoint.spec with
  valid := fun p => AdditiveCubeFixedPoint.spec.valid p ∧ 128 * p.ε ≤ p.R ∧ ⌈p.R / p.ε⌉₊ ≤ p.d
  admissible := fun p T O => AdditiveCubeFixedPoint.spec.admissible p T O ∧ ∃ v : NNReal, O = gaussianOracle p T v }

end LongTails.Setups.GaussianAdditiveCubeFixedPoint
