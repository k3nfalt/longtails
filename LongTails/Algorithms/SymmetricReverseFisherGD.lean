import LongTails.Setups.SymmetricGaussianReverseFisher
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory OracleTemplate WithLp
open scoped ENNReal

namespace LongTails.Algorithms.SymmetricReverseFisherGD

open LongTails.Setups.SymmetricGaussianReverseFisher

noncomputable def coordinateLaw : ProbabilityMeasure ℝ :=
  ⟨(2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1), ⟨by
    norm_num [Measure.smul_apply, Real.volume_Icc]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩⟩

noncomputable def initial (p : Params) (seed : Fin p.dimension → ℝ) : Space p :=
  let z : Space p := toLp 2 seed
  if z = 0 then EuclideanSpace.single ⟨0, p.dimension.pos⟩ 1 else ‖z‖⁻¹ • z

noncomputable def step (p : Params) : ℝ := 1 / (48 + 20 * p.upper)

noncomputable def algorithm (p : Params) : Algorithm (Space p) (Space p) (Space p) where
  Seed := Fin p.dimension → ℝ
  law := ⟨Measure.pi (fun _ => (coordinateLaw : Measure ℝ)), inferInstance⟩
  State := Space p
  initial := initial p
  query x := (0, x)
  update x reply := x - step p • reply
  output x := x

noncomputable def output (p : Params) (oracle : Oracle (Space p) (Space p)) (K : ℕ)
    (seed : Fin p.dimension → ℝ) (oracleSeed : (k : ℕ) → oracle.Seed k) : Space p :=
  execute oracle (algorithm p) (fun _ => K) seed oracleSeed

end LongTails.Algorithms.SymmetricReverseFisherGD
