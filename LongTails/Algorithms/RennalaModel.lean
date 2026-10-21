import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace OracleTemplate.Rennala

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Params where
  d : ℕ
  n : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  Delta : ℝ
  x0 : Point d
  tau : Fin n → ℝ

structure Public where
  d : ℕ
  n : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  x0 : Point d
  horizon : ℕ

structure Instance (d : ℕ) where
  f : Point d → ℝ
  lower : ℝ

noncomputable def batchSize (v eps : ℝ) : ℕ := max ⌈v / eps⌉₊ 1

noncomputable def stepSize (L v eps : ℝ) : ℝ :=
  if v = 0 then 1 / L else min (1 / L) (eps * (batchSize v eps : ℝ) / (2 * L * v))

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  n := p.n
  L := p.L
  v := p.v
  eps := p.eps
  x0 := p.x0
  horizon := ⌊24 * p.L * p.Delta / p.eps⌋₊

structure SmoothLower (p : Params) (I : Instance p.d) : Prop where
  hasGradient : ∀ x, HasGradientAt I.f (gradient I.f x) x
  lipschitz : ∀ x y, ‖gradient I.f x - gradient I.f y‖ ≤ p.L * ‖x - y‖
  lower : ∀ x, I.lower ≤ I.f x
  gap : I.f p.x0 - I.lower = p.Delta

abbrev StochasticOracle {d : ℕ} (Ω : Type) [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (f : Point d → ℝ) (g : Point d → Ω → Point d) (v : ℝ) : Prop :=
  LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω (μ : Measure Ω) f g (Real.sqrt v)

end OracleTemplate.Rennala
