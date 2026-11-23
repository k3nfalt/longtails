import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Setups.ConvexFiniteSumMeanSquareHessian

open OracleTemplate MeasureTheory

structure Params where
  n : ℕ
  d : ℕ
  H : ℝ
  R : ℝ
  ε : ℝ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)
abbrev Reply (p : Params) := ℝ × Point p × (Point p →L[ℝ] Point p)

structure Instance (p : Params) where
  f : Fin p.n → Point p → ℝ
  xstar : Point p

noncomputable def objective {p : Params} (I : Instance p) (x : Point p) : ℝ :=
  (∑ i, I.f i x) / p.n

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Params
  publicInput p := p
  Instance := Instance
  Query p := Fin p.n × Point p
  Reply := Reply
  Output := Point
  valid p :=
    let K := ⌈(p.H * p.R ^ 3 / (Real.sqrt p.n * p.ε)) ^ (2 / 7 : ℝ)⌉₊
    0 < p.n ∧ 0 ≤ p.H ∧ 0 < p.R ∧ 0 < p.ε ∧ 2 ^ 170 * p.n ^ 3 * (1 + K) ^ 12 ≤ p.d
  admissible p I O :=
    (∀ i, ContDiff ℝ 2 (I.f i)) ∧ ConvexOn ℝ Set.univ (objective I) ∧
    (∀ x y, ∑ i, ‖fderiv ℝ (gradient (I.f i)) x - fderiv ℝ (gradient (I.f i)) y‖ ^ 2 ≤
      p.n * p.H ^ 2 * ‖x - y‖ ^ 2) ∧
    ‖I.xstar‖ ≤ p.R ∧ (∀ x, objective I I.xstar ≤ objective I x) ∧
    (∀ history seed i x, O.answer history (0, i, x) seed =
      (I.f i x, gradient (I.f i) x, fderiv ℝ (gradient (I.f i)) x))
  successful p I output P :=
    Measurable output ∧ Integrable (fun ω => objective I (output ω) - objective I I.xstar) (P : Measure _) ∧
      (∫ ω, objective I (output ω) - objective I I.xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.ConvexFiniteSumMeanSquareHessian
