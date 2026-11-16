import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  n : ℕ
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  Δ : ℝ
  ε : ℝ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)

noncomputable def objective {p : Params} (f : Fin p.n → Point p → ℝ) (x : Point p) : ℝ :=
  (p.n : ℝ)⁻¹ * ∑ i, f i x

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → Point p → ℝ
  Query p := Fin p.n × Point p
  Reply p := ℝ × Point p
  Output p := Point p
  publicInput := id
  valid p := 0 < p.L0 ∧ 0 ≤ p.L1 ∧ 0 < p.R ∧ 0 < p.ε ∧ 2 ≤ p.n ∧
    2 * p.ε ≤ p.Δ ∧ 4 * p.n * p.ε ≤ p.L0 * p.R ^ 2 ∧
    ⌈(2 : ℝ) ^ 80 * (1 + p.n + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε) ^ 24⌉₊ ≤ p.d
  admissible p f oracle :=
    (∀ i, ConvexOn ℝ Set.univ (f i)) ∧
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ i, Differentiable ℝ (gradient (f i))) ∧
    (∀ i x, ‖fderiv ℝ (gradient (f i)) x‖ ≤ p.L0 + p.L1 * ‖gradient (f i) x‖) ∧
    (∀ history seed i x, oracle.answer history (0, (i, x)) seed = (f i x, gradient (f i) x)) ∧
    ∃ xstar, (∀ i, IsMinOn (f i) Set.univ xstar) ∧ ‖xstar‖ ≤ p.R ∧
      objective f 0 - objective f xstar ≤ p.Δ
  successful p f output P :=
    ∃ xstar, (∀ i, IsMinOn (f i) Set.univ xstar) ∧
      Integrable (fun ω => objective f (output ω) - objective f xstar) (P : Measure _) ∧
      (∫ ω, objective f (output ω) - objective f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum
