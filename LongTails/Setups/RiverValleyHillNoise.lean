import LongTails.Template
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OracleTemplate.StepDecaySgd

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def method (ηs ηc : ℝ) (T K : ℕ) (x0 : E) : Algorithm E E E where
  Seed := Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := ℕ × ℕ × E
  initial τ := (τ.val, 0, x0)
  query s := (0, s.2.2)
  update s g :=
    if s.2.1 < s.1 then (s.1, s.2.1 + 1, s.2.2 - ηs • g)
    else if s.2.1 < s.1 + K then (s.1, s.2.1 + 1, s.2.2 - ηc • g)
    else s
  output s := s.2.2

end OracleTemplate.StepDecaySgd

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.RiverValleyHillNoise

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  Lh : ℝ
  ρh : ℝ
  G : ℝ
  Γ : ℝ
  LJ : ℝ
  ρJ : ℝ
  μ : ℝ
  Lv : ℝ
  σu : ℝ
  σv : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE
  Params.borelE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p :=
    0 < p.μ ∧ p.μ ≤ p.Lv ∧ 0 ≤ p.Lh ∧ 0 ≤ p.ρh ∧ 0 ≤ p.G ∧ 0 ≤ p.Γ ∧ 0 ≤ p.LJ ∧ 0 ≤ p.ρJ ∧
    0 ≤ p.σu ∧ 0 ≤ p.σv ∧ 0 ≤ p.Δ ∧ 0 < p.ε ∧ 16 * p.Γ ≤ 1 ∧
    64 * (p.Γ * p.Lh + 2 * p.LJ * p.G) ≤ p.μ ∧
    64 * (2 * p.G * p.ρJ + 2 * p.LJ * p.Lh + p.Γ * p.ρh + p.G * p.LJ ^ 2) * p.σu ≤ p.μ * p.Lv ∧
    32 * p.Lh * Real.log (3 + p.Lv ^ 2 / p.μ ^ 2 + 4 * p.Lv ^ 2 *
      ((2 * p.G * p.ρh + p.Lh ^ 2) * p.σu ^ 2 + 4 * p.Lv ^ 2 * p.σv ^ 2 +
        20 * p.Γ ^ 2 * p.μ ^ 2 * p.σu ^ 2 + 8 * p.Lv * p.LJ ^ 2 * p.σu ^ 4 / p.μ +
        p.Γ * p.μ * p.G * p.LJ * p.σu ^ 2 / 4) /
      (p.μ ^ 3 * (p.Lv * p.ε ^ 2 + 8 *
      (2 * p.Lh * p.σu ^ 2 + 7 * (256 * (p.Γ * p.Lh + 2 * p.LJ * p.G) ^ 2 / p.μ + 32 * p.Γ * (p.Γ * p.Lh + 2 * p.LJ * p.G) +
          2 * (2 * p.G * p.ρJ + 2 * p.LJ * p.Lh + p.Γ * p.ρh + p.G * p.LJ ^ 2) * p.σu / p.Lv) * (p.σv ^ 2 + p.σu ^ 2) +
        (p.Γ * p.Lh + 2 * p.LJ * p.G) * p.σu * p.σv + (2 * p.G * p.ρJ + 2 * p.LJ * p.Lh + p.Γ * p.ρh + p.G * p.LJ ^ 2) * p.σu ^ 3 / p.μ +
        (2 * p.G * p.ρJ + 2 * p.LJ * p.Lh + p.Γ * p.ρh + p.G * p.LJ ^ 2) * p.Γ * p.G * p.σu ^ 2 / p.Lv + 2 * p.LJ ^ 2 * p.σu ^ 4 / p.Lv)))) ≤ p.μ
  admissible p f O :=
    ∃ (K : Submodule ℝ p.E) (h : p.E → ℝ) (gh : p.E → p.E) (Hh : p.E → p.E →L[ℝ] p.E)
      (φ : p.E → p.E) (Jφ : p.E → p.E →L[ℝ] p.E) (DJ : p.E → p.E →L[ℝ] p.E →L[ℝ] p.E)
      (A : p.E →L[ℝ] p.E) (g : p.E → p.Ω → p.E) (P0 : ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (ℕ → p.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (P0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (f = fun x => h (Kᗮ.starProjection x) +
      1 / 2 * ⟪A (K.starProjection x - φ (Kᗮ.starProjection x)),
        K.starProjection x - φ (Kᗮ.starProjection x)⟫) ∧
    (∀ y, HasGradientAt h (gh y) y) ∧ (∀ y y', ‖gh y - gh y'‖ ≤ p.Lh * ‖y - y'‖) ∧
    (∀ y, HasFDerivAt gh (Hh y) y) ∧ (∀ y y', ‖Hh y - Hh y'‖ ≤ p.ρh * ‖y - y'‖) ∧
    (∀ y, ‖gh y‖ ≤ p.G) ∧
    (∀ y, φ y ∈ K) ∧ (∀ y, HasFDerivAt φ (Jφ y) y) ∧
    (∀ y y', ‖Jφ y - Jφ y'‖ ≤ p.LJ * ‖y - y'‖) ∧ (∀ y, HasFDerivAt Jφ (DJ y) y) ∧
    (∀ y y', ‖DJ y - DJ y'‖ ≤ p.ρJ * ‖y - y'‖) ∧
    (∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫) ∧ (∀ k ∈ K, A k ∈ K) ∧
    (∀ k ∈ K, p.μ * ‖k‖ ^ 2 ≤ ⟪A k, k⟫) ∧ (∀ k ∈ K, ‖A k‖ ≤ p.Lv * ‖k‖) ∧
    (∀ y z, ‖A (Jφ y (Kᗮ.starProjection z))‖ ≤ p.Γ * p.μ * ‖Kᗮ.starProjection z‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(P0 : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖Kᗮ.starProjection (g x ω - gradient f x)‖ ^ 2) (P0 : Measure _)) ∧
    (∀ x, Integrable (fun ω => ‖K.starProjection (g x ω - gradient f x)‖ ^ 2) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖Kᗮ.starProjection (g x ω - gradient f x)‖ ^ 2 ∂(P0 : Measure _) ≤ p.σu ^ 2) ∧
    (∀ x, ∫ ω, ‖K.starProjection (g x ω - gradient f x)‖ ^ 2 ∂(P0 : Measure _) ≤ p.σv ^ 2)
  successful p f output P :=
    Measurable output ∧ Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ p.ε
  allowedAlgorithm p A :=
    ∃ ηs ηc : ℝ, 0 < ηs ∧ 0 < ηc ∧ ∃ T K : ℕ, A = StepDecaySgd.method ηs ηc T K p.x0

end LongTails.Setups.RiverValleyHillNoise
