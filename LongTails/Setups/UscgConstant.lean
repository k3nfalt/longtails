import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.UscgConstant

open OracleTemplate

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def dualNorm {d : ℕ} (N : Seminorm ℝ (Space d)) (u : Space d) : ℝ :=
  sSup ((fun v => ⟪u, v⟫) '' {v | N v ≤ 1})

structure IsBallLMO {d : ℕ} (N : Seminorm ℝ (Space d)) (ρ : ℝ) (lmo : Space d → Space d) :
    Prop where
  measurable : Measurable lmo
  feasible : ∀ s, N (lmo s) ≤ ρ
  minimal : ∀ s x, N x ≤ ρ → ⟪s, lmo s⟫ ≤ ⟪s, x⟫

structure Problem {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (N : Seminorm ℝ (Space d))
    (L L₂ σ Δ : ℝ) (x₁ : Space d) (f : Space d → ℝ) (g : Space d → Ω → Space d)
    (p : Measure Ω) : Prop where
  differentiable : ∀ x, HasGradientAt f (gradient f x) x
  lipschitz : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y)
  lipschitz₂ : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₂ * ‖x - y‖
  lower : ∃ fmin : ℝ, (∀ x, fmin ≤ f x) ∧ f x₁ - fmin ≤ Δ
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) p
  unbiased : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  variance_integrable : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  variance : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ σ ^ 2

structure ConstrainedProblem {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (N : Seminorm ℝ (Space d))
    (ρ L L₂ σ Δ : ℝ) (x₁ : Space d) (f : Space d → ℝ) (g : Space d → Ω → Space d)
    (p : Measure Ω) : Prop where
  differentiable : ∀ x, N x ≤ ρ → HasGradientAt f (gradient f x) x
  lipschitz : ∀ x y, N x ≤ ρ → N y ≤ ρ →
    dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y)
  lipschitz₂ : ∀ x y, N x ≤ ρ → N y ≤ ρ → ‖gradient f x - gradient f y‖ ≤ L₂ * ‖x - y‖
  lower : ∃ fmin : ℝ, (∀ x, N x ≤ ρ → fmin ≤ f x) ∧ f x₁ - fmin ≤ Δ
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, N x ≤ ρ → Integrable (g x) p
  unbiased : ∀ x, N x ≤ ρ → ∫ ω, g x ω ∂p = gradient f x
  variance_integrable : ∀ x, N x ≤ ρ → Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  variance : ∀ x, N x ≤ ρ → ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ σ ^ 2

structure State (d : ℕ) where
  stop : ℕ
  count : ℕ
  point : Space d
  momentum : Space d

noncomputable def lmoMethod {d : ℕ} (step : Space d → Space d → Space d) (α : ℕ → ℝ) (T : ℕ)
    (x₁ : Space d) : Algorithm (Space d) (Space d) (Space d) where
  Seed := Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := State d
  initial j := ⟨j.val, 0, x₁, 0⟩
  query s := (0, s.point)
  update s r :=
    if s.count < s.stop then
      ⟨s.stop, s.count + 1,
        step s.point (α (s.count + 1) • r + (1 - α (s.count + 1)) • s.momentum),
        α (s.count + 1) • r + (1 - α (s.count + 1)) • s.momentum⟩
    else s
  output s := s.point

noncomputable def uscg {d : ℕ} (lmo : Space d → Space d) (α : ℕ → ℝ) (γ : ℝ) (T : ℕ)
    (x₁ : Space d) : Algorithm (Space d) (Space d) (Space d) :=
  lmoMethod (fun x m => x + γ • lmo m) α T x₁

noncomputable def scg {d : ℕ} (lmo : Space d → Space d) (α : ℕ → ℝ) (γ : ℝ) (T : ℕ)
    (x₁ : Space d) : Algorithm (Space d) (Space d) (Space d) :=
  lmoMethod (fun x m => (1 - γ) • x + γ • lmo m) α T x₁

noncomputable def constantMomentum (α : ℝ) : ℕ → ℝ := fun k => if k = 1 then 1 else α

noncomputable def vanishingMomentum : ℕ → ℝ := fun k => 1 / Real.sqrt k

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  N : Seminorm ℝ (Space d)
  lmo : Space d → Space d
  ρ : ℝ
  ρ₂ : ℝ
  ζ : ℝ
  x₁ : Space d
  L : ℝ
  L₂ : ℝ
  σ : ℝ
  Δ : ℝ
  α : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

noncomputable def horizon (p : Params) : ℕ :=
  ⌈((p.Δ / p.ρ + p.L * p.ρ / 2 + (p.ρ₂ / p.ρ + p.ζ) * (2 * p.L₂ * p.ρ₂ + 4 * p.σ) / p.α) /
    p.ε) ^ 2⌉₊

noncomputable def stepSize (p : Params) : ℝ := 1 / Real.sqrt (horizon p + 1)

noncomputable def method (p : Params) : Algorithm (Space p.d) (Space p.d) (Space p.d) :=
  uscg p.lmo (constantMomentum p.α) (stepSize p) (horizon p) p.x₁

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Space p.d → ℝ
  Query p := Space p.d
  Reply p := Space p.d
  Output p := Space p.d
  publicInput p := p
  valid p :=
    (∀ x, p.N x = 0 → x = 0) ∧ 0 < p.ρ ∧ IsBallLMO p.N p.ρ p.lmo ∧
      (∀ x, p.N x ≤ p.ρ → ‖x‖ ≤ p.ρ₂) ∧ 0 ≤ p.ζ ∧ (∀ u, dualNorm p.N u ≤ p.ζ * ‖u‖) ∧
      0 < p.L ∧ 0 ≤ p.L₂ ∧ 0 ≤ p.σ ∧ 0 ≤ p.Δ ∧ 0 < p.α ∧ p.α < 1 ∧ 0 < p.ε
  admissible p f O :=
    ∃ (g : Space p.d → p.Ω → Space p.d) (P₀ : ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (ℕ → p.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → p.Ω) => ξ k) (P₀ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => p.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      Problem p.N p.L p.L₂ p.σ p.Δ p.x₁ f g (P₀ : Measure _)
  successful p f output P :=
    Measurable output ∧
      Integrable (fun ω => dualNorm p.N (gradient f (output ω))) (P : Measure _) ∧
      ∫ ω, dualNorm p.N (gradient f (output ω)) ∂(P : Measure _) ≤
        p.ε + (p.ρ₂ / p.ρ + p.ζ) * Real.sqrt (2 * p.α) * p.σ
  allowedAlgorithm p A := A = method p

attribute [local simp] dualNorm lmoMethod uscg scg constantMomentum vanishingMomentum horizon stepSize method

end LongTails.Setups.UscgConstant
