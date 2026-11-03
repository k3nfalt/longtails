import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import LongTails.Setups.UscgConstant

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.MinimaxLmo

open OracleTemplate
open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO)

structure GeneralizedMinimax {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] (N : Seminorm ℝ (Space d₁))
    (L₀ L₁ μ σx σy Δ W : ℝ) (x₁ : Space d₁) (y₁ : Space d₂) (f : Space d₁ → Space d₂ → ℝ)
    (gx : Space d₁ → Space d₂ → Space d₁) (gy : Space d₁ → Space d₂ → Space d₂)
    (ox : Space d₁ → Space d₂ → Ω → Space d₁) (oy : Space d₁ → Space d₂ → Ω → Space d₂)
    (p : Measure Ω) : Prop where
  grad_x : ∀ x y, HasGradientAt (fun x' => f x' y) (gx x y) x
  grad_y : ∀ x y, HasGradientAt (f x) (gy x y) y
  smooth_x : ∀ x y x' y', L₁ * (N (x - x') + ‖y - y'‖) ≤ 1 →
    dualNorm N (gx x y - gx x' y') ≤ (L₀ + L₁ * dualNorm N (gx x y)) * (N (x - x') + ‖y - y'‖)
  smooth_y : ∀ x y x' y', L₁ * (N (x - x') + ‖y - y'‖) ≤ 1 →
    ‖gy x y - gy x' y'‖ ≤ (L₀ + L₁ * ‖gy x y‖) * (N (x - x') + ‖y - y'‖)
  strongly_concave : ∀ x y y', f x y' ≤ f x y + ⟪gy x y, y' - y⟫ - μ / 2 * ‖y' - y‖ ^ 2
  gap : ∀ x y, ∃ y', f x₁ y - f x y' ≤ Δ
  warm_start : ∀ y, (∀ y', f x₁ y' ≤ f x₁ y) → ‖y₁ - y‖ ≤ W
  measurable_x : Measurable (fun z : (Space d₁ × Space d₂) × Ω => ox z.1.1 z.1.2 z.2)
  measurable_y : Measurable (fun z : (Space d₁ × Space d₂) × Ω => oy z.1.1 z.1.2 z.2)
  integrable_x : ∀ x y, Integrable (ox x y) p
  integrable_y : ∀ x y, Integrable (oy x y) p
  unbiased_x : ∀ x y, ∫ ω, ox x y ω ∂p = gx x y
  unbiased_y : ∀ x y, ∫ ω, oy x y ω ∂p = gy x y
  variance_x_integrable : ∀ x y, Integrable (fun ω => ‖ox x y ω - gx x y‖ ^ 2) p
  variance_x : ∀ x y, ∫ ω, ‖ox x y ω - gx x y‖ ^ 2 ∂p ≤ σx ^ 2
  variance_y_integrable : ∀ x y, Integrable (fun ω => ‖oy x y ω - gy x y‖ ^ 2) p
  variance_y : ∀ x y, ∫ ω, ‖oy x y ω - gy x y‖ ^ 2 ∂p ≤ σy ^ 2

noncomputable def clip {d : ℕ} (c : ℝ) (v : Space d) : Space d :=
  if ‖v‖ ≤ c then v else (c / ‖v‖) • v

structure GdaState (d₁ d₂ : ℕ) where
  stop : ℕ
  count : ℕ
  x : Space d₁
  y : Space d₂
  momentum : Space d₁

noncomputable def lmoGda {d₁ d₂ : ℕ} (lmo : Space d₁ → Space d₁) (γ α β δ : ℕ → ℝ) (T : ℕ)
    (w : PMF (Fin (T + 1))) (x₁ : Space d₁) (y₁ : Space d₂) :
    Algorithm (Space d₁ × Space d₂) (Space d₁ × Space d₂) (Space d₁) where
  Seed := Fin (T + 1)
  law := ⟨w.toMeasure, inferInstance⟩
  State := GdaState d₁ d₂
  initial j := ⟨j.val, 0, x₁, y₁, 0⟩
  query s := (0, (s.x, s.y))
  update s r :=
    if s.count < s.stop then
      ⟨s.stop, s.count + 1,
        s.x + γ (s.count + 1) • lmo (α (s.count + 1) • r.1 + (1 - α (s.count + 1)) • s.momentum),
        s.y + β (s.count + 1) • clip (δ (s.count + 1)) r.2,
        α (s.count + 1) • r.1 + (1 - α (s.count + 1)) • s.momentum⟩
    else s
  output s := s.x

structure Params where
  d₁ : ℕ
  d₂ : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  N : Seminorm ℝ (Space d₁)
  lmo : Space d₁ → Space d₁
  ρ : ℝ
  R : ℝ
  ζ : ℝ
  x₁ : Space d₁
  y₁ : Space d₂
  L₀ : ℝ
  L₁ : ℝ
  μ : ℝ
  σx : ℝ
  σy : ℝ
  Δ : ℝ
  W : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Space p.d₁ → Space p.d₂ → ℝ
  Query p := Space p.d₁ × Space p.d₂
  Reply p := Space p.d₁ × Space p.d₂
  Output p := Space p.d₁
  publicInput p := p
  valid p :=
    (∀ x, p.N x = 0 → x = 0) ∧ 0 < p.ρ ∧ IsBallLMO p.N p.ρ p.lmo ∧
      (∀ v, p.N v ≤ 1 → ‖v‖ ≤ p.R) ∧ 0 ≤ p.ζ ∧ (∀ u, dualNorm p.N u ≤ p.ζ * ‖u‖) ∧
      0 < p.μ ∧ p.μ ≤ p.L₀ ∧ 0 ≤ p.L₁ ∧ 0 ≤ p.σx ∧ 0 ≤ p.σy ∧ 0 ≤ p.Δ ∧ 0 ≤ p.W ∧
      32 * p.L₁ * p.W ≤ 1 ∧ 0 < p.ε
  admissible p f O :=
    ∃ (gx : Space p.d₁ → Space p.d₂ → Space p.d₁) (gy : Space p.d₁ → Space p.d₂ → Space p.d₂)
      (ox : Space p.d₁ → Space p.d₂ → p.Ω → Space p.d₁) (oy : Space p.d₁ → Space p.d₂ → p.Ω → Space p.d₂)
      (P₀ : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → p.Ω) => ξ k) (P₀ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => p.Ω
            law := P
            answer := fun _ (_, z) ω => (ox z.1 z.2 ω, oy z.1 z.2 ω) } ∧
      GeneralizedMinimax p.N p.L₀ p.L₁ p.μ p.σx p.σy p.Δ p.W p.x₁ p.y₁ f gx gy ox oy (P₀ : Measure _)
  successful p f output P :=
    Measurable output ∧ (∃ ys : Space p.d₁ → Space p.d₂, ∀ x y, f x y ≤ f x (ys x)) ∧
      ∀ ys : Space p.d₁ → Space p.d₂, (∀ x y, f x y ≤ f x (ys x)) →
        Integrable (fun ω => dualNorm p.N (gradient (fun x => f x (ys x)) (output ω))) (P : Measure _) ∧
        ∫ ω, dualNorm p.N (gradient (fun x => f x (ys x)) (output ω)) ∂(P : Measure _) ≤ p.ε
  allowedAlgorithm p A :=
    ∃ (γ α β δ : ℕ → ℝ) (T : ℕ) (w : PMF (Fin (T + 1))),
      (∀ k, 0 ≤ γ k) ∧ (∀ k, 0 < α k ∧ α k ≤ 1) ∧ (∀ k, 0 ≤ β k) ∧ (∀ k, 0 < δ k) ∧
        A = lmoGda p.lmo γ α β δ T w p.x₁ p.y₁

end LongTails.Setups.MinimaxLmo
