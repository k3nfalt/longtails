import LongTails.Setups.HeavyTailedAdam

open MeasureTheory

namespace LongTails.Setups.GeneralizedSmoothAdam

open OracleTemplate

noncomputable def method {d : ℕ} (β ρ η τ vinit : ℝ) (n : ℕ) (x0 : Adam.Point d) :
    Algorithm (Adam.Point d) (Adam.Point d) (Adam.Point d) where
  Seed := Fin (n + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (n + 1))).toMeasure, inferInstance⟩
  State := Adam.State d
  initial k := ⟨k.val, 0, x0, 0, WithLp.toLp 2 (fun _ => vinit), x0⟩
  query s := (0, s.point)
  update := Adam.update β ρ η τ
  output s := s.saved

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L0 : ℝ
  L1 : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  β : ℝ
  x0 : Adam.Point d

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Adam.Point q.d → ℝ
  Query q := Adam.Point q.d
  Reply q := Adam.Point q.d
  Output q := Adam.Point q.d
  publicInput q := q
  valid q := 0 ≤ q.L0 ∧ 0 ≤ q.L1 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε ∧
    0 ≤ q.β ∧ q.β < 1
  admissible q f O :=
    ∃ (g : Adam.Point q.d → q.Ω → Adam.Point q.d)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, q.L1 * ‖y - x‖ ≤ 1 →
        ‖gradient f y - gradient f x‖ ≤ (q.L0 + q.L1 * ‖gradient f x‖) * ‖y - x‖) ∧
      (∀ x, f q.x0 - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p) ∧
      (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ q.σ ^ 2)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖gradient f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ q.ε ^ 2
  allowedAlgorithm q A :=
    ∃ (ρ η τ vinit : ℝ) (n : ℕ), 0 < ρ ∧ ρ ≤ 1 ∧ 0 < η ∧ 0 < τ ∧ 0 < vinit ∧
      A = method q.β ρ η τ vinit n q.x0

end LongTails.Setups.GeneralizedSmoothAdam
