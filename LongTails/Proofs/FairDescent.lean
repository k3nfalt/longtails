import LongTails.Proofs.HeavyTailedSospDescent
import LongTails.Proofs.NormalizedStormMoments

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory
open NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma initial_gradient_bound {f : E → ℝ} {g : E → E} {L Δ : ℝ} {x0 : E}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hgap : ∀ x, f x0 - f x ≤ Δ) : ‖g x0‖ ≤ Real.sqrt (2 * L * Δ) := by
  have hd := Gradient.descent hL hg hLip x0
  have hh := hgap (x0 - (1 / L) • g x0)
  have hs : ‖g x0‖ ^ 2 ≤ Δ * (2 * L) :=
    (div_le_iff₀ (by positivity : 0 < 2 * L)).mp (by linarith)
  have he := Real.sq_sqrt (by positivity : 0 ≤ 2 * L * Δ)
  nlinarith [Real.sqrt_nonneg (2 * L * Δ), norm_nonneg (g x0)]

omit [CompleteSpace E] in
lemma path_distance {η : ℝ} (hη : 0 ≤ η) (x v : ℕ → E) {T : ℕ}
    (hx : ∀ t < T, x (t + 1) = stormStep η (x t) (v t)) :
    ∀ t, t ≤ T → ‖x t - x 0‖ ≤ (t : ℝ) * η
  | 0, _ => by simp
  | t + 1, ht => by
      have hi := path_distance hη x v hx t (by omega)
      have hd : ‖x (t + 1) - x t‖ ≤ η := by
        rw [hx t (by omega)]
        exact stormStep_dist hη _ _
      have hh := norm_sub_le_norm_sub_add_norm_sub (x (t + 1)) (x t) (x 0)
      push_cast
      linarith

lemma path_gradient_bound {f : E → ℝ} {g : E → E} {L Δ η : ℝ}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hη : 0 ≤ η) (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (x v : ℕ → E) {T : ℕ} (hx : ∀ t < T, x (t + 1) = stormStep η (x t) (v t))
    (hgap : ∀ y, f (x 0) - f y ≤ Δ) {t : ℕ} (ht : t ≤ T) :
    ‖g (x t)‖ ≤ Real.sqrt (2 * L * Δ) + L * (t : ℝ) * η := by
  have h0 := initial_gradient_bound hL hΔ hg hLip hgap
  have hd := path_distance hη x v hx t ht
  have hh := hLip (x t) (x 0)
  have hm := mul_le_mul_of_nonneg_left hd hL.le
  have hn := norm_le_norm_add_norm_sub (g (x 0)) (g (x t))
  rw [norm_sub_rev (g (x 0))] at hn
  nlinarith

lemma path_descent_sum {f : E → ℝ} {g : E → E} {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (x v : ℕ → E) {T : ℕ} (hx : ∀ t < T, x (t + 1) = stormStep η (x t) (v t)) :
    ∀ t, t ≤ T → η * (∑ j ∈ Finset.range t, ‖g (x j)‖) + f (x t) ≤
      f (x 0) + 2 * η * (∑ j ∈ Finset.range t, ‖v j - g (x j)‖) + (t : ℝ) * L * η ^ 2 / 2
  | 0, _ => by simp
  | t + 1, ht => by
      have hi := path_descent_sum hL hη hg hLip x v hx t (by omega)
      have hd := LongTails.Proofs.HeavyTailedSospDescent.normalized_step_descent
        hL hη hg hLip (x t) (v t)
      have he : x t - η • (‖v t‖⁻¹ • v t) = stormStep η (x t) (v t) := by
        simp only [stormStep, smul_smul, div_eq_mul_inv]
      rw [he, ← hx t (by omega), norm_sub_rev (g (x t))] at hd
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      nlinarith

end OracleTemplate.FairVarianceReduction
