import LongTails.Proofs.GuardedGeneralizedGeometry
import Mathlib.Tactic

namespace LongTails.Proofs.AffineTransportCrossings

lemma squared_growth_bound {r s L t d : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hsr : s ≤ r + L * t) (hshort : L * t ≤ r)
    (hdescent : r * t ≤ 4 * d) :
    s ^ 2 - r ^ 2 ≤ 12 * L * d := by
  have hLt : 0 ≤ L * t := mul_nonneg hL ht
  have hsq : s ^ 2 ≤ (r + L * t) ^ 2 :=
    sq_le_sq₀ hs (add_nonneg hr hLt) |>.mpr hsr
  have hsmall := mul_le_mul_of_nonneg_left hshort hLt
  have hprogress := mul_le_mul_of_nonneg_left hdescent hL
  nlinarith

lemma crossing_charge {r s U L d : ℝ}
    (hr : 0 ≤ r) (hU : 0 ≤ U)
    (hstart : r ≤ U / 2) (hend : 2 * U ≤ s)
    (hgrowth : s ^ 2 - r ^ 2 ≤ 12 * L * d) :
    U ^ 2 ≤ 4 * L * d := by
  have hrU : r ^ 2 ≤ (U / 2) ^ 2 :=
    sq_le_sq₀ hr (by positivity) |>.mpr hstart
  have hsU : (2 * U) ^ 2 ≤ s ^ 2 :=
    sq_le_sq₀ (by positivity) (by linarith) |>.mpr hend
  nlinarith [sq_nonneg U]

lemma total_crossing_charge {ι : Type*} (S : Finset ι)
    (drop : ι → ℝ) {U L Δ : ℝ} (hL : 0 ≤ L)
    (hcharge : ∀ i ∈ S, U ^ 2 ≤ 4 * L * drop i)
    (hbudget : ∑ i ∈ S, drop i ≤ Δ) :
    (S.card : ℝ) * U ^ 2 ≤ 4 * L * Δ := by
  calc
    (S.card : ℝ) * U ^ 2 = ∑ _i ∈ S, U ^ 2 := by simp
    _ ≤ ∑ i ∈ S, 4 * L * drop i := Finset.sum_le_sum hcharge
    _ = 4 * L * ∑ i ∈ S, drop i := by rw [Finset.mul_sum]
    _ ≤ 4 * L * Δ := mul_le_mul_of_nonneg_left hbudget (by positivity)

lemma observable_entry {r v U : ℝ} (hU : 0 ≤ U)
    (herror : |v - r| ≤ (U + r) / 32) (hentry : v ≤ U / 4) :
    r ≤ U / 2 := by
  have := (abs_le.mp herror).1
  linarith

lemma observable_exit {r v U : ℝ} (hU : 0 ≤ U)
    (herror : |v - r| ≤ (U + r) / 32) (hexit : 3 * U ≤ v) :
    2 * U ≤ r := by
  have := (abs_le.mp herror).2
  linarith

lemma observable_fine_bound {r v U : ℝ} (hU : 0 ≤ U)
    (herror : |v - r| ≤ (U + r) / 32) (hstay : v ≤ 3 * U) :
    r ≤ 4 * U := by
  have := (abs_le.mp herror).1
  linarith

lemma observable_coarse_lower {r v U : ℝ} (hU : 0 ≤ U)
    (herror : |v - r| ≤ (U + r) / 32) (hcoarse : U / 4 ≤ v) :
    U / 8 ≤ r := by
  have := (abs_le.mp herror).2
  linarith

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma normalized_step_charge {f : E → ℝ} {g : E → E} {L0 L1 η : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hη : 0 ≤ η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (hsmall : L1 * η ≤ 1 / 4) (x z : E)
    (herror : ‖g x - z‖ ≤ ‖g x‖ / 16) (hbase : L0 * η ≤ ‖g x‖ / 8) :
    η * ‖g x‖ ≤ 4 * (f x - f (x - η • (‖z‖⁻¹ • z))) := by
  have hd := GuardedGeneralizedGeometry.normalized_descent hL0 hL1 hη hf hg hH hsmall x z
  have he := mul_le_mul_of_nonneg_left herror hη
  have hb := mul_le_mul_of_nonneg_left hbase hη
  nlinarith

lemma threshold_step_charge {f : E → ℝ} {g : E → E} {L0 L1 η e : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hη : 0 ≤ η) (he : 0 ≤ e)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (hsmall : L1 * η ≤ 1 / 4) (x z : E)
    (herror : ‖z - g x‖ ≤ e / 64) (hlarge : e / 2 < ‖z‖)
    (hbase : L0 * η ≤ e / 512) :
    31 * e / 64 < ‖g x‖ ∧
      η * ‖g x‖ ≤ 4 * (f x - f (x - η • (‖z‖⁻¹ • z))) := by
  have htri := norm_le_norm_sub_add z (g x)
  have hnorm : 31 * e / 64 < ‖g x‖ := by linarith
  refine ⟨hnorm, normalized_step_charge hL0 hL1 hη hf hg hH hsmall x z ?_ ?_⟩
  · rw [norm_sub_rev]
    linarith
  · linarith

omit [CompleteSpace E] in
lemma local_squared_growth {f : E → ℝ} {g : E → E} {L0 L1 U : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hU : 0 ≤ U)
    (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖) (x y : E)
    (hregion : ‖g x‖ ≤ 4 * U) (hsmall : L1 * ‖y - x‖ ≤ 1 / 4)
    (hshort : 2 * (L0 + 4 * L1 * U) * ‖y - x‖ ≤ ‖g x‖)
    (hdescent : ‖g x‖ * ‖y - x‖ ≤ 4 * (f x - f y)) :
    ‖g y‖ ^ 2 - ‖g x‖ ^ 2 ≤ 24 * (L0 + 4 * L1 * U) * (f x - f y) := by
  have hd := GuardedGeneralizedGeometry.short_gradient_difference hL0 hL1 hg hH x y hsmall
  have hc : 2 * (L0 + L1 * ‖g x‖) * ‖y - x‖ ≤
      2 * (L0 + 4 * L1 * U) * ‖y - x‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have := mul_le_mul_of_nonneg_left hregion hL1
    nlinarith
  have ht := norm_le_norm_sub_add (g y) (g x)
  have hs : ‖g y‖ ≤ ‖g x‖ + 2 * (L0 + 4 * L1 * U) * ‖y - x‖ := by linarith
  have hh := squared_growth_bound (norm_nonneg (g x)) (norm_nonneg (g y))
    (show 0 ≤ 2 * (L0 + 4 * L1 * U) by positivity) (norm_nonneg (y - x))
    hs hshort hdescent
  nlinarith only [hh]

end Geometry

end LongTails.Proofs.AffineTransportCrossings
