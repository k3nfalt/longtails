import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ActiveDirectionCertificates

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

lemma convex_error_bound (u v : ι → E) (w : ι → ℝ) (δ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (he : ∀ i, ‖u i - v i‖ ≤ δ) :
    ‖(∑ i, w i • u i) - ∑ i, w i • v i‖ ≤ δ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    _ ≤ ∑ i, ‖w i • (u i - v i)‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖u i - v i‖ := by
      congr 1
      ext i
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * δ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (he i) (hw i))
    _ = δ := by rw [← Finset.sum_mul, hs, one_mul]

lemma approximate_direction_descent (g h v : E) (δ : ℝ)
    (hδ : 0 < δ) (he : ‖g - h‖ ≤ δ) (hv : 4 * δ ≤ ‖v‖)
    (hproj : ‖v‖ ^ 2 - δ ^ 2 ≤ ⟪h, v⟫) :
    ⟪g, -(‖v‖⁻¹ • v)⟫ ≤ -(5 / 2 : ℝ) * δ := by
  have hvpos : 0 < ‖v‖ := by linarith
  have herr : |⟪g - h, v⟫| ≤ δ * ‖v‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have hlow := (abs_le.mp herr).1
  rw [inner_sub_left] at hlow
  have hinner : (5 / 2 : ℝ) * δ * ‖v‖ ≤ ⟪g, v⟫ := by
    have hprod : 0 ≤ (‖v‖ - 4 * δ) * (‖v‖ + δ / 2) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [sq_nonneg δ]
  rw [inner_neg_right, real_inner_smul_right]
  have hi := mul_le_mul_of_nonneg_left hinner (le_of_lt (inv_pos.mpr hvpos))
  have hid : ‖v‖⁻¹ * ((5 / 2 : ℝ) * δ * ‖v‖) = (5 / 2 : ℝ) * δ := by
    field_simp
  rw [hid] at hi
  linarith

lemma objective_weight_bound (g z : E) (J : ι → E) (a : ℝ) (w : ι → ℝ)
    (H μ e : ℝ) (ha : 0 ≤ a) (hw : ∀ i, 0 ≤ w i)
    (hs : a + ∑ i, w i = 1) (hg : ‖g‖ ≤ H) (hz : ‖z‖ ≤ 1)
    (hJ : ∀ i, 0 < w i → ⟪J i, z⟫ ≤ -μ)
    (hr : ‖a • g + ∑ i, w i • J i‖ ≤ e) :
    μ - e ≤ a * (H + μ) := by
  have hg' : ⟪g, z⟫ ≤ H := by
    calc
      ⟪g, z⟫ ≤ ‖g‖ * ‖z‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ ≤ H := by simpa using hg
  have hr' : -e ≤ ⟪a • g + ∑ i, w i • J i, z⟫ := by
    have h := abs_real_inner_le_norm (a • g + ∑ i, w i • J i) z
    have h' : ‖a • g + ∑ i, w i • J i‖ * ‖z‖ ≤ e := by
      calc
        _ ≤ ‖a • g + ∑ i, w i • J i‖ * 1 :=
          mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        _ ≤ e := by simpa using hr
    exact (abs_le.mp (h.trans h')).1
  have hj' : (∑ i, w i * ⟪J i, z⟫) ≤ (∑ i, w i) * (-μ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : w i = 0
    · simp [hi]
    · exact mul_le_mul_of_nonneg_left (hJ i (lt_of_le_of_ne (hw i) (Ne.symm hi))) (hw i)
  simp only [inner_add_left, real_inner_smul_left, sum_inner] at hr'
  have hag := mul_le_mul_of_nonneg_left hg' ha
  have hs' : (∑ i, w i) = 1 - a := by linarith
  rw [hs'] at hj'
  nlinarith

lemma objective_weight_positive (a H μ e : ℝ) (hH : 0 ≤ H) (hμ : 0 < μ)
    (he : e ≤ μ / 2) (h : μ - e ≤ a * (H + μ)) :
    μ / (2 * (H + μ)) ≤ a := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * (H + μ))).2
  nlinarith

lemma normalized_residual (g : E) (J : ι → E) (a : ℝ) (w : ι → ℝ)
    (e : ℝ) (ha : 0 < a) (hr : ‖a • g + ∑ i, w i • J i‖ ≤ e) :
    ‖g + ∑ i, (w i / a) • J i‖ ≤ e / a := by
  have hid : g + ∑ i, (w i / a) • J i =
      a⁻¹ • (a • g + ∑ i, w i • J i) := by
    simp [smul_add, Finset.smul_sum, smul_smul, div_eq_mul_inv, ha.ne', mul_comm]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  simpa [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hr (le_of_lt (inv_pos.mpr ha))

end LongTails.Proofs.ActiveDirectionCertificates
