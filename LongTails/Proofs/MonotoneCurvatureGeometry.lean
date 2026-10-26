import LongTails.Algorithms.MonotoneCurvatureStage
import LongTails.Proofs.QuarticStageTrial

namespace LongTails.Proofs.MonotoneCurvatureGeometry

open LongTails.Algorithms.MonotoneCurvatureStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Algorithms.QuarticMetricStage
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma inverse_radius (S : E ≃L[ℝ] E) {b : ℝ} (hb : 0 < b)
    (hS : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2) (z : E) :
    ‖S.symm z‖ ≤ ‖z‖ / b := by
  have h := hS (S.symm z)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  apply (le_div_iff₀ hb).mpr
  have hs : (‖S.symm z‖ * b) ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith only [h]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hs

omit [FiniteDimensional ℝ E] in
lemma factor_pairing (S : E ≃L[ℝ] E) (B : E →L[ℝ] E) (hB : B.toLinearMap.IsSymmetric)
    (hS : ∀ v, ‖S v‖ ^ 2 = ⟪v, B v⟫) (x y : E) :
    ⟪S x, S y⟫ = ⟪x, B y⟫ := by
  have hp := hS (x + y)
  have hx := hS x
  have hy := hS y
  have hb : ⟪x, B y⟫ = ⟪y, B x⟫ := by
    have hh := hB x y
    change ⟪B x, y⟫ = ⟪x, B y⟫ at hh
    exact hh.symm.trans (real_inner_comm _ _)
  simp only [map_add, norm_add_sq_real, inner_add_left, inner_add_right] at hp
  linarith

lemma correction_equation (S : E ≃L[ℝ] E) (B : E →L[ℝ] E)
    (hB : B.toLinearMap.IsSymmetric) (hS : ∀ v, ‖S v‖ ^ 2 = ⟪v, B v⟫) (g : E) :
    B (S.symm (transformedGradient S g)) = g := by
  apply ext_inner_left ℝ
  intro y
  rw [← factor_pairing S B hB hS, ContinuousLinearEquiv.apply_symm_apply]
  unfold transformedGradient
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp

omit [FiniteDimensional ℝ E] in
lemma inverse_operator_norm (S : E ≃L[ℝ] E) {b : ℝ} (hb : 0 < b)
    (hS : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2) :
    ‖S.symm.toContinuousLinearMap‖ ≤ b⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hb.le)
  intro z
  simpa only [ContinuousLinearEquiv.coe_coe, div_eq_mul_inv, mul_comm] using inverse_radius S hb hS z

lemma dual_norm (S : E ≃L[ℝ] E) {b : ℝ} (hb : 0 < b)
    (hS : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2) (g : E) :
    ‖transformedGradient S g‖ ≤ ‖g‖ / b := by
  have h := S.symm.toContinuousLinearMap.adjoint.le_opNorm g
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans ((mul_le_mul_of_nonneg_right (inverse_operator_norm S hb hS) (norm_nonneg g)).trans_eq (by ring))

lemma trial_distance (p : Parameters E) {A b : ℝ} (hb : 0 < b)
    (hS : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖p.S v‖ ^ 2)
    (hL : 0 < p.L) (hr : 0 ≤ p.r) (y : Point E)
    (hy : ‖p.S (y.x - p.center.x)‖ ≤ A) :
    ‖trialPoint p y - p.center.x‖ ≤ (A + p.r / 2) / b := by
  have h := QuarticStageTrial.trial_radius p y hL hr
  have hm : ‖p.S (trialPoint p y - p.center.x)‖ ≤ A + p.r / 2 := by
    calc
      _ = ‖p.S (trialPoint p y - y.x) + p.S (y.x - p.center.x)‖ := by
        rw [← map_add]; congr 2; abel
      _ ≤ ‖p.S (trialPoint p y - y.x)‖ + ‖p.S (y.x - p.center.x)‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hi := inverse_radius p.S hb hS (p.S (trialPoint p y - p.center.x))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hi
  exact hi.trans (div_le_div_of_nonneg_right hm hb.le)

omit [FiniteDimensional ℝ E] in
lemma disabled_gradient_stop (S : E ≃L[ℝ] E) (c x : Point E) (H γ t : ℝ) :
    successful (parameters S c H γ t) x ↔ x.value ≤ c.value - γ * (γ / (2 ^ 30 * H)) ^ 2 := by
  simp only [successful, parameters]
  have h : ¬‖x.gradient‖ ≤ (-1 : ℝ) := by linarith [norm_nonneg x.gradient]
  simp [h]

omit [FiniteDimensional ℝ E] in
lemma signed_direction_norm (g v : E) (hv : v ≠ 0) : ‖signedDirection g v‖ = 1 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  unfold signedDirection
  split <;> simp [norm_smul, hn]

omit [FiniteDimensional ℝ E] in
lemma signed_direction_pairing (g v : E) : ⟪g, signedDirection g v⟫ ≤ 0 := by
  unfold signedDirection
  split
  · rename_i h
    simpa only [inner_smul_right] using mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg v)) h
  · rename_i h
    simp only [inner_neg_right, inner_smul_right]
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr (norm_nonneg v)) (le_of_not_ge h))

omit [FiniteDimensional ℝ E] in
lemma signed_direction_curvature (A : E →L[ℝ] E) (g v : E) {γ : ℝ}
    (hv : v ≠ 0) (hc : ⟪v, A v⟫ ≤ -γ * ‖v‖ ^ 2) :
    ⟪signedDirection g v, A (signedDirection g v)⟫ ≤ -γ := by
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have he : ⟪‖v‖⁻¹ • v, A (‖v‖⁻¹ • v)⟫ = ⟪v, A v⟫ / ‖v‖ ^ 2 := by
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hh : ⟪‖v‖⁻¹ • v, A (‖v‖⁻¹ • v)⟫ ≤ -γ := by
    rw [he]
    exact (div_le_iff₀ hn).mpr hc
  unfold signedDirection
  split
  · exact hh
  · simpa only [map_neg, inner_neg_left, inner_neg_right, neg_neg] using hh

end LongTails.Proofs.MonotoneCurvatureGeometry
