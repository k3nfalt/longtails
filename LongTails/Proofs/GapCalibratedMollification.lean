import LongTails.Proofs.GapCalibratedConjugate
import LongTails.Proofs.SmoothConvexMollification
import LongTails.Proofs.AdaptiveGeneralizedSmoothLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapCalibratedMollification

open GapCalibratedConjugate CompactMollification GeneralizedSmoothMollification

variable {m : ℕ} (hm : 0 < m) (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
  (L₀ L₁ B A : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
  (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)

include hm hL₀ hL₁ hG hB hGB

lemma objective_continuous : Continuous (objective L₀ L₁ B A G) :=
  continuous_iff_continuousAt.mpr (fun x =>
    (objective_hasGradientAt hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB x).continuousAt)

lemma field_continuous : Continuous (field L₀ L₁ B A G) :=
  SmoothConvexMollification.field_continuous _ (L₀ + L₁ * B)
    (field_lipschitz hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB)

lemma smooth_gradient (x : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (CompactMollification.average φ (objective L₀ L₁ B A G))
      (CompactMollification.average φ (field L₀ L₁ B A G) x) x :=
  SmoothConvexMollification.average_gradient φ _ _ (L₀ + L₁ * B)
    (objective_convex hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB)
    (objective_hasGradientAt hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB)
    (field_lipschitz hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB) x

lemma translated_pair (hδ : L₁ * φ.rOut ≤ 1 / 16)
    (x u v : EuclideanSpace ℝ (Fin m)) :
    ‖field L₀ L₁ B A G (x - noise φ u) - field L₀ L₁ B A G (x - noise φ v)‖ ≤
      (1 / 4 : ℝ) * (L₀ / L₁ + ‖field L₀ L₁ B A G (x - noise φ v)‖) := by
  have hr : L₁ * (2 * φ.rOut) < 1 := by linarith
  have hd : ‖(x - noise φ u) - (x - noise φ v)‖ ≤ 2 * φ.rOut := by
    rw [sub_sub_sub_cancel_left]
    have hh := norm_sub_le (noise φ v) (noise φ u)
    linarith [noise_norm φ u, noise_norm φ v]
  have hh := endpoint_to_local_pair (field L₀ L₁ B A G) L₀ L₁ (2 * φ.rOut)
    hL₀.le hL₁ hr (field_pair hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB) _ _ hd
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
  linarith

lemma smooth_curvature (hδ : L₁ * φ.rOut ≤ 1 / 16)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (CompactMollification.average φ (field L₀ L₁ B A G)) x‖ ≤
      (4 / 3 : ℝ) * (L₀ + L₁ * ‖CompactMollification.average φ (field L₀ L₁ B A G) x‖) := by
  have hcont := field_continuous hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB
  have hi := average_integrable φ _ hcont
  have hinc (y : EuclideanSpace ℝ (Fin m)) := averaged_endpoint_increment (probability φ)
    (noise φ) (field L₀ L₁ B A G) L₀ L₁ B (1 / 4) hL₁ (by norm_num)
    (field_norm_bound hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB)
    (field_pair hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB) hi
    (translated_pair hm φ L₀ L₁ B A hL₀ hL₁ G hG hB hGB hδ) x y
  have hd := ((average_contDiff φ _ hcont 1).differentiable (by norm_num) x).hasFDerivAt
  have hh := derivative_bound_of_quadratic_increment
    (CompactMollification.average φ (field L₀ L₁ B A G)) x _
    ((L₀ + L₁ * ‖CompactMollification.average φ (field L₀ L₁ B A G) x‖) / (1 - 1 / 4))
    (L₁ * (L₀ + L₁ * B)) hd (by positivity) (by positivity) hinc
  convert hh using 1
  ring

noncomputable def center : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2
  (fun i => -A - GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ B G i - φ.rOut)

lemma center_zero :
    CompactMollification.average φ (objective L₀ L₁ B A G) (center φ L₀ L₁ B A G) = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) :
      objective L₀ L₁ B A G (center φ L₀ L₁ B A G - noise φ z) = 0 := by
    apply objective_zero hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB
    intro i
    have hn := (abs_le.mp ((PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z))).1
    change -A - GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ B G i - φ.rOut -
      noise φ z i + A + GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ B G i ≤ 0
    linarith
  simp only [CompactMollification.average, hz, integral_zero]

lemma origin_gap (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ i, G i * (A + GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ B G i + φ.rOut) ≤ D) :
    CompactMollification.average φ (objective L₀ L₁ B A G) 0 ≤ D := by
  have hp (z : EuclideanSpace ℝ (Fin m)) : objective L₀ L₁ B A G (0 - noise φ z) ≤ D := by
    apply objective_upper hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB _ D hD
    intro i
    have hn := (abs_le.mp ((PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z))).1
    apply le_trans _ (hbound i)
    apply mul_le_mul_of_nonneg_left _ (hG i).le
    change 0 - noise φ z i + A + _ ≤ _
    linarith
  have hi := integral_mono
    (average_integrable φ _ (objective_continuous hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB) 0)
    (integrable_const D) hp
  simpa only [CompactMollification.average, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

lemma hidden_gap (τ : ℝ) (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (hx : -τ ≤ x i) :
    G i * (A + 2 / L₁ - τ - φ.rOut) ≤ CompactMollification.average φ (objective L₀ L₁ B A G) x := by
  have hp (z : EuclideanSpace ℝ (Fin m)) :
      G i * (A + 2 / L₁ - τ - φ.rOut) ≤ objective L₀ L₁ B A G (x - noise φ z) := by
    apply le_trans _ (objective_vertex_bound hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB i _)
    apply mul_le_mul_of_nonneg_left _ (hG i).le
    have hn := (abs_le.mp ((PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z))).2
    change A + 2 / L₁ - τ - φ.rOut ≤ x i - noise φ z i + A + 2 / L₁
    linarith
  have hi := integral_mono (integrable_const (G i * (A + 2 / L₁ - τ - φ.rOut)))
    (average_integrable φ _ (objective_continuous hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB) x) hp
  simpa only [CompactMollification.average, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

noncomputable def seed (M : ℝ) (hM : 0 < M) (hδ : L₁ * φ.rOut ≤ 1 / 16)
    (hcenter : ∀ i, |A + GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ B G i + φ.rOut| ≤ M) :
    AdaptiveGeneralizedSmoothLocalization.Seed (E := EuclideanSpace ℝ (Fin m)) where
  f := CompactMollification.average φ (objective L₀ L₁ B A G)
  g := CompactMollification.average φ (field L₀ L₁ B A G)
  z := center φ L₀ L₁ B A G
  G := B
  r := Real.sqrt m * M
  L₀ := 4 * L₀
  L₁ := 4 * L₁
  G_nonneg := hB
  r_pos := by positivity
  L₀_pos := by positivity
  L₁_pos := by positivity
  convex := average_convex φ _ (objective_continuous hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB)
    (objective_convex hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB)
  gradient := smooth_gradient hm φ L₀ L₁ B A hL₀ hL₁ G hG hB hGB
  differentiable := (average_contDiff φ _
    (field_continuous hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB) 1).differentiable (by norm_num)
  curvature := fun x => by
    have hh := smooth_curvature hm φ L₀ L₁ B A hL₀ hL₁ G hG hB hGB hδ x
    convert hh using 1
    ring
  bounded := average_norm_bound φ _ (field_continuous hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB) B
    (field_norm_bound hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB)
  nonnegative := fun x => integral_nonneg (fun z =>
    objective_nonnegative hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB (x - noise φ z))
  zero := center_zero hm φ L₀ L₁ B A hL₀ hL₁ G hG hB hGB
  radius := by
    apply GeneralizedSmoothHardChainRadius.norm_bound_of_coordinate_bound _ M hM.le
    intro i
    change |-A - GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ B G i - φ.rOut| ≤ M
    convert hcenter i using 1
    rw [show -A - GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ B G i - φ.rOut =
      -(A + GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ B G i + φ.rOut) by ring, abs_neg]

end LongTails.Proofs.GapCalibratedMollification
