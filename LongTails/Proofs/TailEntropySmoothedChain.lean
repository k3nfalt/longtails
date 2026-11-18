import LongTails.Proofs.TailEntropyHardChain
import LongTails.Proofs.CompactMollification
import LongTails.Proofs.GeneralizedSmoothMollification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.TailEntropySmoothedChain

open TailEntropyHardChain CompactMollification GeneralizedSmoothMollification
open KnownGapChainWeights (peak peak_pos)

noncomputable def smoothObjective {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L₀ L₁ ε h : ℝ) : EuclideanSpace ℝ (Fin m) → ℝ := average φ (objective m L₀ L₁ ε h)

noncomputable def smoothField {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L₀ L₁ ε h : ℝ) : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
  average φ (field m L₀ L₁ ε h)

noncomputable def threshold (L₁ : ℝ) : ℝ := margin L₁ / 2

lemma threshold_pos (L₁ : ℝ) (hL₁ : 0 < L₁) : 0 < threshold L₁ := by
  unfold threshold margin
  positivity

lemma threshold_double (L₁ : ℝ) : margin L₁ = 2 * threshold L₁ := by
  unfold threshold; ring

section

variable {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
  (L₀ L₁ ε h : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 < h)

include hL₀ hL₁ hε hh

lemma objective_continuous : Continuous (objective m L₀ L₁ ε h) :=
  continuous_iff_continuousAt.mpr (fun x =>
    (objective_hasGradientAt (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh x).differentiableAt.continuousAt)

lemma smooth_hasGradientAt (x : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (smoothObjective φ L₀ L₁ ε h) (smoothField φ L₀ L₁ ε h x) x := by
  exact average_hasGradient_of_remainder (probability φ) (noise φ) _ _
    (L₀ + L₁ * peak m L₁ ε h)
    (average_integrable φ _ (objective_continuous (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh))
    (average_integrable φ _ (field_lipschitz (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh).continuous)
    (objective_remainder (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh) x

lemma smooth_contDiff (n : ℕ∞) : ContDiff ℝ n (smoothObjective φ L₀ L₁ ε h) :=
  average_contDiff φ _ (objective_continuous (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh) n

lemma smoothField_contDiff (n : ℕ∞) : ContDiff ℝ n (smoothField φ L₀ L₁ ε h) :=
  average_contDiff φ _ (field_lipschitz (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh).continuous n

lemma smoothField_norm_bound (x : EuclideanSpace ℝ (Fin m)) :
    ‖smoothField φ L₀ L₁ ε h x‖ ≤ peak m L₁ ε h :=
  average_norm_bound φ _ (field_lipschitz (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh).continuous _
    (field_norm_bound (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh) x

lemma smooth_convex : ConvexOn ℝ univ (smoothObjective φ L₀ L₁ ε h) :=
  average_convex φ _ (objective_continuous (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh)
    (objective_convex (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh)

lemma smooth_nonnegative (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ smoothObjective φ L₀ L₁ ε h x :=
  integral_nonneg (fun z => objective_nonnegative L₀ L₁ ε h hL₀ hL₁ hε hh (x - noise φ z))

lemma translated_field_pair (hδ : L₁ * φ.rOut ≤ 1 / 16)
    (x u v : EuclideanSpace ℝ (Fin m)) :
    ‖field m L₀ L₁ ε h (x - noise φ u) - field m L₀ L₁ ε h (x - noise φ v)‖ ≤
      (1 / 4 : ℝ) * (L₀ / L₁ + ‖field m L₀ L₁ ε h (x - noise φ v)‖) := by
  have hr : L₁ * (2 * φ.rOut) < 1 := by linarith
  have hd : ‖(x - noise φ u) - (x - noise φ v)‖ ≤ 2 * φ.rOut := by
    rw [sub_sub_sub_cancel_left]
    have hh' := norm_sub_le (noise φ v) (noise φ u)
    linarith [noise_norm φ u, noise_norm φ v]
  have hh' := endpoint_to_local_pair (field m L₀ L₁ ε h) L₀ L₁ (2 * φ.rOut)
    hL₀.le hL₁ hr (field_pair (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh) _ _ hd
  apply hh'.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
  linarith

lemma smooth_curvature (hδ : L₁ * φ.rOut ≤ 1 / 16) (x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (smoothField φ L₀ L₁ ε h) x‖ ≤
      (4 / 3 : ℝ) * (L₀ + L₁ * ‖smoothField φ L₀ L₁ ε h x‖) := by
  have hcont := (field_lipschitz (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh).continuous
  have hi := average_integrable φ _ hcont
  have hinc (y : EuclideanSpace ℝ (Fin m)) := averaged_endpoint_increment (probability φ)
    (noise φ) (field m L₀ L₁ ε h) L₀ L₁ (peak m L₁ ε h) (1 / 4) hL₁ (by norm_num)
    (field_norm_bound (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh) (field_pair (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh) hi
    (translated_field_pair (m := m) φ L₀ L₁ ε h hL₀ hL₁ hε hh hδ) x y
  have hd := ((smoothField_contDiff (m := m) φ L₀ L₁ ε h hL₀ hL₁ hε hh 1).differentiable
    (by norm_num)).differentiableAt.hasFDerivAt (x := x)
  have hpeak := peak_pos m L₁ ε h hL₁ hε
  have hh' := derivative_bound_of_quadratic_increment (smoothField φ L₀ L₁ ε h) x _
    ((L₀ + L₁ * ‖smoothField φ L₀ L₁ ε h x‖) / (1 - 1 / 4))
    (L₁ * (L₀ + L₁ * peak m L₁ ε h)) hd (by positivity) (by positivity) hinc
  convert hh' using 1
  ring

omit hL₀ hL₁ hε hh in
lemma noise_coordinate_bound (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    |noise φ z i| ≤ φ.rOut :=
  (PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z)

lemma smooth_gap (hh1 : h ≤ 1) (hδ : φ.rOut ≤ threshold L₁) (i : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) (hx : -(threshold L₁) ≤ x i) :
    252 * ε ≤ smoothObjective φ L₀ L₁ ε h x := by
  have hp (z : EuclideanSpace ℝ (Fin m)) : 252 * ε ≤ objective m L₀ L₁ ε h (x - noise φ z) := by
    apply objective_gap L₀ L₁ ε h hL₀ hL₁ hε hh hh1 i
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).2
    change -(margin L₁) ≤ x i - noise φ z i
    rw [threshold_double]
    linarith
  have hh' := integral_mono (integrable_const (252 * ε))
    (average_integrable φ _ (objective_continuous (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh) x) hp
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, smoothObjective,
    CompactMollification.average] using hh'

end

noncomputable def center {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L₀ L₁ ε h : ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun _ => -level m L₀ L₁ ε h - φ.rOut)

section

variable {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
  (L₀ L₁ ε h : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 < h)

include hL₀ hL₁ hε hh

lemma smooth_center_zero : smoothObjective φ L₀ L₁ ε h (center φ L₀ L₁ ε h) = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) :
      objective m L₀ L₁ ε h (center φ L₀ L₁ ε h - noise φ z) = 0 := by
    apply objective_zero L₀ L₁ ε h hL₀ hL₁ hε hh
    intro i
    have hh' := (abs_le.mp (noise_coordinate_bound φ z i)).1
    change -level m L₀ L₁ ε h - φ.rOut - noise φ z i + level m L₀ L₁ ε h ≤ 0
    linarith
  simp only [smoothObjective, CompactMollification.average, hz, integral_zero]

lemma smoothField_prefix_eq (hh1 : h ≤ 1) (hδ : φ.rOut ≤ threshold L₁) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(threshold L₁) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ threshold L₁)
    (hyt : ∀ i, j < i → y i ≤ threshold L₁) :
    smoothField φ L₀ L₁ ε h x = smoothField φ L₀ L₁ ε h y := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  apply field_prefix_eq L₀ L₁ ε h hL₀ hL₁ hε hh hh1 j
  · intro i hi
    change x i - noise φ z i = y i - noise φ z i
    rw [hxy i hi]
  · have hz := (abs_le.mp (noise_coordinate_bound φ z j)).2
    change -(margin L₁) ≤ x j - noise φ z j
    rw [threshold_double]
    linarith
  · intro i hi
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).1
    have hx := hxt i hi
    change x i - noise φ z i ≤ margin L₁
    rw [threshold_double]
    linarith
  · intro i hi
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).1
    have hy := hyt i hi
    change y i - noise φ z i ≤ margin L₁
    rw [threshold_double]
    linarith

lemma smoothObjective_prefix_eq (hh1 : h ≤ 1) (hδ : φ.rOut ≤ threshold L₁) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(threshold L₁) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ threshold L₁)
    (hyt : ∀ i, j < i → y i ≤ threshold L₁) :
    smoothObjective φ L₀ L₁ ε h x = smoothObjective φ L₀ L₁ ε h y := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  apply objective_prefix_eq L₀ L₁ ε h hL₀ hL₁ hε hh hh1 j
  · intro i hi
    change x i - noise φ z i = y i - noise φ z i
    rw [hxy i hi]
  · have hz := (abs_le.mp (noise_coordinate_bound φ z j)).2
    change -(margin L₁) ≤ x j - noise φ z j
    rw [threshold_double]
    linarith
  · intro i hi
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).1
    have hx := hxt i hi
    change x i - noise φ z i ≤ margin L₁
    rw [threshold_double]
    linarith
  · intro i hi
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).1
    have hy := hyt i hi
    change y i - noise φ z i ≤ margin L₁
    rw [threshold_double]
    linarith

lemma smoothField_tail_zero (hh1 : h ≤ 1) (hδ : φ.rOut ≤ threshold L₁) (j : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) (hxj : -(threshold L₁) ≤ x j)
    (hxt : ∀ l, j < l → x l ≤ threshold L₁) (l : Fin m) (hjl : j < l) :
    smoothField φ L₀ L₁ ε h x l = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) : field m L₀ L₁ ε h (x - noise φ z) l = 0 := by
    apply field_tail_zero L₀ L₁ ε h hL₀ hL₁ hε hh hh1 j _ _ _ l hjl
    · have hn := (abs_le.mp (noise_coordinate_bound φ z j)).2
      change -(margin L₁) ≤ x j - noise φ z j
      rw [threshold_double]
      linarith
    · intro i hi
      have hn := (abs_le.mp (noise_coordinate_bound φ z i)).1
      have hx := hxt i hi
      change x i - noise φ z i ≤ margin L₁
      rw [threshold_double]
      linarith
  have hi := average_integrable φ _ (field_lipschitz (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh).continuous x
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) l).integral_comp_comm hi
  change (∫ z, field m L₀ L₁ ε h (x - noise φ z) l ∂(probability φ : Measure _)) =
    smoothField φ L₀ L₁ ε h x l at hp
  rw [← hp]
  simp only [hz, integral_zero]

end

end LongTails.Proofs.TailEntropySmoothedChain
