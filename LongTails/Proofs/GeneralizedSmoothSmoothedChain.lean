import LongTails.Proofs.GeneralizedSmoothHardChain
import LongTails.Proofs.CompactMollification
import LongTails.Proofs.GeneralizedSmoothMollification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothSmoothedChain

open GeneralizedSmoothHardChain CompactMollification GeneralizedSmoothMollification

noncomputable def smoothObjective {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L₀ L₁ ε : ℝ) : EuclideanSpace ℝ (Fin m) → ℝ := average φ (objective m L₀ L₁ ε)

noncomputable def smoothField {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L₀ L₁ ε : ℝ) : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
  average φ (field m L₀ L₁ ε)

lemma objective_continuous {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) : Continuous (objective m L₀ L₁ ε) :=
  continuous_iff_continuousAt.mpr (fun x =>
    (objective_hasGradientAt hm L₀ L₁ ε hL₀ hL₁ hε x).differentiableAt.continuousAt)

lemma smooth_hasGradientAt {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (smoothObjective φ L₀ L₁ ε) (smoothField φ L₀ L₁ ε x) x := by
  exact average_hasGradient_of_remainder (probability φ) (noise φ) _ _
    (L₀ + L₁ * peak m L₁ ε)
    (average_integrable φ _ (objective_continuous hm L₀ L₁ ε hL₀ hL₁ hε))
    (average_integrable φ _ (field_lipschitz hm L₀ L₁ ε hL₀ hL₁ hε).continuous)
    (objective_remainder hm L₀ L₁ ε hL₀ hL₁ hε) x

lemma smooth_contDiff {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (n : ℕ∞) :
    ContDiff ℝ n (smoothObjective φ L₀ L₁ ε) :=
  average_contDiff φ _ (objective_continuous hm L₀ L₁ ε hL₀ hL₁ hε) n

lemma smoothField_contDiff {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (n : ℕ∞) :
    ContDiff ℝ n (smoothField φ L₀ L₁ ε) :=
  average_contDiff φ _ (field_lipschitz hm L₀ L₁ ε hL₀ hL₁ hε).continuous n

lemma smoothField_norm_bound {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    ‖smoothField φ L₀ L₁ ε x‖ ≤ peak m L₁ ε :=
  average_norm_bound φ _ (field_lipschitz hm L₀ L₁ ε hL₀ hL₁ hε).continuous _
    (field_norm_bound hm L₀ L₁ ε hL₀ hL₁ hε) x

lemma smooth_convex {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) :
    ConvexOn ℝ univ (smoothObjective φ L₀ L₁ ε) :=
  average_convex φ _ (objective_continuous hm L₀ L₁ ε hL₀ hL₁ hε)
    (objective_convex hm L₀ L₁ ε hL₀ hL₁ hε)

lemma smooth_nonnegative {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ smoothObjective φ L₀ L₁ ε x :=
  integral_nonneg (fun z => objective_nonnegative hm L₀ L₁ ε hL₀ hL₁ hε (x - noise φ z))

lemma translated_field_pair {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hδ : L₁ * φ.rOut ≤ 1 / 16)
    (x u v : EuclideanSpace ℝ (Fin m)) :
    ‖field m L₀ L₁ ε (x - noise φ u) - field m L₀ L₁ ε (x - noise φ v)‖ ≤
      (1 / 4 : ℝ) * (L₀ / L₁ + ‖field m L₀ L₁ ε (x - noise φ v)‖) := by
  have hr : L₁ * (2 * φ.rOut) < 1 := by linarith
  have hd : ‖(x - noise φ u) - (x - noise φ v)‖ ≤ 2 * φ.rOut := by
    rw [sub_sub_sub_cancel_left]
    have hh := norm_sub_le (noise φ v) (noise φ u)
    linarith [noise_norm φ u, noise_norm φ v]
  have hh := endpoint_to_local_pair (field m L₀ L₁ ε) L₀ L₁ (2 * φ.rOut)
    hL₀.le hL₁ hr (field_pair hm L₀ L₁ ε hL₀ hL₁ hε) _ _ hd
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
  linarith

lemma smooth_curvature {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hδ : L₁ * φ.rOut ≤ 1 / 16)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (smoothField φ L₀ L₁ ε) x‖ ≤
      (4 / 3 : ℝ) * (L₀ + L₁ * ‖smoothField φ L₀ L₁ ε x‖) := by
  have hcont := (field_lipschitz hm L₀ L₁ ε hL₀ hL₁ hε).continuous
  have hi := average_integrable φ _ hcont
  have hinc (y : EuclideanSpace ℝ (Fin m)) := averaged_endpoint_increment (probability φ)
    (noise φ) (field m L₀ L₁ ε) L₀ L₁ (peak m L₁ ε) (1 / 4) hL₁ (by norm_num)
    (field_norm_bound hm L₀ L₁ ε hL₀ hL₁ hε) (field_pair hm L₀ L₁ ε hL₀ hL₁ hε) hi
    (translated_field_pair hm φ L₀ L₁ ε hL₀ hL₁ hε hδ) x y
  have hd := ((smoothField_contDiff hm φ L₀ L₁ ε hL₀ hL₁ hε 1).differentiable
    (by norm_num)).differentiableAt.hasFDerivAt (x := x)
  have hpeak := peak_pos m L₁ ε hL₁ hε
  have hh := derivative_bound_of_quadratic_increment (smoothField φ L₀ L₁ ε) x _
    ((L₀ + L₁ * ‖smoothField φ L₀ L₁ ε x‖) / (1 - 1 / 4))
    (L₁ * (L₀ + L₁ * peak m L₁ ε)) hd (by positivity) (by positivity) hinc
  convert hh using 1
  ring

lemma noise_coordinate_bound {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) : |noise φ z i| ≤ φ.rOut :=
  (PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z)

lemma smooth_gap {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (hδ : φ.rOut ≤ 1 / (16 * L₁ * Real.sqrt m)) (i : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) (hx : -(1 / (16 * L₁ * Real.sqrt m)) ≤ x i) :
    15 * ε / 4 ≤ smoothObjective φ L₀ L₁ ε x := by
  have hp (z : EuclideanSpace ℝ (Fin m)) : 15 * ε / 4 ≤ objective m L₀ L₁ ε (x - noise φ z) := by
    apply objective_gap hm L₀ L₁ ε hL₀ hL₁ hε i
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).2
    change -(1 / (8 * L₁ * Real.sqrt m)) ≤ x i - noise φ z i
    have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
    rw [he]
    linarith
  have hh := integral_mono (integrable_const (15 * ε / 4))
    (average_integrable φ _ (objective_continuous hm L₀ L₁ ε hL₀ hL₁ hε) x) hp
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, smoothObjective, CompactMollification.average] using hh

noncomputable def center {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L₀ L₁ ε : ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => -GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ (peak m L₁ ε)
    (weight m L₁ ε) i - φ.rOut)

lemma smooth_center_zero {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) :
    smoothObjective φ L₀ L₁ ε (center φ L₀ L₁ ε) = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) :
      objective m L₀ L₁ ε (center φ L₀ L₁ ε - noise φ z) = 0 := by
    apply objective_zero hm L₀ L₁ ε hL₀ hL₁ hε
    intro i
    have hh := (abs_le.mp (noise_coordinate_bound φ z i)).1
    change -GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ (peak m L₁ ε)
      (weight m L₁ ε) i - φ.rOut - noise φ z i +
      GeneralizedSmoothHardTransfer.shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i ≤ 0
    linarith
  simp only [smoothObjective, CompactMollification.average, hz, integral_zero]

lemma smoothField_prefix_eq {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (hδ : φ.rOut ≤ 1 / (16 * L₁ * Real.sqrt m)) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(1 / (16 * L₁ * Real.sqrt m)) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ 1 / (16 * L₁ * Real.sqrt m))
    (hyt : ∀ i, j < i → y i ≤ 1 / (16 * L₁ * Real.sqrt m)) :
    smoothField φ L₀ L₁ ε x = smoothField φ L₀ L₁ ε y := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  apply field_prefix_eq hm L₀ L₁ ε hL₀ hL₁ hε j
  · intro i hi
    change x i - noise φ z i = y i - noise φ z i
    rw [hxy i hi]
  · have hz := (abs_le.mp (noise_coordinate_bound φ z j)).2
    change -(1 / (8 * L₁ * Real.sqrt m)) ≤ x j - noise φ z j
    have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
    rw [he]
    linarith
  · intro i hi
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).1
    have hx := hxt i hi
    change x i - noise φ z i ≤ 1 / (8 * L₁ * Real.sqrt m)
    have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
    rw [he]
    linarith
  · intro i hi
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).1
    have hy := hyt i hi
    change y i - noise φ z i ≤ 1 / (8 * L₁ * Real.sqrt m)
    have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
    rw [he]
    linarith

lemma smoothObjective_prefix_eq {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (hδ : φ.rOut ≤ 1 / (16 * L₁ * Real.sqrt m)) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(1 / (16 * L₁ * Real.sqrt m)) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ 1 / (16 * L₁ * Real.sqrt m))
    (hyt : ∀ i, j < i → y i ≤ 1 / (16 * L₁ * Real.sqrt m)) :
    smoothObjective φ L₀ L₁ ε x = smoothObjective φ L₀ L₁ ε y := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  apply objective_prefix_eq hm L₀ L₁ ε hL₀ hL₁ hε j
  · intro i hi
    change x i - noise φ z i = y i - noise φ z i
    rw [hxy i hi]
  · have hz := (abs_le.mp (noise_coordinate_bound φ z j)).2
    change -(1 / (8 * L₁ * Real.sqrt m)) ≤ x j - noise φ z j
    have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
    rw [he]
    linarith
  · intro i hi
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).1
    have hx := hxt i hi
    change x i - noise φ z i ≤ 1 / (8 * L₁ * Real.sqrt m)
    have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
    rw [he]
    linarith
  · intro i hi
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).1
    have hy := hyt i hi
    change y i - noise φ z i ≤ 1 / (8 * L₁ * Real.sqrt m)
    have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
    rw [he]
    linarith

lemma smoothField_tail_zero {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (hδ : φ.rOut ≤ 1 / (16 * L₁ * Real.sqrt m)) (j l : Fin m) (hjl : j < l)
    (x : EuclideanSpace ℝ (Fin m)) (hxj : -(1 / (16 * L₁ * Real.sqrt m)) ≤ x j)
    (hxl : x l ≤ 1 / (16 * L₁ * Real.sqrt m)) : smoothField φ L₀ L₁ ε x l = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) : field m L₀ L₁ ε (x - noise φ z) l = 0 := by
    apply field_tail_zero hm L₀ L₁ ε hL₀ hL₁ hε j l hjl
    · have hn := (abs_le.mp (noise_coordinate_bound φ z j)).2
      change -(1 / (8 * L₁ * Real.sqrt m)) ≤ x j - noise φ z j
      have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
      rw [he]
      linarith
    · have hn := (abs_le.mp (noise_coordinate_bound φ z l)).1
      change x l - noise φ z l ≤ 1 / (8 * L₁ * Real.sqrt m)
      have he : 1 / (8 * L₁ * Real.sqrt m) = 2 * (1 / (16 * L₁ * Real.sqrt m)) := by ring
      rw [he]
      linarith
  have hi := average_integrable φ _ (field_lipschitz hm L₀ L₁ ε hL₀ hL₁ hε).continuous x
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) l).integral_comp_comm hi
  change (∫ z, field m L₀ L₁ ε (x - noise φ z) l ∂(probability φ : Measure _)) =
    smoothField φ L₀ L₁ ε x l at hp
  rw [← hp]
  simp only [hz, integral_zero]

end LongTails.Proofs.GeneralizedSmoothSmoothedChain
