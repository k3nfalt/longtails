import LongTails.Algorithms.StochasticEqualityDirection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

namespace LongTails.Proofs.StochasticEqualityGeometry

open LongTails.Algorithms.StochasticEqualityDirection
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma injective_of_regular {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) : Function.Injective J := by
  apply (injective_iff_map_eq_zero J).mpr
  intro v hv
  have h := hJ v
  rw [hv, norm_zero] at h
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp this

lemma regular_perturbation {ν δ : ℝ} {J K : F →L[ℝ] E}
    (hJ : regular ν J) (hδ : ‖K - J‖ ≤ δ) : regular (ν - δ) K := by
  intro v
  have h₁ := (K - J).le_opNorm v
  have h₂ := norm_sub_norm_le (J v) (K v)
  have h₃ := mul_le_mul_of_nonneg_right hδ (norm_nonneg v)
  rw [sub_apply, norm_sub_rev] at h₁
  nlinarith only [hJ v, h₁, h₂, h₃]

lemma error_of_rejected {ν : ℝ} {J K : F →L[ℝ] E}
    (hJ : regular ν J) (hK : ¬regular (ν / 2) K) : ν / 2 < ‖K - J‖ := by
  by_contra h
  have hh := regular_perturbation hJ (not_lt.mp h)
  have he : ν - ν / 2 = ν / 2 := by ring
  exact hK (he ▸ hh)

variable [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ F]

lemma gram_isUnit {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) : IsUnit (J.adjoint.comp J) := by
  have hi := J.adjoint_comp_self_injective_iff.mpr (injective_of_regular hν hJ)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

lemma normal_equation {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) (g : E) : J.adjoint (tangent J g) = 0 := by
  have h := congrArg (fun A : F →L[ℝ] F => A (J.adjoint g))
    (Ring.mul_inverse_cancel (J.adjoint.comp J) (gram_isUnit hν hJ))
  simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
    one_apply_eq_self] at h
  simp only [tangent, multiplier, map_add, map_neg]
  rw [h, add_neg_cancel]

lemma tangent_orthogonal {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) (g : E) (v : F) : ⟪tangent J g, J v⟫ = 0 := by
  rw [← J.adjoint_inner_left, normal_equation hν hJ, inner_zero_left]

lemma tangent_pythagoras {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) (g : E) :
    ‖g‖ ^ 2 = ‖tangent J g‖ ^ 2 + ‖J (multiplier J g)‖ ^ 2 := by
  have h := norm_sub_sq_real (tangent J g) (J (multiplier J g))
  rw [tangent_orthogonal hν hJ, mul_zero, sub_zero] at h
  simpa only [tangent, add_sub_cancel_right] using h

lemma norm_tangent_le {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) (g : E) : ‖tangent J g‖ ≤ ‖g‖ := by
  have h := tangent_pythagoras hν hJ g
  nlinarith [norm_nonneg g, norm_nonneg (tangent J g),
    sq_nonneg ‖J (multiplier J g)‖]

lemma norm_tangent_le_shift {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) (g : E) (v : F) : ‖tangent J g‖ ≤ ‖g + J v‖ := by
  have he : g + J v = tangent J g + J (v - multiplier J g) := by
    simp only [tangent, map_sub]
    abel
  have h := norm_add_sq_real (tangent J g) (J (v - multiplier J g))
  rw [tangent_orthogonal hν hJ, mul_zero, add_zero] at h
  rw [he]
  nlinarith [norm_nonneg (tangent J g), norm_nonneg (tangent J g + J (v - multiplier J g)),
    sq_nonneg ‖J (v - multiplier J g)‖]

lemma norm_multiplier_le {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) (g : E) : ‖multiplier J g‖ ≤ ‖g‖ / ν := by
  have h := tangent_pythagoras hν hJ g
  have hb : ‖J (multiplier J g)‖ ≤ ‖g‖ := by
    nlinarith [norm_nonneg g, norm_nonneg (J (multiplier J g)),
      sq_nonneg ‖tangent J g‖]
  apply (le_div_iff₀ hν).mpr
  nlinarith [hJ (multiplier J g)]

lemma norm_thresholded_tangent_le (ν : ℝ) (hν : 0 < ν)
    (J : F →L[ℝ] E) (g : E) :
    ‖g + J (thresholdedMultiplier ν J g)‖ ≤ ‖g‖ := by
  classical
  by_cases hJ : regular (ν / 2) J
  · simpa only [thresholdedMultiplier, ite_eq_left hJ, tangent] using
      norm_tangent_le (half_pos hν) hJ g
  · simp only [thresholdedMultiplier, ite_eq_right hJ, map_zero, add_zero, le_refl]

lemma norm_direction_le (ν : ℝ) (hν : 0 < ν)
    (J : F →L[ℝ] E) (g : E) (c : F) :
    ‖direction ν J g c‖ ≤ ‖g‖ + ‖J‖ * ‖c‖ := by
  calc
    ‖direction ν J g c‖ ≤ ‖g + J (thresholdedMultiplier ν J g)‖ + ‖J c‖ := by
      simpa only [direction, norm_neg] using
        norm_sub_le (-(g + J (thresholdedMultiplier ν J g))) (J c)
    _ ≤ ‖g‖ + ‖J‖ * ‖c‖ := add_le_add
      (norm_thresholded_tangent_le ν hν J g) (J.le_opNorm c)

omit [FiniteDimensional ℝ F] in
lemma gram_regular {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) : regular (ν ^ 2) (J.adjoint.comp J) := by
  intro v
  have hi := real_inner_le_norm (J.adjoint (J v)) v
  rw [J.adjoint_inner_left, real_inner_self_eq_norm_sq] at hi
  have hj := hJ v
  have hn := norm_nonneg v
  have hjn := norm_nonneg (J v)
  by_cases hv : ‖v‖ = 0
  · simp only [hv, mul_zero, norm_nonneg]
  · have hvp : 0 < ‖v‖ := lt_of_le_of_ne hn (Ne.symm hv)
    have hs : (ν * ‖v‖) ^ 2 ≤ ‖J v‖ ^ 2 := sq_le_sq₀ (by positivity) hjn |>.mpr hj
    change ν ^ 2 * ‖v‖ ≤ ‖J.adjoint (J v)‖
    nlinarith

lemma multiplier_residual_bound {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) (g : E) (v : F) :
    ν ^ 2 * ‖multiplier J g - v‖ ≤ ‖J.adjoint (g + J v)‖ := by
  have h := gram_regular hν hJ (multiplier J g - v)
  have hn := normal_equation hν hJ g
  change J.adjoint (g + J (multiplier J g)) = 0 at hn
  simp only [map_add] at hn
  have he : J.adjoint (J (multiplier J g)) = -J.adjoint g := by
    exact eq_neg_of_add_eq_zero_right hn
  have heq : (J.adjoint.comp J) (multiplier J g - v) =
      -J.adjoint (g + J v) := by
    simp only [ContinuousLinearMap.comp_apply, map_sub, he, map_add]
    abel
  rw [heq, norm_neg] at h
  exact h

lemma perturbed_normal_residual {ν : ℝ} (hν : 0 < ν) {J : F →L[ℝ] E}
    (hJ : regular ν J) (K : F →L[ℝ] E) (g h : E) :
    ‖K.adjoint (h + K (multiplier J g))‖ ≤
      ‖K‖ * (‖h - g‖ + ‖K - J‖ * ‖multiplier J g‖) +
      ‖K - J‖ * ‖tangent J g‖ := by
  have he : K.adjoint (h + K (multiplier J g)) =
      K.adjoint ((h - g) + (K - J) (multiplier J g)) +
      (K.adjoint - J.adjoint) (tangent J g) := by
    have hn := normal_equation hν hJ g
    change _ = _ + (K.adjoint (tangent J g) - J.adjoint (tangent J g))
    rw [hn, sub_zero]
    simp only [sub_apply, map_add, map_sub, tangent]
    abel
  rw [he]
  calc
    _ ≤ ‖K.adjoint ((h - g) + (K - J) (multiplier J g))‖ +
        ‖(K.adjoint - J.adjoint) (tangent J g)‖ := norm_add_le _ _
    _ ≤ ‖K.adjoint‖ * ‖(h - g) + (K - J) (multiplier J g)‖ +
        ‖K.adjoint - J.adjoint‖ * ‖tangent J g‖ :=
      add_le_add (K.adjoint.le_opNorm _) ((K.adjoint - J.adjoint).le_opNorm _)
    _ ≤ ‖K‖ * (‖h - g‖ + ‖K - J‖ * ‖multiplier J g‖) +
        ‖K - J‖ * ‖tangent J g‖ := by
      rw [← map_sub ContinuousLinearMap.adjoint, ContinuousLinearMap.adjoint.norm_map,
        ContinuousLinearMap.adjoint.norm_map]
      exact add_le_add (mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add le_rfl ((K - J).le_opNorm _)))
        (norm_nonneg K)) le_rfl

lemma multiplier_perturbation {ν μ : ℝ} (hν : 0 < ν) (hμ : 0 < μ)
    {J K : F →L[ℝ] E} (hJ : regular ν J) (hK : regular μ K) (g h : E) :
    μ ^ 2 * ‖multiplier K h - multiplier J g‖ ≤
      ‖K‖ * (‖h - g‖ + ‖K - J‖ * (‖g‖ / ν)) + ‖K - J‖ * ‖g‖ := by
  apply (multiplier_residual_bound hμ hK h (multiplier J g)).trans
  apply (perturbed_normal_residual hν hJ K g h).trans
  gcongr
  · exact norm_multiplier_le hν hJ g
  · exact norm_tangent_le hν hJ g

omit [FiniteDimensional ℝ F] in
lemma tangent_difference_bound (J K : F →L[ℝ] E) (g h : E) :
    ‖tangent K h - tangent J g‖ ≤ ‖h - g‖ +
      ‖K - J‖ * ‖multiplier J g‖ + ‖K‖ * ‖multiplier K h - multiplier J g‖ := by
  have he : tangent K h - tangent J g =
      (h - g) + (K - J) (multiplier J g) + K (multiplier K h - multiplier J g) := by
    simp only [tangent, sub_apply, map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl ((K - J).le_opNorm _)))
    (K.le_opNorm _))

lemma regular_tangent_error {ν μ : ℝ} (hν : 0 < ν) (hμ : 0 < μ)
    {J K : F →L[ℝ] E} (hJ : regular ν J) (hK : regular μ K) (g h : E) :
    ‖tangent K h - tangent J g‖ ≤ ‖h - g‖ + ‖K - J‖ * (‖g‖ / ν) +
      ‖K‖ * ((‖K‖ * (‖h - g‖ + ‖K - J‖ * (‖g‖ / ν)) +
        ‖K - J‖ * ‖g‖) / μ ^ 2) := by
  apply (tangent_difference_bound J K g h).trans
  apply add_le_add
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (norm_multiplier_le hν hJ g) (norm_nonneg _))
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg K)
    apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
    simpa only [mul_comm] using multiplier_perturbation hν hμ hJ hK g h

lemma norm_thresholdedMultiplier_le (ν : ℝ) (hν : 0 < ν)
    (J : F →L[ℝ] E) (g : E) :
    ‖thresholdedMultiplier ν J g‖ ≤ 2 * ‖g‖ / ν := by
  classical
  by_cases hJ : regular (ν / 2) J
  · simp only [thresholdedMultiplier, ite_eq_left hJ]
    convert norm_multiplier_le (half_pos hν) hJ g using 1; ring
  · simp only [thresholdedMultiplier, ite_eq_right hJ, norm_zero]
    positivity

lemma rejected_tangent_error {ν G : ℝ} (hν : 0 < ν) {J K : F →L[ℝ] E}
    (hJ : regular ν J) (hK : ¬regular (ν / 2) K) {g h : E}
    (hg : ‖g‖ ≤ G) (hh : ‖h‖ ≤ G) :
    ‖h + K (thresholdedMultiplier ν K h) - tangent J g‖ ≤
      4 * G / ν * ‖K - J‖ := by
  classical
  simp only [thresholdedMultiplier, ite_eq_right hK, map_zero, add_zero]
  have hb : ‖h - tangent J g‖ ≤ 2 * G := by
    have ht := norm_tangent_le hν hJ g
    have htri := norm_sub_le h (tangent J g)
    linarith
  apply hb.trans
  have he := error_of_rejected hJ hK
  have hG : 0 ≤ G := (norm_nonneg g).trans hg
  have hm := mul_le_mul_of_nonneg_left he.le (show 0 ≤ 4 * G by positivity)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hν).mpr
  nlinarith only [hm]

lemma thresholded_tangent_error {ν G L : ℝ} (hν : 0 < ν) {J K : F →L[ℝ] E}
    (hJ : regular ν J) {g h : E} (hg : ‖g‖ ≤ G) (hh : ‖h‖ ≤ G)
    (hL : ‖K‖ ≤ L) :
    ‖h + K (thresholdedMultiplier ν K h) - tangent J g‖ ≤
      (1 + 4 * L ^ 2 / ν ^ 2) * ‖h - g‖ +
      ((1 + 4 * L ^ 2 / ν ^ 2) * G / ν + 4 * L * G / ν ^ 2 + 4 * G / ν) *
        ‖K - J‖ := by
  classical
  have hG : 0 ≤ G := (norm_nonneg g).trans hg
  have hL0 : 0 ≤ L := (norm_nonneg K).trans hL
  by_cases hK : regular (ν / 2) K
  · simp only [thresholdedMultiplier, ite_eq_left hK]
    change ‖tangent K h - tangent J g‖ ≤ _
    have hb := regular_tangent_error hν (half_pos hν) hJ hK g h
    have hc : ‖h - g‖ + ‖K - J‖ * (‖g‖ / ν) +
        ‖K‖ * ((‖K‖ * (‖h - g‖ + ‖K - J‖ * (‖g‖ / ν)) +
          ‖K - J‖ * ‖g‖) / (ν / 2) ^ 2) ≤
        ‖h - g‖ + ‖K - J‖ * (G / ν) +
        L * ((L * (‖h - g‖ + ‖K - J‖ * (G / ν)) + ‖K - J‖ * G) / (ν / 2) ^ 2) := by
      gcongr
    apply (hb.trans hc).trans
    have he : ‖h - g‖ + ‖K - J‖ * (G / ν) +
        L * ((L * (‖h - g‖ + ‖K - J‖ * (G / ν)) + ‖K - J‖ * G) / (ν / 2) ^ 2) =
        (1 + 4 * L ^ 2 / ν ^ 2) * ‖h - g‖ +
        ((1 + 4 * L ^ 2 / ν ^ 2) * G / ν + 4 * L * G / ν ^ 2) * ‖K - J‖ := by
      field_simp
      ring
    rw [he]
    have hp : 0 ≤ 4 * G / ν * ‖K - J‖ := by positivity
    nlinarith only [hp]
  · apply (rejected_tangent_error hν hJ hK hg hh).trans
    have h₁ : 0 ≤ (1 + 4 * L ^ 2 / ν ^ 2) * ‖h - g‖ := by positivity
    have h₂ : 0 ≤ ((1 + 4 * L ^ 2 / ν ^ 2) * G / ν + 4 * L * G / ν ^ 2) * ‖K - J‖ := by positivity
    nlinarith only [h₁, h₂]

omit [FiniteDimensional ℝ F] in
lemma direction_error_bound (ν : ℝ) (J K : F →L[ℝ] E) (g h : E) (c v : F) :
    ‖direction ν K h v - (-tangent J g - J c)‖ ≤
      ‖h + K (thresholdedMultiplier ν K h) - tangent J g‖ +
      ‖K‖ * ‖v - c‖ + ‖K - J‖ * ‖c‖ := by
  have he : direction ν K h v - (-tangent J g - J c) =
      -(h + K (thresholdedMultiplier ν K h) - tangent J g) -
        K (v - c) - (K - J) c := by
    simp only [direction, map_sub, sub_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖-(h + K (thresholdedMultiplier ν K h) - tangent J g) - K (v - c)‖ +
        ‖(K - J) c‖ := norm_sub_le _ _
    _ ≤ (‖h + K (thresholdedMultiplier ν K h) - tangent J g‖ + ‖K (v - c)‖) +
        ‖(K - J) c‖ := by
      simpa only [norm_neg] using add_le_add (norm_sub_le
        (-(h + K (thresholdedMultiplier ν K h) - tangent J g)) (K (v - c))) le_rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl (K.le_opNorm _)) ((K - J).le_opNorm _)

lemma multiplier_field_lipschitz {ν G Lc Lf LJ : ℝ} (hν : 0 < ν)
    {J : E → F →L[ℝ] E} {g : E → E}
    (hJ : ∀ x, regular ν (J x)) (hJn : ∀ x, ‖J x‖ ≤ Lc)
    (hgL : ∀ x y, ‖g y - g x‖ ≤ Lf * ‖y - x‖)
    (hJL : ∀ x y, ‖J y - J x‖ ≤ LJ * ‖y - x‖) (x y : E)
    (hgn : ‖g x‖ ≤ G) :
    ‖multiplier (J y) (g y) - multiplier (J x) (g x)‖ ≤
      ((Lc * Lf + Lc * LJ * G / ν + LJ * G) / ν ^ 2) * ‖y - x‖ := by
  have hG : 0 ≤ G := (norm_nonneg (g x)).trans hgn
  have hLc : 0 ≤ Lc := (norm_nonneg (J y)).trans (hJn y)
  have hbase := multiplier_perturbation hν hν (hJ x) (hJ y) (g x) (g y)
  have hbound : ‖J y‖ * (‖g y - g x‖ + ‖J y - J x‖ * (‖g x‖ / ν)) +
      ‖J y - J x‖ * ‖g x‖ ≤
      Lc * (Lf * ‖y - x‖ + LJ * ‖y - x‖ * (G / ν)) + LJ * ‖y - x‖ * G := by
    have hD0 : 0 ≤ LJ * ‖y - x‖ := (norm_nonneg _).trans (hJL x y)
    gcongr <;> first | exact hJn y | exact hgL x y | exact hJL x y
  have hdiv := (le_div_iff₀ (sq_pos_of_pos hν)).mpr
    (show ‖multiplier (J y) (g y) - multiplier (J x) (g x)‖ * ν ^ 2 ≤ _ by
      simpa only [mul_comm] using hbase.trans hbound)
  convert hdiv using 1; ring

end LongTails.Proofs.StochasticEqualityGeometry
