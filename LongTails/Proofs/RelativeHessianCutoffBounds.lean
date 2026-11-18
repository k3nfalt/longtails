import LongTails.Proofs.RelativeHessianCutoffSpatial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.RelativeHessianCutoffBounds

open scoped RealInnerProductSpace
open RelativeHessianCutoffSpatial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma argument_gradient_bound {R : ℝ} (hR : 0 < R) (x : E) (hx : ‖x‖ ≤ 2 * R) :
    ‖gradient (argument R) x‖ ≤ 4 / R := by
  rw [argument_gradient, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 / R ^ 2)]
  calc
    _ ≤ (2 / R ^ 2) * (2 * R) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by field_simp; ring

omit [FiniteDimensional ℝ E] in
lemma argument_hessian_bound {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (gradient (argument R)) x‖ ≤ 2 / R ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [argument_hessian, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 / R ^ 2)]

lemma local_bounds {R : ℝ} (hR : 0 < R) (x : E) (hx : ‖x‖ ≤ 2 * R) :
    ‖gradient (value R) x‖ ≤ 2 ^ 32 / R ∧
    ‖fderiv ℝ (gradient (value R)) x‖ ≤ 2 ^ 32 / R ^ 2 ∧
    ‖fderiv ℝ (fderiv ℝ (gradient (value R))) x‖ ≤ 2 ^ 32 / R ^ 3 := by
  have hj := RelativeHessianCutoff.jet_bounds (argument R x)
  have hg := argument_gradient_bound hR x hx
  have hH := argument_hessian_bound hR x
  have hM : (0 : ℝ) ≤ 2 ^ 24 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · have he : gradient (value R) x = RelativeHessianCutoff.first (argument R x) • gradient (argument R) x := by
      unfold value
      exact ScalarCompositionJets.comp_gradient (argument_smooth R) RelativeHessianCutoff.profile_derivative x
    rw [he, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ 2 ^ 24 * (4 / R) := mul_le_mul hj.1 hg (norm_nonneg _) hM
      _ ≤ 2 ^ 32 / R := by apply (le_div_iff₀ hR).mpr; field_simp; norm_num
  · have h := ScalarCompositionJets.comp_hessian_norm (argument_smooth R) RelativeHessianCutoff.smooth
      RelativeHessianCutoff.profile_derivative RelativeHessianCutoff.first_derivative x
    change ‖fderiv ℝ (gradient (value R)) x‖ ≤ _ at h
    calc
      _ ≤ |RelativeHessianCutoff.first (argument R x)| * ‖fderiv ℝ (gradient (argument R)) x‖ +
          |RelativeHessianCutoff.second (argument R x)| * ‖gradient (argument R) x‖ ^ 2 := h
      _ ≤ 2 ^ 24 * (2 / R ^ 2) + 2 ^ 24 * (4 / R) ^ 2 := by
        gcongr <;> first | exact hj.1 | exact hj.2.1
      _ = 18 * 2 ^ 24 / R ^ 2 := by ring
      _ ≤ 2 ^ 32 / R ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg R)
  · have h := ScalarCompositionJets.comp_third_norm (argument_smooth R) RelativeHessianCutoff.smooth
      RelativeHessianCutoff.profile_derivative RelativeHessianCutoff.first_derivative
      RelativeHessianCutoff.second_derivative x
    change ‖fderiv ℝ (fderiv ℝ (gradient (value R))) x‖ ≤ _ at h
    have hz : ‖(0 : E →L[ℝ] E →L[ℝ] E)‖ = 0 := @norm_zero (E →L[ℝ] E →L[ℝ] E) _
    rw [argument_third, hz, mul_zero, zero_add] at h
    calc
      _ ≤ 3 * |RelativeHessianCutoff.second (argument R x)| * ‖gradient (argument R) x‖ *
          ‖fderiv ℝ (gradient (argument R)) x‖ +
          |RelativeHessianCutoff.third (argument R x)| * ‖gradient (argument R) x‖ ^ 3 := h
      _ ≤ 3 * 2 ^ 24 * (4 / R) * (2 / R ^ 2) + 2 ^ 24 * (4 / R) ^ 3 := by
        gcongr <;> first | exact hj.2.1 | exact hj.2.2
      _ = 88 * 2 ^ 24 / R ^ 3 := by ring
      _ ≤ 2 ^ 32 / R ^ 3 := div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hR.le _)

lemma bounds {R : ℝ} (hR : 0 < R) (x : E) :
    ‖gradient (value R) x‖ ≤ 2 ^ 32 / R ∧
    ‖fderiv ℝ (gradient (value R)) x‖ ≤ 2 ^ 32 / R ^ 2 ∧
    ‖fderiv ℝ (fderiv ℝ (gradient (value R))) x‖ ≤ 2 ^ 32 / R ^ 3 := by
  by_cases hx : ‖x‖ ≤ 2 * R
  · exact local_bounds hR x hx
  · obtain ⟨_, hg, hH, hT⟩ := outside_jets hR x (le_of_not_ge hx)
    have hz : ‖(0 : E →L[ℝ] E →L[ℝ] E)‖ = 0 := @norm_zero (E →L[ℝ] E →L[ℝ] E) _
    rw [hg, hH, hT, hz, norm_zero, norm_zero]
    exact ⟨by positivity, by positivity, by positivity⟩

end LongTails.Proofs.RelativeHessianCutoffBounds
