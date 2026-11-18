import LongTails.Proofs.RelativeHessianCutoff
import LongTails.Proofs.RelativeHessianGuard

namespace LongTails.Proofs.RelativeHessianCutoffSpatial

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def argument (R : ℝ) (x : E) : ℝ :=
  FullGeneralizedSmoothZeroQuery.quadratic (2 / R ^ 2) 0 x

noncomputable def value (R : ℝ) : E → ℝ := RelativeHessianCutoff.profile ∘ argument R

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma argument_eq (R : ℝ) (x : E) : argument R x = ‖x‖ ^ 2 / R ^ 2 := by
  simp only [argument, FullGeneralizedSmoothZeroQuery.quadratic, sub_zero]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma argument_smooth (R : ℝ) : ContDiff ℝ 3 (argument (E := E) R) :=
  RelativeHessianGuard.quadratic_smooth _

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smooth (R : ℝ) : ContDiff ℝ 3 (value (E := E) R) :=
  RelativeHessianCutoff.smooth.comp (argument_smooth R)

omit [FiniteDimensional ℝ E] in
lemma argument_gradient (R : ℝ) (x : E) : gradient (argument R) x = (2 / R ^ 2) • x :=
  RelativeHessianGuard.quadratic_gradient _ _

omit [FiniteDimensional ℝ E] in
lemma argument_hessian (R : ℝ) (x u : E) : fderiv ℝ (gradient (argument R)) x u = (2 / R ^ 2) • u := by
  have he : gradient (argument (E := E) R) = fun y => (2 / R ^ 2) • y := funext (argument_gradient R)
  rw [he]
  change (fderiv ℝ ((2 / R ^ 2) • (id : E → E)) x) u = _
  rw [((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (2 / R ^ 2)).fderiv]
  rfl

omit [FiniteDimensional ℝ E] in
lemma argument_third (R : ℝ) (x : E) : fderiv ℝ (fderiv ℝ (gradient (argument R))) x = 0 :=
  RelativeHessianGuard.quadratic_third _ _

lemma gradient_eq (R : ℝ) (x : E) : gradient (value R) x =
    RelativeHessianCutoff.first (argument R x) • ((2 / R ^ 2) • x) := by
  unfold value
  rw [ScalarCompositionJets.comp_gradient (argument_smooth R) RelativeHessianCutoff.profile_derivative,
    argument_gradient]

lemma hessian_apply (R : ℝ) (x u : E) : fderiv ℝ (gradient (value R)) x u =
    RelativeHessianCutoff.first (argument R x) • ((2 / R ^ 2) • u) +
    (RelativeHessianCutoff.second (argument R x) * ⟪(2 / R ^ 2) • x, u⟫) • ((2 / R ^ 2) • x) := by
  unfold value
  rw [ScalarCompositionJets.comp_hessian_apply (argument_smooth R) RelativeHessianCutoff.smooth
    RelativeHessianCutoff.profile_derivative RelativeHessianCutoff.first_derivative,
    argument_gradient, argument_hessian]

lemma third_apply (R : ℝ) (x u w : E) : fderiv ℝ (fderiv ℝ (gradient (value R))) x u w =
    (RelativeHessianCutoff.second (argument R x) * ⟪(2 / R ^ 2) • x, u⟫) • ((2 / R ^ 2) • w) +
    (RelativeHessianCutoff.second (argument R x) * ⟪(2 / R ^ 2) • x, w⟫) • ((2 / R ^ 2) • u) +
    (RelativeHessianCutoff.third (argument R x) * ⟪(2 / R ^ 2) • x, u⟫ * ⟪(2 / R ^ 2) • x, w⟫ +
      RelativeHessianCutoff.second (argument R x) * ⟪(2 / R ^ 2) • u, w⟫) • ((2 / R ^ 2) • x) := by
  unfold value
  rw [ScalarCompositionJets.comp_third_apply (argument_smooth R) RelativeHessianCutoff.smooth
    RelativeHessianCutoff.profile_derivative RelativeHessianCutoff.first_derivative
    RelativeHessianCutoff.second_derivative, argument_gradient, argument_hessian, argument_third]
  simp [argument_hessian]

lemma zero_jets (R : ℝ) (x : E)
    (h : RelativeHessianCutoff.first (argument R x) = 0 ∧
      RelativeHessianCutoff.second (argument R x) = 0 ∧ RelativeHessianCutoff.third (argument R x) = 0) :
    gradient (value R) x = 0 ∧ fderiv ℝ (gradient (value R)) x = 0 ∧
      fderiv ℝ (fderiv ℝ (gradient (value R))) x = 0 := by
  refine ⟨by simp [gradient_eq, h.1], ?_, ?_⟩
  · ext u
    simp [hessian_apply, h.1, h.2.1]
  · ext u w
    simp [third_apply, h.2.1, h.2.2]

lemma inside_jets {R : ℝ} (hR : 0 < R) (x : E) (hx : ‖x‖ ≤ R) :
    value R x = 1 ∧ gradient (value R) x = 0 ∧ fderiv ℝ (gradient (value R)) x = 0 ∧
      fderiv ℝ (fderiv ℝ (gradient (value R))) x = 0 := by
  have hq : argument R x ≤ 1 := by
    rw [argument_eq, div_le_one (sq_pos_of_pos hR)]
    exact pow_le_pow_left₀ (norm_nonneg x) hx 2
  have h := RelativeHessianCutoff.flat hq
  exact ⟨h.1, zero_jets R x h.2⟩

lemma outside_jets {R : ℝ} (hR : 0 < R) (x : E) (hx : 2 * R ≤ ‖x‖) :
    value R x = 0 ∧ gradient (value R) x = 0 ∧ fderiv ℝ (gradient (value R)) x = 0 ∧
      fderiv ℝ (fderiv ℝ (gradient (value R))) x = 0 := by
  have hq : 4 ≤ argument R x := by
    rw [argument_eq, le_div_iff₀ (sq_pos_of_pos hR)]
    nlinarith [sq_nonneg (‖x‖ - 2 * R)]
  have h := RelativeHessianCutoff.outside hq
  exact ⟨h.1, zero_jets R x h.2⟩

end LongTails.Proofs.RelativeHessianCutoffSpatial
