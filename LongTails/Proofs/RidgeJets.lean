import LongTails.Proofs.ScalarCompositionJets

namespace LongTails.Proofs.RidgeJets

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def value (φ : ℝ → ℝ) (a x : E) : ℝ := φ ⟪a, x⟫

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) (a : E) : ContDiff ℝ 3 (value φ a) :=
  hφ.comp (innerSL ℝ a).contDiff

omit [FiniteDimensional ℝ E] in
lemma gradient_eq {φ φ₁ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (a x : E) :
    gradient (value φ a) x = φ₁ ⟪a, x⟫ • a := by
  have h := (hφ ⟪a, x⟫).comp_hasFDerivAt x (innerSL ℝ a).hasFDerivAt
  have hh : HasGradientAt (value φ a) (φ₁ ⟪a, x⟫ • a) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    · funext y; rfl
    · ext v
      simp
  exact hh.gradient

omit [FiniteDimensional ℝ E] in
lemma hessian_apply {φ φ₁ φ₂ : ℝ → ℝ} (_hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (a x v : E) :
    fderiv ℝ (gradient (value φ a)) x v = (φ₂ ⟪a, x⟫ * ⟪a, v⟫) • a := by
  have he : gradient (value φ a) = fun y => φ₁ ⟪a, y⟫ • a := funext (gradient_eq hφ a)
  have h := ((hφ₁ ⟪a, x⟫).comp_hasFDerivAt x (innerSL ℝ a).hasFDerivAt).smul_const a
  rw [he]
  change (fderiv ℝ (fun y => (φ₁ ∘ inner ℝ a) y • a) x) v = _
  rw [h.fderiv]
  rfl

lemma third_apply {φ φ₁ φ₂ φ₃ : ℝ → ℝ} (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (hφ₂ : ∀ t, HasDerivAt φ₂ (φ₃ t) t) (a x u v : E) :
    fderiv ℝ (fderiv ℝ (gradient (value φ a))) x u v =
      (φ₃ ⟪a, x⟫ * ⟪a, u⟫ * ⟪a, v⟫) • a := by
  have hscalar := ScalarCompositionJets.along_line
    ((hφ₂ ⟪a, x⟫).comp_hasFDerivAt x (innerSL ℝ a).hasFDerivAt) u
  have h := (hscalar.mul_const ⟪a, v⟫).smul_const a
  have hcan := (ScalarCompositionJets.along_line
    ((GradientDependentLocal.derivative_chain (smooth hφc a)).2.2 x) u).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have he : (fun t : ℝ => fderiv ℝ (gradient (value φ a)) (x + t • u) v) =
      fun t => (φ₂ ⟪a, x + t • u⟫ * ⟪a, v⟫) • a :=
    funext (fun _ => hessian_apply hφc hφ hφ₁ a _ _)
  change HasDerivAt (fun t : ℝ => fderiv ℝ (gradient (value φ a)) (x + t • u) v) _ 0 at hcan
  rw [he] at hcan
  simpa using hcan.unique h

omit [FiniteDimensional ℝ E] in
lemma hessian_norm {φ φ₁ φ₂ : ℝ → ℝ} (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (a x : E) {M : ℝ} (hM : 0 ≤ M) (ha : ‖a‖ ≤ 1) (h₂ : |φ₂ ⟪a, x⟫| ≤ M) :
    ‖fderiv ℝ (gradient (value φ a)) x‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro u
  have hu : |⟪a, u⟫| ≤ ‖u‖ := (abs_real_inner_le_norm a u).trans
    (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg u))
  rw [hessian_apply hφc hφ hφ₁, norm_smul, Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul (mul_le_mul h₂ hu (abs_nonneg _) hM) ha
    (norm_nonneg a) (by positivity)).trans_eq (mul_one _)

lemma third_norm {φ φ₁ φ₂ φ₃ : ℝ → ℝ} (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (hφ₂ : ∀ t, HasDerivAt φ₂ (φ₃ t) t) (a x : E) {M : ℝ}
    (hM : 0 ≤ M) (ha : ‖a‖ ≤ 1) (h₃ : |φ₃ ⟪a, x⟫| ≤ M) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value φ a))) x‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hu : |⟪a, u⟫| ≤ ‖u‖ := (abs_real_inner_le_norm a u).trans
    (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg u))
  have hv : |⟪a, v⟫| ≤ ‖v‖ := (abs_real_inner_le_norm a v).trans
    (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg v))
  rw [third_apply hφc hφ hφ₁ hφ₂, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
  exact (mul_le_mul (mul_le_mul (mul_le_mul h₃ hu (abs_nonneg _) hM) hv
    (abs_nonneg _) (by positivity)) ha (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

lemma jet_bounds {φ φ₁ φ₂ φ₃ : ℝ → ℝ} (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (hφ₂ : ∀ t, HasDerivAt φ₂ (φ₃ t) t) (a x u v : E) {M U V : ℝ}
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : ‖a‖ ≤ 1)
    (hu : |⟪a, u⟫| ≤ U) (hv : |⟪a, v⟫| ≤ V)
    (h₀ : |φ ⟪a, x⟫| ≤ M) (h₁ : |φ₁ ⟪a, x⟫| ≤ M)
    (h₂ : |φ₂ ⟪a, x⟫| ≤ M) (h₃ : |φ₃ ⟪a, x⟫| ≤ M) :
    |value φ a x| ≤ M ∧ ‖gradient (value φ a) x‖ ≤ M ∧
    |⟪gradient (value φ a) x, u⟫| ≤ M * U ∧
    |⟪gradient (value φ a) x, v⟫| ≤ M * V ∧
    ‖fderiv ℝ (gradient (value φ a)) x u‖ ≤ M * U ∧
    ‖fderiv ℝ (gradient (value φ a)) x v‖ ≤ M * V ∧
    |⟪fderiv ℝ (gradient (value φ a)) x u, v⟫| ≤ M * U * V ∧
    ‖fderiv ℝ (fderiv ℝ (gradient (value φ a))) x u v‖ ≤ M * U * V := by
  have hmul {c : ℝ} (hc : |c| ≤ M) {z : ℝ} {W : ℝ} (hz : |z| ≤ W) :
      |c| * |z| ≤ M * W := mul_le_mul hc hz (abs_nonneg z) hM
  have hmul₂ {c : ℝ} (hc : |c| ≤ M) :
      |c| * |⟪a, u⟫| * |⟪a, v⟫| ≤ M * U * V :=
    mul_le_mul (hmul hc hu) hv (abs_nonneg _) (mul_nonneg hM hU)
  refine ⟨h₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gradient_eq hφ, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul h₁ ha (norm_nonneg a) hM).trans_eq (mul_one M)
  · simpa [gradient_eq hφ, real_inner_smul_left, abs_mul] using hmul h₁ hu
  · simpa [gradient_eq hφ, real_inner_smul_left, abs_mul] using hmul h₁ hv
  · rw [hessian_apply hφc hφ hφ₁, norm_smul, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (hmul h₂ hu) ha (norm_nonneg a) (mul_nonneg hM hU)).trans_eq (mul_one _)
  · rw [hessian_apply hφc hφ hφ₁, norm_smul, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (hmul h₂ hv) ha (norm_nonneg a) (mul_nonneg hM hV)).trans_eq (mul_one _)
  · simpa [hessian_apply hφc hφ hφ₁, real_inner_smul_left, abs_mul] using hmul₂ h₂
  · rw [third_apply hφc hφ hφ₁ hφ₂, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
    exact (mul_le_mul (hmul₂ h₃) ha (norm_nonneg a) (by positivity)).trans_eq (mul_one _)

end LongTails.Proofs.RidgeJets
