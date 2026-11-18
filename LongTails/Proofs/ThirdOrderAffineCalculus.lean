import LongTails.Proofs.GradientDependentLocal

set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.ThirdOrderAffineCalculus

open Filter
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma norm_smul_tensor_le (c : ℝ) (T : E →L[ℝ] E →L[ℝ] E) : ‖c • T‖ ≤ |c| * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  calc
    _ = |c| * ‖T u v‖ := by simp only [smul_apply, norm_smul, Real.norm_eq_abs]
    _ ≤ |c| * (‖T‖ * ‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left
      (((T u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (T.le_opNorm u) (norm_nonneg v)))
      (abs_nonneg c)
    _ = _ := by ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma norm_smul_operator_le (c : ℝ) (T : E →L[ℝ] E) : ‖c • T‖ ≤ |c| * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  calc
    _ = |c| * ‖T u‖ := by simp only [smul_apply, norm_smul, Real.norm_eq_abs]
    _ ≤ |c| * (‖T‖ * ‖u‖) := mul_le_mul_of_nonneg_left (T.le_opNorm u) (abs_nonneg c)
    _ = _ := by ring

lemma combination_gradient {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (a b : ℝ) (x : E) :
    gradient (fun z => a * f z + b * g z) x = a • gradient f x + b • gradient g x := by
  have h := (((GradientDependentLocal.derivative_chain hf).1 x).const_mul a).add
    (((GradientDependentLocal.derivative_chain hg).1 x).const_mul b)
  have hh : HasGradientAt (fun z => a * f z + b * g z)
      (a • gradient f x + b • gradient g x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext u
    simp
  exact hh.gradient

lemma combination_hessian {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (a b : ℝ) (x : E) :
    fderiv ℝ (gradient (fun z => a * f z + b * g z)) x =
      a • fderiv ℝ (gradient f) x + b • fderiv ℝ (gradient g) x := by
  have he : gradient (fun z => a * f z + b * g z) =
      fun z => a • gradient f z + b • gradient g z := funext (combination_gradient hf hg a b)
  rw [he]
  exact ((((GradientDependentLocal.derivative_chain hf).2.1 x).const_smul a).add
    (((GradientDependentLocal.derivative_chain hg).2.1 x).const_smul b)).fderiv

lemma combination_third {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (a b : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun z => a * f z + b * g z))) x =
      a • fderiv ℝ (fderiv ℝ (gradient f)) x + b • fderiv ℝ (fderiv ℝ (gradient g)) x := by
  have he : fderiv ℝ (gradient (fun z => a * f z + b * g z)) =
      fun z => a • fderiv ℝ (gradient f) z + b • fderiv ℝ (gradient g) z :=
    funext (combination_hessian hf hg a b)
  rw [he]
  exact ((((GradientDependentLocal.derivative_chain hf).2.2 x).const_smul a).add
    (((GradientDependentLocal.derivative_chain hg).2.2 x).const_smul b)).fderiv

lemma sum_gradient {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ 3 (f i)) (x : E) :
    gradient (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, gradient (f i) x := by
  have h := HasFDerivAt.sum (u := s)
    (fun i hi => (GradientDependentLocal.derivative_chain (hf i hi)).1 x)
  have hh : HasGradientAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, gradient (f i) x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    · funext y
      simp
    · ext v
      simp
  exact hh.gradient

lemma sum_hessian {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ 3 (f i)) (x : E) :
    fderiv ℝ (gradient (fun y => ∑ i ∈ s, f i y)) x =
      ∑ i ∈ s, fderiv ℝ (gradient (f i)) x := by
  have he : gradient (fun y => ∑ i ∈ s, f i y) = fun y => ∑ i ∈ s, gradient (f i) y :=
    funext (sum_gradient s hf)
  rw [he]
  convert (HasFDerivAt.sum (u := s)
    (fun i hi => (GradientDependentLocal.derivative_chain (hf i hi)).2.1 x)).fderiv using 2
  funext y
  simp

lemma sum_third {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ 3 (f i)) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun y => ∑ i ∈ s, f i y))) x =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (gradient (f i))) x := by
  have he : fderiv ℝ (gradient (fun y => ∑ i ∈ s, f i y)) =
      fun y => ∑ i ∈ s, fderiv ℝ (gradient (f i)) y := funext (sum_hessian s hf)
  rw [he]
  convert (HasFDerivAt.sum (u := s)
    (fun i hi => (GradientDependentLocal.derivative_chain (hf i hi)).2.2 x)).fderiv using 2
  funext y
  simp

lemma difference_gradient {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    gradient (fun z => f z - g z) x = gradient f x - gradient g x := by
  simpa only [one_mul, neg_one_mul, one_smul, neg_one_smul, sub_eq_add_neg] using
    combination_gradient hf hg 1 (-1) x

lemma difference_hessian {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    fderiv ℝ (gradient (fun z => f z - g z)) x =
      fderiv ℝ (gradient f) x - fderiv ℝ (gradient g) x := by
  simpa only [one_mul, neg_one_mul, one_smul, neg_one_smul, sub_eq_add_neg] using
    combination_hessian hf hg 1 (-1) x

lemma difference_third {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun z => f z - g z))) x =
      fderiv ℝ (fderiv ℝ (gradient f)) x - fderiv ℝ (fderiv ℝ (gradient g)) x := by
  have h := combination_third hf hg 1 (-1) x
  simp only [one_mul, neg_one_mul] at h
  rw [show (fun z => f z - g z) = (fun z => f z + -g z) from rfl, h]
  ext u v
  simp only [add_apply, smul_apply, one_smul, neg_one_smul, neg_apply, sub_eq_add_neg]

omit [FiniteDimensional ℝ E] in
lemma shift_gradient (f : E → ℝ) (c : ℝ) :
    gradient (fun z => f z - c) = gradient f := by
  funext x
  simp only [gradient, fderiv_sub_const]

omit [FiniteDimensional ℝ E] in
lemma shift_third (f : E → ℝ) (c : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun z => f z - c))) x =
      fderiv ℝ (fderiv ℝ (gradient f)) x := by rw [shift_gradient]

lemma scale_gradient {f : E → ℝ} (hf : ContDiff ℝ 3 f) (c r : ℝ) (x : E) :
    gradient (fun z => c * f (r • z)) x = (c * r) • gradient f (r • x) := by
  have hp := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul r
  have h := (((GradientDependentLocal.derivative_chain hf).1 (r • x)).comp x hp).const_mul c
  have hh : HasGradientAt (fun z => c * f (r • z)) ((c * r) • gradient f (r • x)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    · funext z
      rfl
    · ext u
      simp [smul_smul, mul_assoc]
  exact hh.gradient

lemma scale_hessian {f : E → ℝ} (hf : ContDiff ℝ 3 f) (c r : ℝ) (x : E) :
    fderiv ℝ (gradient (fun z => c * f (r • z))) x =
      (c * r ^ 2) • fderiv ℝ (gradient f) (r • x) := by
  have he : gradient (fun z => c * f (r • z)) =
      fun z => (c * r) • gradient f (r • z) := funext (scale_gradient hf c r)
  rw [he]
  have hp := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul r
  have h := (((GradientDependentLocal.derivative_chain hf).2.1 (r • x)).comp x hp).const_smul (c * r)
  have hh : HasFDerivAt (fun z => (c * r) • gradient f (r • z))
      ((c * r ^ 2) • fderiv ℝ (gradient f) (r • x)) x := by
    convert h using 1
    · funext z
      rfl
    · ext u
      simp [smul_smul, pow_two, mul_assoc]
  exact hh.fderiv

lemma scale_third {f : E → ℝ} (hf : ContDiff ℝ 3 f) (c r : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun z => c * f (r • z)))) x =
      (c * r ^ 3) • fderiv ℝ (fderiv ℝ (gradient f)) (r • x) := by
  have he : fderiv ℝ (gradient (fun z => c * f (r • z))) =
      fun z => (c * r ^ 2) • fderiv ℝ (gradient f) (r • z) := funext (scale_hessian hf c r)
  rw [he]
  have hp := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul r
  have h := (((GradientDependentLocal.derivative_chain hf).2.2 (r • x)).comp x hp).const_smul (c * r ^ 2)
  have hh : HasFDerivAt (fun z => (c * r ^ 2) • fderiv ℝ (gradient f) (r • z))
      ((c * r ^ 3) • fderiv ℝ (fderiv ℝ (gradient f)) (r • x)) x := by
    convert h using 1
    · funext z
      rfl
    · ext u v
      simp [smul_smul, pow_succ, mul_assoc]
  exact hh.fderiv

omit [FiniteDimensional ℝ E] in
lemma local_jets_eq {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) :
    f x = g x ∧ gradient f x = gradient g x ∧
      fderiv ℝ (gradient f) x = fderiv ℝ (gradient g) x ∧
      fderiv ℝ (fderiv ℝ (gradient f)) x = fderiv ℝ (fderiv ℝ (gradient g)) x :=
  ⟨h.eq_of_nhds, h.gradient_eq, h.gradient.fderiv_eq, h.gradient.fderiv.fderiv_eq⟩

end LongTails.Proofs.ThirdOrderAffineCalculus
