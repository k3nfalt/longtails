import LongTails.Proofs.GradientDependentLocal
import LongTails.Proofs.RelativeHessianGate

namespace LongTails.Proofs.ScalarCompositionJets

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma along_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {f' : E →L[ℝ] F} (hf : HasFDerivAt f f' x) (u : E) :
    HasDerivAt (fun t : ℝ => f (x + t • u)) (f' u) 0 := by
  have hp : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hh : HasFDerivAt f f' (x + (0 : ℝ) • u) := by simpa using hf
  exact hh.comp_hasDerivAt 0 hp

lemma comp_gradient {f : E → ℝ} {φ φ₁ : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (x : E) :
    gradient (φ ∘ f) x = φ₁ (f x) • gradient f x := by
  have h := (hφ (f x)).comp_hasFDerivAt x ((GradientDependentLocal.derivative_chain hf).1 x)
  have hg : HasGradientAt (φ ∘ f) (φ₁ (f x) • gradient f x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext v
    simp
  exact hg.gradient

lemma comp_hessian_apply {f : E → ℝ} {φ φ₁ φ₂ : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (x v : E) :
    fderiv ℝ (gradient (φ ∘ f)) x v =
      φ₁ (f x) • (fderiv ℝ (gradient f) x v) +
        (φ₂ (f x) * ⟪gradient f x, v⟫) • gradient f x := by
  have hgpath := along_line ((GradientDependentLocal.derivative_chain hf).2.1 x) v
  have hscalar := along_line ((hφ₁ (f x)).comp_hasFDerivAt x
    ((GradientDependentLocal.derivative_chain hf).1 x)) v
  have hprod := hscalar.smul hgpath
  have hcan := along_line ((GradientDependentLocal.derivative_chain (hφc.comp hf)).2.1 x) v
  have he : (fun t : ℝ => gradient (φ ∘ f) (x + t • v)) =
      fun t => φ₁ (f (x + t • v)) • gradient f (x + t • v) := by
    funext t
    exact comp_gradient hf hφ _
  change HasDerivAt (fun t : ℝ => gradient (φ ∘ f) (x + t • v)) _ 0 at hcan
  rw [he] at hcan
  simpa using hcan.unique hprod

lemma comp_third_apply {f : E → ℝ} {φ φ₁ φ₂ φ₃ : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (hφ₂ : ∀ t, HasDerivAt φ₂ (φ₃ t) t) (x u v : E) :
    fderiv ℝ (fderiv ℝ (gradient (φ ∘ f))) x u v =
      φ₁ (f x) • (fderiv ℝ (fderiv ℝ (gradient f)) x u v) +
      (φ₂ (f x) * ⟪gradient f x, u⟫) • (fderiv ℝ (gradient f) x v) +
      (φ₂ (f x) * ⟪gradient f x, v⟫) • (fderiv ℝ (gradient f) x u) +
      (φ₃ (f x) * ⟪gradient f x, u⟫ * ⟪gradient f x, v⟫ +
        φ₂ (f x) * ⟪fderiv ℝ (gradient f) x u, v⟫) • gradient f x := by
  have hgpath := along_line ((GradientDependentLocal.derivative_chain hf).2.1 x) u
  have hHpath := (along_line ((GradientDependentLocal.derivative_chain hf).2.2 x) u).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have hs₁ := along_line ((hφ₁ (f x)).comp_hasFDerivAt x
    ((GradientDependentLocal.derivative_chain hf).1 x)) u
  have hs₂ := along_line ((hφ₂ (f x)).comp_hasFDerivAt x
    ((GradientDependentLocal.derivative_chain hf).1 x)) u
  have hi := hgpath.inner ℝ (hasDerivAt_const (0 : ℝ) v)
  have hsum := (hs₁.smul hHpath).add ((hs₂.mul hi).smul hgpath)
  have hcan := (along_line ((GradientDependentLocal.derivative_chain (hφc.comp hf)).2.2 x) u).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have he : (fun t : ℝ => fderiv ℝ (gradient (φ ∘ f)) (x + t • u) v) =
      fun t => φ₁ (f (x + t • u)) • (fderiv ℝ (gradient f) (x + t • u) v) +
        (φ₂ (f (x + t • u)) * ⟪gradient f (x + t • u), v⟫) • gradient f (x + t • u) := by
    funext t
    exact comp_hessian_apply hf hφc hφ hφ₁ _ _
  change HasDerivAt (fun t : ℝ => fderiv ℝ (gradient (φ ∘ f)) (x + t • u) v) _ 0 at hcan
  rw [he] at hcan
  have hh := hcan.unique hsum
  simpa [Function.comp_def, add_assoc, mul_assoc] using hh

lemma comp_hessian_norm {f : E → ℝ} {φ φ₁ φ₂ : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t) (x : E) :
    ‖fderiv ℝ (gradient (φ ∘ f)) x‖ ≤ |φ₁ (f x)| * ‖fderiv ℝ (gradient f) x‖ +
      |φ₂ (f x)| * ‖gradient f x‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [comp_hessian_apply hf hφc hφ hφ₁]
  calc
    _ ≤ ‖φ₁ (f x) • fderiv ℝ (gradient f) x u‖ +
        ‖(φ₂ (f x) * ⟪gradient f x, u⟫) • gradient f x‖ := norm_add_le _ _
    _ = |φ₁ (f x)| * ‖fderiv ℝ (gradient f) x u‖ +
        (|φ₂ (f x)| * |⟪gradient f x, u⟫|) * ‖gradient f x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul]
    _ ≤ |φ₁ (f x)| * (‖fderiv ℝ (gradient f) x‖ * ‖u‖) +
        (|φ₂ (f x)| * (‖gradient f x‖ * ‖u‖)) * ‖gradient f x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left ((fderiv ℝ (gradient f) x).le_opNorm u) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)) (norm_nonneg _))
    _ = _ := by ring

lemma comp_third_norm {f : E → ℝ} {φ φ₁ φ₂ φ₃ : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (hφ₂ : ∀ t, HasDerivAt φ₂ (φ₃ t) t) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (φ ∘ f))) x‖ ≤
      |φ₁ (f x)| * ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ +
      3 * |φ₂ (f x)| * ‖gradient f x‖ * ‖fderiv ℝ (gradient f) x‖ +
      |φ₃ (f x)| * ‖gradient f x‖ ^ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have ht : ‖fderiv ℝ (fderiv ℝ (gradient f)) x u v‖ ≤
      ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ * ‖u‖ * ‖v‖ :=
    ((fderiv ℝ (fderiv ℝ (gradient f)) x u).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ (gradient f)) x).le_opNorm u) (norm_nonneg v))
  have hh : |⟪fderiv ℝ (gradient f) x u, v⟫| ≤ ‖fderiv ℝ (gradient f) x‖ * ‖u‖ * ‖v‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (gradient f) x).le_opNorm u) (norm_nonneg v))
  have hs {c A B : ℝ} {z : E} (hc : |c| ≤ A) (hz : ‖z‖ ≤ B) (hA : 0 ≤ A) :
      ‖c • z‖ ≤ A * B := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hz (norm_nonneg z) hA
  have hcoef : |φ₃ (f x) * ⟪gradient f x, u⟫ * ⟪gradient f x, v⟫ +
      φ₂ (f x) * ⟪fderiv ℝ (gradient f) x u, v⟫| ≤
      |φ₃ (f x)| * (‖gradient f x‖ * ‖u‖) * (‖gradient f x‖ * ‖v‖) +
        |φ₂ (f x)| * (‖fderiv ℝ (gradient f) x‖ * ‖u‖ * ‖v‖) := by
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    exact add_le_add (mul_le_mul
      (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _))
      (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_left hh (abs_nonneg _))
  rw [comp_third_apply hf hφc hφ hφ₁ hφ₂]
  calc
    _ ≤ ‖φ₁ (f x) • fderiv ℝ (fderiv ℝ (gradient f)) x u v‖ +
        ‖(φ₂ (f x) * ⟪gradient f x, u⟫) • fderiv ℝ (gradient f) x v‖ +
        ‖(φ₂ (f x) * ⟪gradient f x, v⟫) • fderiv ℝ (gradient f) x u‖ +
        ‖(φ₃ (f x) * ⟪gradient f x, u⟫ * ⟪gradient f x, v⟫ +
          φ₂ (f x) * ⟪fderiv ℝ (gradient f) x u, v⟫) • gradient f x‖ := by
      grw [norm_add_le, norm_add_le, norm_add_le]
    _ ≤ |φ₁ (f x)| * (‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ * ‖u‖ * ‖v‖) +
        (|φ₂ (f x)| * (‖gradient f x‖ * ‖u‖)) * (‖fderiv ℝ (gradient f) x‖ * ‖v‖) +
        (|φ₂ (f x)| * (‖gradient f x‖ * ‖v‖)) * (‖fderiv ℝ (gradient f) x‖ * ‖u‖) +
        (|φ₃ (f x)| * (‖gradient f x‖ * ‖u‖) * (‖gradient f x‖ * ‖v‖) +
          |φ₂ (f x)| * (‖fderiv ℝ (gradient f) x‖ * ‖u‖ * ‖v‖)) * ‖gradient f x‖ := by
      refine add_le_add (add_le_add (add_le_add (hs le_rfl ht (abs_nonneg _)) ?_) ?_)
        (hs hcoef le_rfl (by positivity))
      · apply hs _ ((fderiv ℝ (gradient f) x).le_opNorm v) (by positivity)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      · apply hs _ ((fderiv ℝ (gradient f) x).le_opNorm u) (by positivity)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ = _ := by ring

end LongTails.Proofs.ScalarCompositionJets
