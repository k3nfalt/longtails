import LongTails.Proofs.ScalarCompositionJets

namespace LongTails.Proofs.ProductCompositionJets

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma product_gradient {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  have h := ((GradientDependentLocal.derivative_chain hf).1 x).mul
    ((GradientDependentLocal.derivative_chain hg).1 x)
  have hh : HasGradientAt (fun y => f y * g y)
      (f x • gradient g x + g x • gradient f x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext v
    simp
  exact hh.gradient

lemma product_hessian_apply {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x v : E) :
    fderiv ℝ (gradient (fun y => f y * g y)) x v =
      f x • fderiv ℝ (gradient g) x v +
      ⟪gradient f x, v⟫ • gradient g x +
      g x • fderiv ℝ (gradient f) x v +
      ⟪gradient g x, v⟫ • gradient f x := by
  have hfp := ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hf).1 x) v
  have hgp := ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hg).1 x) v
  have hfg := ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hf).2.1 x) v
  have hgg := ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hg).2.1 x) v
  have h := (hfp.smul hgg).add (hgp.smul hfg)
  have hcan := ScalarCompositionJets.along_line
    ((GradientDependentLocal.derivative_chain (hf.mul hg)).2.1 x) v
  have he : (fun t : ℝ => gradient (fun y => f y * g y) (x + t • v)) =
      fun t => f (x + t • v) • gradient g (x + t • v) +
        g (x + t • v) • gradient f (x + t • v) := funext (fun _ => product_gradient hf hg _)
  change HasDerivAt (fun t : ℝ => gradient (fun y => f y * g y) (x + t • v)) _ 0 at hcan
  rw [he] at hcan
  simpa [add_assoc] using hcan.unique h

lemma product_third_apply {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x u v : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun y => f y * g y))) x u v =
      f x • fderiv ℝ (fderiv ℝ (gradient g)) x u v +
      ⟪gradient f x, u⟫ • fderiv ℝ (gradient g) x v +
      ⟪gradient f x, v⟫ • fderiv ℝ (gradient g) x u +
      ⟪fderiv ℝ (gradient f) x u, v⟫ • gradient g x +
      g x • fderiv ℝ (fderiv ℝ (gradient f)) x u v +
      ⟪gradient g x, u⟫ • fderiv ℝ (gradient f) x v +
      ⟪gradient g x, v⟫ • fderiv ℝ (gradient f) x u +
      ⟪fderiv ℝ (gradient g) x u, v⟫ • gradient f x := by
  have hfp := ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hf).1 x) u
  have hgp := ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hg).1 x) u
  have hfg := ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hf).2.1 x) u
  have hgg := ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hg).2.1 x) u
  have hfH := (ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hf).2.2 x) u).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have hgH := (ScalarCompositionJets.along_line ((GradientDependentLocal.derivative_chain hg).2.2 x) u).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have h := (((hfp.smul hgH).add
    ((hfg.inner ℝ (hasDerivAt_const (0 : ℝ) v)).smul hgg)).add
    (hgp.smul hfH)).add ((hgg.inner ℝ (hasDerivAt_const (0 : ℝ) v)).smul hfg)
  have hcan := (ScalarCompositionJets.along_line
    ((GradientDependentLocal.derivative_chain (hf.mul hg)).2.2 x) u).clm_apply
      (hasDerivAt_const (0 : ℝ) v)
  have he : (fun t : ℝ => fderiv ℝ (gradient (fun y => f y * g y)) (x + t • u) v) =
      fun t => f (x + t • u) • fderiv ℝ (gradient g) (x + t • u) v +
        ⟪gradient f (x + t • u), v⟫ • gradient g (x + t • u) +
        g (x + t • u) • fderiv ℝ (gradient f) (x + t • u) v +
        ⟪gradient g (x + t • u), v⟫ • gradient f (x + t • u) :=
    funext (fun _ => product_hessian_apply hf hg _ _)
  change HasDerivAt (fun t : ℝ => fderiv ℝ (gradient (fun y => f y * g y)) (x + t • u) v) _ 0 at hcan
  rw [he] at hcan
  simpa [add_assoc] using hcan.unique h

lemma product_gradient_bound {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : E) {M : ℝ} (hM : 0 ≤ M) (hval : |f x| ≤ M ∧ |g x| ≤ M)
    (hgrad : ‖gradient f x‖ ≤ M ∧ ‖gradient g x‖ ≤ M) :
    ‖gradient (fun y => f y * g y) x‖ ≤ 2 * M ^ 2 := by
  rw [product_gradient hf hg]
  calc
    _ ≤ ‖f x • gradient g x‖ + ‖g x • gradient f x‖ := norm_add_le _ _
    _ = |f x| * ‖gradient g x‖ + |g x| * ‖gradient f x‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ M * M + M * M := add_le_add
      (mul_le_mul hval.1 hgrad.2 (norm_nonneg _) hM)
      (mul_le_mul hval.2 hgrad.1 (norm_nonneg _) hM)
    _ = _ := by ring

lemma product_hessian_bound {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : E) {M : ℝ} (hM : 0 ≤ M) (hval : |f x| ≤ M ∧ |g x| ≤ M)
    (hgrad : ‖gradient f x‖ ≤ M ∧ ‖gradient g x‖ ≤ M)
    (hH : ‖fderiv ℝ (gradient f) x‖ ≤ M ∧ ‖fderiv ℝ (gradient g) x‖ ≤ M) :
    ‖fderiv ℝ (gradient (fun y => f y * g y)) x‖ ≤ 4 * M ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have hfu := ((fderiv ℝ (gradient f) x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hH.1 (norm_nonneg u))
  have hgu := ((fderiv ℝ (gradient g) x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hH.2 (norm_nonneg u))
  have hdf := (abs_real_inner_le_norm (gradient f x) u).trans
    (mul_le_mul_of_nonneg_right hgrad.1 (norm_nonneg u))
  have hdg := (abs_real_inner_le_norm (gradient g x) u).trans
    (mul_le_mul_of_nonneg_right hgrad.2 (norm_nonneg u))
  rw [product_hessian_apply hf hg]
  calc
    _ ≤ ‖f x • fderiv ℝ (gradient g) x u‖ + ‖⟪gradient f x, u⟫ • gradient g x‖ +
        ‖g x • fderiv ℝ (gradient f) x u‖ + ‖⟪gradient g x, u⟫ • gradient f x‖ := by
      grw [norm_add_le, norm_add_le, norm_add_le]
    _ = |f x| * ‖fderiv ℝ (gradient g) x u‖ + |⟪gradient f x, u⟫| * ‖gradient g x‖ +
        |g x| * ‖fderiv ℝ (gradient f) x u‖ + |⟪gradient g x, u⟫| * ‖gradient f x‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ M * (M * ‖u‖) + (M * ‖u‖) * M + M * (M * ‖u‖) + (M * ‖u‖) * M :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul hval.1 hgu (norm_nonneg _) hM)
        (mul_le_mul hdf hgrad.2 (norm_nonneg _) (by positivity)))
        (mul_le_mul hval.2 hfu (norm_nonneg _) hM))
        (mul_le_mul hdg hgrad.1 (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma product_third_bound {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x u v : E) {M U V : ℝ} (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hval : |f x| ≤ M ∧ |g x| ≤ M)
    (hgrad : ‖gradient f x‖ ≤ M ∧ ‖gradient g x‖ ≤ M)
    (hdu : |⟪gradient f x, u⟫| ≤ M * U ∧ |⟪gradient g x, u⟫| ≤ M * U)
    (hdv : |⟪gradient f x, v⟫| ≤ M * V ∧ |⟪gradient g x, v⟫| ≤ M * V)
    (hHu : ‖fderiv ℝ (gradient f) x u‖ ≤ M * U ∧ ‖fderiv ℝ (gradient g) x u‖ ≤ M * U)
    (hHv : ‖fderiv ℝ (gradient f) x v‖ ≤ M * V ∧ ‖fderiv ℝ (gradient g) x v‖ ≤ M * V)
    (hHuv : |⟪fderiv ℝ (gradient f) x u, v⟫| ≤ M * U * V ∧
      |⟪fderiv ℝ (gradient g) x u, v⟫| ≤ M * U * V)
    (hT : ‖fderiv ℝ (fderiv ℝ (gradient f)) x u v‖ ≤ M * U * V ∧
      ‖fderiv ℝ (fderiv ℝ (gradient g)) x u v‖ ≤ M * U * V) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun y => f y * g y))) x u v‖ ≤ 8 * M ^ 2 * U * V := by
  have hs {c A B : ℝ} {z : E} (hc : |c| ≤ A) (hz : ‖z‖ ≤ B) (hA : 0 ≤ A) :
      ‖c • z‖ ≤ A * B := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hz (norm_nonneg z) hA
  rw [product_third_apply hf hg]
  calc
    _ ≤ ‖f x • fderiv ℝ (fderiv ℝ (gradient g)) x u v‖ +
        ‖⟪gradient f x, u⟫ • fderiv ℝ (gradient g) x v‖ +
        ‖⟪gradient f x, v⟫ • fderiv ℝ (gradient g) x u‖ +
        ‖⟪fderiv ℝ (gradient f) x u, v⟫ • gradient g x‖ +
        ‖g x • fderiv ℝ (fderiv ℝ (gradient f)) x u v‖ +
        ‖⟪gradient g x, u⟫ • fderiv ℝ (gradient f) x v‖ +
        ‖⟪gradient g x, v⟫ • fderiv ℝ (gradient f) x u‖ +
        ‖⟪fderiv ℝ (gradient g) x u, v⟫ • gradient f x‖ := by
      grw [norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le]
    _ ≤ M * (M * U * V) + (M * U) * (M * V) + (M * V) * (M * U) +
        (M * U * V) * M + M * (M * U * V) + (M * U) * (M * V) +
        (M * V) * (M * U) + (M * U * V) * M := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (hs hval.1 hT.2 hM) (hs hdu.1 hHv.2 (by positivity)))
        (hs hdv.1 hHu.2 (by positivity))) (hs hHuv.1 hgrad.2 (by positivity)))
        (hs hval.2 hT.1 hM)) (hs hdu.2 hHv.1 (by positivity)))
        (hs hdv.2 hHu.1 (by positivity))) (hs hHuv.2 hgrad.1 (by positivity))
    _ = _ := by ring

lemma product_third_norm {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun y => f y * g y))) x‖ ≤
      |f x| * ‖fderiv ℝ (fderiv ℝ (gradient g)) x‖ +
      |g x| * ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ +
      3 * ‖gradient f x‖ * ‖fderiv ℝ (gradient g) x‖ +
      3 * ‖gradient g x‖ * ‖fderiv ℝ (gradient f) x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have ht (T : E →L[ℝ] E →L[ℝ] E) : ‖T u v‖ ≤ ‖T‖ * ‖u‖ * ‖v‖ :=
    ((T u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (T.le_opNorm u) (norm_nonneg v))
  have hh (H : E →L[ℝ] E) : |⟪H u, v⟫| ≤ ‖H‖ * ‖u‖ * ‖v‖ :=
    (abs_real_inner_le_norm (H u) v).trans
      (mul_le_mul_of_nonneg_right (H.le_opNorm u) (norm_nonneg v))
  have hs {c A B : ℝ} {z : E} (hc : |c| ≤ A) (hz : ‖z‖ ≤ B) (hA : 0 ≤ A) :
      ‖c • z‖ ≤ A * B := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hz (norm_nonneg z) hA
  rw [product_third_apply hf hg]
  calc
    _ ≤ ‖f x • fderiv ℝ (fderiv ℝ (gradient g)) x u v‖ +
        ‖⟪gradient f x, u⟫ • fderiv ℝ (gradient g) x v‖ +
        ‖⟪gradient f x, v⟫ • fderiv ℝ (gradient g) x u‖ +
        ‖⟪fderiv ℝ (gradient f) x u, v⟫ • gradient g x‖ +
        ‖g x • fderiv ℝ (fderiv ℝ (gradient f)) x u v‖ +
        ‖⟪gradient g x, u⟫ • fderiv ℝ (gradient f) x v‖ +
        ‖⟪gradient g x, v⟫ • fderiv ℝ (gradient f) x u‖ +
        ‖⟪fderiv ℝ (gradient g) x u, v⟫ • gradient f x‖ := by
      grw [norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le]
    _ ≤ |f x| * (‖fderiv ℝ (fderiv ℝ (gradient g)) x‖ * ‖u‖ * ‖v‖) +
        (‖gradient f x‖ * ‖u‖) * (‖fderiv ℝ (gradient g) x‖ * ‖v‖) +
        (‖gradient f x‖ * ‖v‖) * (‖fderiv ℝ (gradient g) x‖ * ‖u‖) +
        (‖fderiv ℝ (gradient f) x‖ * ‖u‖ * ‖v‖) * ‖gradient g x‖ +
        |g x| * (‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ * ‖u‖ * ‖v‖) +
        (‖gradient g x‖ * ‖u‖) * (‖fderiv ℝ (gradient f) x‖ * ‖v‖) +
        (‖gradient g x‖ * ‖v‖) * (‖fderiv ℝ (gradient f) x‖ * ‖u‖) +
        (‖fderiv ℝ (gradient g) x‖ * ‖u‖ * ‖v‖) * ‖gradient f x‖ := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (hs le_rfl (ht _) (abs_nonneg _))
        (hs (abs_real_inner_le_norm _ _) ((fderiv ℝ (gradient g) x).le_opNorm v) (by positivity)))
        (hs (abs_real_inner_le_norm _ _) ((fderiv ℝ (gradient g) x).le_opNorm u) (by positivity)))
        (hs (hh _) le_rfl (by positivity)))
        (hs le_rfl (ht _) (abs_nonneg _)))
        (hs (abs_real_inner_le_norm _ _) ((fderiv ℝ (gradient f) x).le_opNorm v) (by positivity)))
        (hs (abs_real_inner_le_norm _ _) ((fderiv ℝ (gradient f) x).le_opNorm u) (by positivity)))
        (hs (hh _) le_rfl (by positivity))
    _ = _ := by ring

end LongTails.Proofs.ProductCompositionJets
