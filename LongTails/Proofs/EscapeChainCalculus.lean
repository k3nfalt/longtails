import LongTails.Proofs.RidgeJets
import LongTails.Proofs.ProductCompositionJets
import LongTails.Proofs.ThirdOrderAffineCalculus
import LongTails.Proofs.RelativeHessianGuard

namespace LongTails.Proofs.EscapeChainCalculus

open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def D (f : E → ℝ) (x e : E) : ℝ := ⟪gradient f x, e⟫
noncomputable def Q (f : E → ℝ) (x e : E) : ℝ := ⟪fderiv ℝ (gradient f) x e, e⟫

lemma D_mul {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x e : E) :
    D (fun y => f y * g y) x e = f x * D g x e + g x * D f x e := by
  unfold D
  rw [ProductCompositionJets.product_gradient hf hg, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]

lemma Q_mul {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x e : E) :
    Q (fun y => f y * g y) x e = f x * Q g x e + 2 * (D f x e * D g x e) + g x * Q f x e := by
  unfold Q D
  rw [ProductCompositionJets.product_hessian_apply hf hg]
  simp only [inner_add_left, real_inner_smul_left]
  ring

omit [FiniteDimensional ℝ E] in
lemma D_const (c : ℝ) (x e : E) : D (fun _ : E => c) x e = 0 := by
  simp [D, gradient_fun_const]

omit [FiniteDimensional ℝ E] in
lemma Q_const (c : ℝ) (x e : E) : Q (fun _ : E => c) x e = 0 := by
  simp [Q, gradient_fun_const']

lemma D_const_mul {g : E → ℝ} (hg : ContDiff ℝ 3 g) (c : ℝ) (x e : E) :
    D (fun y => c * g y) x e = c * D g x e := by
  rw [D_mul contDiff_const hg, D_const]; ring

lemma Q_const_mul {g : E → ℝ} (hg : ContDiff ℝ 3 g) (c : ℝ) (x e : E) :
    Q (fun y => c * g y) x e = c * Q g x e := by
  rw [Q_mul contDiff_const hg, D_const, Q_const]; ring

lemma D_add {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x e : E) :
    D (fun y => f y + g y) x e = D f x e + D g x e := by
  unfold D
  have h := ThirdOrderAffineCalculus.combination_gradient hf hg 1 1 x
  simp only [one_mul, one_smul] at h
  rw [h, inner_add_left]

lemma Q_add {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x e : E) :
    Q (fun y => f y + g y) x e = Q f x e + Q g x e := by
  unfold Q
  have h := ThirdOrderAffineCalculus.combination_hessian hf hg 1 1 x
  simp only [one_mul, one_smul] at h
  rw [h]
  simp [inner_add_left]

lemma D_sub {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x e : E) :
    D (fun y => f y - g y) x e = D f x e - D g x e := by
  unfold D
  rw [ThirdOrderAffineCalculus.difference_gradient hf hg, inner_sub_left]

lemma Q_sub {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x e : E) :
    Q (fun y => f y - g y) x e = Q f x e - Q g x e := by
  unfold Q
  rw [ThirdOrderAffineCalculus.difference_hessian hf hg]
  simp [inner_sub_left]

lemma D_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ 3 (f i))
    (x e : E) : D (fun y => ∑ i ∈ s, f i y) x e = ∑ i ∈ s, D (f i) x e := by
  unfold D
  rw [ThirdOrderAffineCalculus.sum_gradient s hf, sum_inner]

lemma Q_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ 3 (f i))
    (x e : E) : Q (fun y => ∑ i ∈ s, f i y) x e = ∑ i ∈ s, Q (f i) x e := by
  unfold Q
  rw [ThirdOrderAffineCalculus.sum_hessian s hf]
  simp [sum_inner]

omit [FiniteDimensional ℝ E] in
lemma D_ridge {φ φ₁ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (a x e : E) :
    D (RidgeJets.value φ a) x e = φ₁ ⟪a, x⟫ * ⟪a, e⟫ := by
  unfold D
  rw [RidgeJets.gradient_eq hφ, real_inner_smul_left]

omit [FiniteDimensional ℝ E] in
lemma Q_ridge {φ φ₁ φ₂ : ℝ → ℝ} (hφc : ContDiff ℝ 3 φ) (hφ : ∀ t, HasDerivAt φ (φ₁ t) t)
    (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t) (a x e : E) :
    Q (RidgeJets.value φ a) x e = φ₂ ⟪a, x⟫ * ⟪a, e⟫ ^ 2 := by
  unfold Q
  rw [RidgeJets.hessian_apply hφc hφ hφ₁, real_inner_smul_left]
  ring

lemma D_comp {f : E → ℝ} {φ φ₁ : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (x e : E) :
    D (φ ∘ f) x e = φ₁ (f x) * D f x e := by
  unfold D
  rw [ScalarCompositionJets.comp_gradient hf hφ, real_inner_smul_left]

lemma Q_comp {f : E → ℝ} {φ φ₁ φ₂ : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t) (x e : E) :
    Q (φ ∘ f) x e = φ₁ (f x) * Q f x e + φ₂ (f x) * D f x e ^ 2 := by
  unfold Q D
  rw [ScalarCompositionJets.comp_hessian_apply hf hφc hφ hφ₁]
  simp only [inner_add_left, real_inner_smul_left]
  ring

omit [FiniteDimensional ℝ E] in
lemma D_normsq (x e : E) : D (FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E)) x e = 2 * ⟪x, e⟫ := by
  unfold D
  rw [RelativeHessianGuard.quadratic_gradient, real_inner_smul_left]

omit [FiniteDimensional ℝ E] in
lemma Q_normsq (x e : E) : Q (FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E)) x e = 2 * ‖e‖ ^ 2 := by
  unfold Q
  have hg : gradient (FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E)) = fun y => (2 : ℝ) • y :=
    funext (RelativeHessianGuard.quadratic_gradient 2)
  rw [hg]
  change ⟪(fderiv ℝ ((2 : ℝ) • (id : E → E)) x) e, e⟫ = _
  rw [((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (2 : ℝ)).fderiv]
  simp [real_inner_smul_left]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma normsq_eq (x : E) : FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) x = ‖x‖ ^ 2 := by
  simp [FullGeneralizedSmoothZeroQuery.quadratic]

end LongTails.Proofs.EscapeChainCalculus
