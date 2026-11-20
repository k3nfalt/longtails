import LongTails.Proofs.ProductCompositionJets
import LongTails.Proofs.RidgeJets
import Mathlib.Analysis.Calculus.MeanValue

namespace LongTails.Proofs.ThirdOrderJetDifference

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure JetBound (f : E → ℝ) (z u v : E) (c₀ c₁ c₂ c₃ U V : ℝ) : Prop where
  val : |f z| ≤ c₀
  grad : ‖gradient f z‖ ≤ c₁
  du : |⟪gradient f z, u⟫| ≤ c₁ * U
  dv : |⟪gradient f z, v⟫| ≤ c₁ * V
  hu : ‖fderiv ℝ (gradient f) z u‖ ≤ c₂ * U
  hv : ‖fderiv ℝ (gradient f) z v‖ ≤ c₂ * V
  huv : |⟪fderiv ℝ (gradient f) z u, v⟫| ≤ c₂ * U * V
  third : ‖fderiv ℝ (fderiv ℝ (gradient f)) z u v‖ ≤ c₃ * U * V

structure JetDiff (f : E → ℝ) (x y u v : E) (l₀ l₁ l₂ l₃ U V Z : ℝ) : Prop where
  val : |f x - f y| ≤ l₀ * Z
  grad : ‖gradient f x - gradient f y‖ ≤ l₁ * Z
  du : |⟪gradient f x, u⟫ - ⟪gradient f y, u⟫| ≤ l₁ * Z * U
  dv : |⟪gradient f x, v⟫ - ⟪gradient f y, v⟫| ≤ l₁ * Z * V
  hu : ‖fderiv ℝ (gradient f) x u - fderiv ℝ (gradient f) y u‖ ≤ l₂ * Z * U
  hv : ‖fderiv ℝ (gradient f) x v - fderiv ℝ (gradient f) y v‖ ≤ l₂ * Z * V
  huv : |⟪fderiv ℝ (gradient f) x u, v⟫ - ⟪fderiv ℝ (gradient f) y u, v⟫| ≤ l₂ * Z * U * V
  third : ‖fderiv ℝ (fderiv ℝ (gradient f)) x u v - fderiv ℝ (fderiv ℝ (gradient f)) y u v‖ ≤
    l₃ * Z * U * V

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smul_diff [NormedSpace ℝ E] (c c' : ℝ) (z z' : E) {A B C D : ℝ} (h₁ : |c - c'| ≤ A)
    (h₂ : ‖z‖ ≤ B) (h₃ : |c'| ≤ C) (h₄ : ‖z - z'‖ ≤ D) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ‖c • z - c' • z'‖ ≤ A * B + C * D := by
  have e : c • z - c' • z' = (c - c') • z + c' • (z - z') := by module
  rw [e]
  calc _ ≤ ‖(c - c') • z‖ + ‖c' • (z - z')‖ := norm_add_le _ _
    _ = |c - c'| * ‖z‖ + |c'| * ‖z - z'‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ A * B + C * D :=
        add_le_add (mul_le_mul h₁ h₂ (norm_nonneg _) hA) (mul_le_mul h₃ h₄ (norm_nonneg _) hC)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma norm_add₈_le (d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ : E) :
    ‖d₁ + d₂ + d₃ + d₄ + d₅ + d₆ + d₇ + d₈‖ ≤
      ‖d₁‖ + ‖d₂‖ + ‖d₃‖ + ‖d₄‖ + ‖d₅‖ + ‖d₆‖ + ‖d₇‖ + ‖d₈‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact norm_add_le _ _

lemma product_third_diff {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x y u v : E)
    {a₀ a₁ a₂ a₃ p₀ p₁ p₂ p₃ b₀ b₁ b₂ b₃ q₀ q₁ q₂ q₃ U V Z : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hZ : 0 ≤ Z)
    (ha : 0 ≤ a₀ ∧ 0 ≤ a₁ ∧ 0 ≤ a₂) (hp : 0 ≤ p₀ ∧ 0 ≤ p₁ ∧ 0 ≤ p₂)
    (hb : 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ 0 ≤ b₂) (hq : 0 ≤ q₀ ∧ 0 ≤ q₁ ∧ 0 ≤ q₂)
    (fx : JetBound f x u v a₀ a₁ a₂ a₃ U V) (fy : JetBound f y u v a₀ a₁ a₂ a₃ U V)
    (fd : JetDiff f x y u v p₀ p₁ p₂ p₃ U V Z)
    (gx : JetBound g x u v b₀ b₁ b₂ b₃ U V) (gy : JetBound g y u v b₀ b₁ b₂ b₃ U V)
    (gd : JetDiff g x y u v q₀ q₁ q₂ q₃ U V Z) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun z => f z * g z))) x u v -
        fderiv ℝ (fderiv ℝ (gradient (fun z => f z * g z))) y u v‖ ≤
      (p₀ * b₃ + a₀ * q₃ + 2 * (p₁ * b₂ + a₁ * q₂) + (p₂ * b₁ + a₂ * q₁) +
        (q₀ * a₃ + b₀ * p₃) + 2 * (q₁ * a₂ + b₁ * p₂) + (q₂ * a₁ + b₂ * p₁)) * Z * U * V := by
  obtain ⟨ha₀, ha₁, ha₂⟩ := ha
  obtain ⟨hp₀, hp₁, hp₂⟩ := hp
  obtain ⟨hb₀, hb₁, hb₂⟩ := hb
  obtain ⟨hq₀, hq₁, hq₂⟩ := hq
  have t₁ := smul_diff (f x) (f y) (fderiv ℝ (fderiv ℝ (gradient g)) x u v)
    (fderiv ℝ (fderiv ℝ (gradient g)) y u v) fd.val gx.third fy.val gd.third (by positivity) ha₀
  have t₂ := smul_diff ⟪gradient f x, u⟫ ⟪gradient f y, u⟫ (fderiv ℝ (gradient g) x v)
    (fderiv ℝ (gradient g) y v) fd.du gx.hv fy.du gd.hv (by positivity) (by positivity)
  have t₃ := smul_diff ⟪gradient f x, v⟫ ⟪gradient f y, v⟫ (fderiv ℝ (gradient g) x u)
    (fderiv ℝ (gradient g) y u) fd.dv gx.hu fy.dv gd.hu (by positivity) (by positivity)
  have t₄ := smul_diff ⟪fderiv ℝ (gradient f) x u, v⟫ ⟪fderiv ℝ (gradient f) y u, v⟫
    (gradient g x) (gradient g y) fd.huv gx.grad fy.huv gd.grad (by positivity) (by positivity)
  have t₅ := smul_diff (g x) (g y) (fderiv ℝ (fderiv ℝ (gradient f)) x u v)
    (fderiv ℝ (fderiv ℝ (gradient f)) y u v) gd.val fx.third gy.val fd.third (by positivity) hb₀
  have t₆ := smul_diff ⟪gradient g x, u⟫ ⟪gradient g y, u⟫ (fderiv ℝ (gradient f) x v)
    (fderiv ℝ (gradient f) y v) gd.du fx.hv gy.du fd.hv (by positivity) (by positivity)
  have t₇ := smul_diff ⟪gradient g x, v⟫ ⟪gradient g y, v⟫ (fderiv ℝ (gradient f) x u)
    (fderiv ℝ (gradient f) y u) gd.dv fx.hu gy.dv fd.hu (by positivity) (by positivity)
  have t₈ := smul_diff ⟪fderiv ℝ (gradient g) x u, v⟫ ⟪fderiv ℝ (gradient g) y u, v⟫
    (gradient f x) (gradient f y) gd.huv fx.grad gy.huv fd.grad (by positivity) (by positivity)
  rw [ProductCompositionJets.product_third_apply hf hg, ProductCompositionJets.product_third_apply hf hg]
  have e : ∀ (A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ : E),
      A₁ + A₂ + A₃ + A₄ + A₅ + A₆ + A₇ + A₈ - (B₁ + B₂ + B₃ + B₄ + B₅ + B₆ + B₇ + B₈) =
        (A₁ - B₁) + (A₂ - B₂) + (A₃ - B₃) + (A₄ - B₄) + (A₅ - B₅) + (A₆ - B₆) + (A₇ - B₇) +
          (A₈ - B₈) := by
    intros; abel
  rw [e]
  refine (norm_add₈_le _ _ _ _ _ _ _ _).trans ?_
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add t₁ t₂) t₃) t₄) t₅) t₆) t₇) t₈
  refine hsum.trans (le_of_eq ?_)
  ring

lemma product_hessian_bilinear {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x u v : E) {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ U V : ℝ} (hU : 0 ≤ U)
    (ha : 0 ≤ a₀ ∧ 0 ≤ a₁) (hb : 0 ≤ b₀ ∧ 0 ≤ b₁)
    (fx : JetBound f x u v a₀ a₁ a₂ a₃ U V) (gx : JetBound g x u v b₀ b₁ b₂ b₃ U V) :
    |⟪fderiv ℝ (gradient (fun z => f z * g z)) x u, v⟫| ≤
      (a₀ * b₂ + 2 * (a₁ * b₁) + a₂ * b₀) * U * V := by
  rw [ProductCompositionJets.product_hessian_apply hf hg]
  simp only [inner_add_left, real_inner_smul_left]
  have h₁ : |f x * ⟪fderiv ℝ (gradient g) x u, v⟫| ≤ a₀ * (b₂ * U * V) := by
    rw [abs_mul]; exact mul_le_mul fx.val gx.huv (abs_nonneg _) ha.1
  have h₂ : |⟪gradient f x, u⟫ * ⟪gradient g x, v⟫| ≤ (a₁ * U) * (b₁ * V) := by
    rw [abs_mul]; exact mul_le_mul fx.du gx.dv (abs_nonneg _) (mul_nonneg ha.2 hU)
  have h₃ : |g x * ⟪fderiv ℝ (gradient f) x u, v⟫| ≤ b₀ * (a₂ * U * V) := by
    rw [abs_mul]; exact mul_le_mul gx.val fx.huv (abs_nonneg _) hb.1
  have h₄ : |⟪gradient g x, u⟫ * ⟪gradient f x, v⟫| ≤ (b₁ * U) * (a₁ * V) := by
    rw [abs_mul]; exact mul_le_mul gx.du fx.dv (abs_nonneg _) (mul_nonneg hb.2 hU)
  calc _ ≤ |f x * ⟪fderiv ℝ (gradient g) x u, v⟫| + |⟪gradient f x, u⟫ * ⟪gradient g x, v⟫| +
        |g x * ⟪fderiv ℝ (gradient f) x u, v⟫| + |⟪gradient g x, u⟫ * ⟪gradient f x, v⟫| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ a₀ * (b₂ * U * V) + (a₁ * U) * (b₁ * V) + b₀ * (a₂ * U * V) + (b₁ * U) * (a₁ * V) :=
        add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = _ := by ring

lemma product_hessian_norm {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    ‖fderiv ℝ (gradient (fun z => f z * g z)) x‖ ≤
      |f x| * ‖fderiv ℝ (gradient g) x‖ + 2 * ‖gradient f x‖ * ‖gradient g x‖ +
        |g x| * ‖fderiv ℝ (gradient f) x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [ProductCompositionJets.product_hessian_apply hf hg]
  have h₁ : ‖f x • fderiv ℝ (gradient g) x u‖ ≤ |f x| * (‖fderiv ℝ (gradient g) x‖ * ‖u‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((fderiv ℝ (gradient g) x).le_opNorm u) (abs_nonneg _)
  have h₂ : ‖⟪gradient f x, u⟫ • gradient g x‖ ≤ (‖gradient f x‖ * ‖u‖) * ‖gradient g x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
  have h₃ : ‖g x • fderiv ℝ (gradient f) x u‖ ≤ |g x| * (‖fderiv ℝ (gradient f) x‖ * ‖u‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((fderiv ℝ (gradient f) x).le_opNorm u) (abs_nonneg _)
  have h₄ : ‖⟪gradient g x, u⟫ • gradient f x‖ ≤ (‖gradient g x‖ * ‖u‖) * ‖gradient f x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
  calc _ ≤ ‖f x • fderiv ℝ (gradient g) x u‖ + ‖⟪gradient f x, u⟫ • gradient g x‖ +
        ‖g x • fderiv ℝ (gradient f) x u‖ + ‖⟪gradient g x, u⟫ • gradient f x‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ |f x| * (‖fderiv ℝ (gradient g) x‖ * ‖u‖) + (‖gradient f x‖ * ‖u‖) * ‖gradient g x‖ +
        |g x| * (‖fderiv ℝ (gradient f) x‖ * ‖u‖) + (‖gradient g x‖ * ‖u‖) * ‖gradient f x‖ :=
        add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = _ := by ring

lemma ridge_bound {φ φ₁ φ₂ φ₃ : ℝ → ℝ} (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (hφ₂ : ∀ t, HasDerivAt φ₂ (φ₃ t) t) (a z u v : E) {M U V : ℝ}
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : ‖a‖ ≤ 1)
    (hu : |⟪a, u⟫| ≤ U) (hv : |⟪a, v⟫| ≤ V)
    (h₀ : |φ ⟪a, z⟫| ≤ M) (h₁ : |φ₁ ⟪a, z⟫| ≤ M) (h₂ : |φ₂ ⟪a, z⟫| ≤ M) (h₃ : |φ₃ ⟪a, z⟫| ≤ M) :
    JetBound (RidgeJets.value φ a) z u v M M M M U V := by
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩ :=
    RidgeJets.jet_bounds hφc hφ hφ₁ hφ₂ a z u v hM hU hV ha hu hv h₀ h₁ h₂ h₃
  exact ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩

lemma ridge_diff {φ φ₁ φ₂ φ₃ : ℝ → ℝ} (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (hφ₂ : ∀ t, HasDerivAt φ₂ (φ₃ t) t) (a x y u v : E) {Λ U V Z : ℝ}
    (hΛ : 0 ≤ Λ) (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : ‖a‖ ≤ 1)
    (hu : |⟪a, u⟫| ≤ U) (hv : |⟪a, v⟫| ≤ V) (hz : |⟪a, x⟫ - ⟪a, y⟫| ≤ Z)
    (l₀ : ∀ s t, |φ s - φ t| ≤ Λ * |s - t|) (l₁ : ∀ s t, |φ₁ s - φ₁ t| ≤ Λ * |s - t|)
    (l₂ : ∀ s t, |φ₂ s - φ₂ t| ≤ Λ * |s - t|) (l₃ : ∀ s t, |φ₃ s - φ₃ t| ≤ Λ * |s - t|) :
    JetDiff (RidgeJets.value φ a) x y u v Λ Λ Λ Λ U V Z := by
  have hZ : 0 ≤ Z := (abs_nonneg _).trans hz
  have k : ∀ {ψ : ℝ → ℝ}, (∀ s t, |ψ s - ψ t| ≤ Λ * |s - t|) → |ψ ⟪a, x⟫ - ψ ⟪a, y⟫| ≤ Λ * Z :=
    fun l => (l _ _).trans (mul_le_mul_of_nonneg_left hz hΛ)
  have hΛZ : 0 ≤ Λ * Z := mul_nonneg hΛ hZ
  refine ⟨k l₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [RidgeJets.gradient_eq hφ, RidgeJets.gradient_eq hφ, ← sub_smul, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (k l₁) ha (norm_nonneg _) hΛZ).trans_eq (mul_one _)
  · rw [RidgeJets.gradient_eq hφ, RidgeJets.gradient_eq hφ, real_inner_smul_left,
      real_inner_smul_left, ← sub_mul, abs_mul]
    exact mul_le_mul (k l₁) hu (abs_nonneg _) hΛZ
  · rw [RidgeJets.gradient_eq hφ, RidgeJets.gradient_eq hφ, real_inner_smul_left,
      real_inner_smul_left, ← sub_mul, abs_mul]
    exact mul_le_mul (k l₁) hv (abs_nonneg _) hΛZ
  · rw [RidgeJets.hessian_apply hφc hφ hφ₁, RidgeJets.hessian_apply hφc hφ hφ₁, ← sub_smul,
      ← sub_mul, norm_smul, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (mul_le_mul (k l₂) hu (abs_nonneg _) hΛZ) ha (norm_nonneg _)
      (by positivity)).trans_eq (mul_one _)
  · rw [RidgeJets.hessian_apply hφc hφ hφ₁, RidgeJets.hessian_apply hφc hφ hφ₁, ← sub_smul,
      ← sub_mul, norm_smul, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (mul_le_mul (k l₂) hv (abs_nonneg _) hΛZ) ha (norm_nonneg _)
      (by positivity)).trans_eq (mul_one _)
  · rw [RidgeJets.hessian_apply hφc hφ hφ₁, RidgeJets.hessian_apply hφc hφ hφ₁,
      real_inner_smul_left, real_inner_smul_left, ← sub_mul, ← sub_mul, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (k l₂) hu (abs_nonneg _) hΛZ) hv (abs_nonneg _) (by positivity)
  · rw [RidgeJets.third_apply hφc hφ hφ₁ hφ₂, RidgeJets.third_apply hφc hφ hφ₁ hφ₂, ← sub_smul,
      ← sub_mul, ← sub_mul, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
    exact (mul_le_mul (mul_le_mul (mul_le_mul (k l₃) hu (abs_nonneg _) hΛZ) hv (abs_nonneg _)
      (by positivity)) ha (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma lipschitz_of_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {h : E → G}
    {h' : E → E →L[ℝ] G} (hd : ∀ z, HasFDerivAt h (h' z) z) {K : ℝ} (hK : ∀ z, ‖h' z‖ ≤ K)
    (x y : E) : ‖h x - h y‖ ≤ K * ‖x - y‖ :=
  (convex_univ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hd z).hasFDerivWithinAt) (fun z _ => hK z) (Set.mem_univ y) (Set.mem_univ x)

omit [FiniteDimensional ℝ E] in
lemma norm_bound (f : E → ℝ) (z u v : E) {c₀ c₁ c₂ c₃ : ℝ}
    (h₀ : |f z| ≤ c₀) (h₁ : ‖gradient f z‖ ≤ c₁) (h₂ : ‖fderiv ℝ (gradient f) z‖ ≤ c₂)
    (h₃ : ‖fderiv ℝ (fderiv ℝ (gradient f)) z‖ ≤ c₃) :
    JetBound f z u v c₀ c₁ c₂ c₃ ‖u‖ ‖v‖ := by
  have hH : ∀ w : E, ‖fderiv ℝ (gradient f) z w‖ ≤ c₂ * ‖w‖ := fun w =>
    ((fderiv ℝ (gradient f) z).le_opNorm w).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg w))
  have hg : ∀ w : E, |⟪gradient f z, w⟫| ≤ c₁ * ‖w‖ := fun w =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg w))
  refine ⟨h₀, h₁, hg u, hg v, hH u, hH v, ?_, ?_⟩
  · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hH u) (norm_nonneg v))
  · exact ((fderiv ℝ (fderiv ℝ (gradient f)) z u).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ (gradient f)) z).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right h₃ (norm_nonneg u))) (norm_nonneg v))

omit [FiniteDimensional ℝ E] in
lemma norm_diff (f : E → ℝ) (x y u v : E) {l₀ l₁ l₂ l₃ : ℝ}
    (h₀ : |f x - f y| ≤ l₀ * ‖x - y‖) (h₁ : ‖gradient f x - gradient f y‖ ≤ l₁ * ‖x - y‖)
    (h₂ : ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ l₂ * ‖x - y‖)
    (h₃ : ‖fderiv ℝ (fderiv ℝ (gradient f)) x - fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤
      l₃ * ‖x - y‖) :
    JetDiff f x y u v l₀ l₁ l₂ l₃ ‖u‖ ‖v‖ ‖x - y‖ := by
  have hH : ∀ w : E, ‖fderiv ℝ (gradient f) x w - fderiv ℝ (gradient f) y w‖ ≤
      l₂ * ‖x - y‖ * ‖w‖ := fun w => by
    have := (fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y).le_opNorm w
    rw [sub_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg w))
  have hg : ∀ w : E, |⟪gradient f x, w⟫ - ⟪gradient f y, w⟫| ≤ l₁ * ‖x - y‖ * ‖w‖ := fun w => by
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg w))
  refine ⟨h₀, h₁, hg u, hg v, hH u, hH v, ?_, ?_⟩
  · rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hH u) (norm_nonneg v))
  · have h := ((fderiv ℝ (fderiv ℝ (gradient f)) x - fderiv ℝ (fderiv ℝ (gradient f)) y) u).le_opNorm v
    have h' := (fderiv ℝ (fderiv ℝ (gradient f)) x - fderiv ℝ (fderiv ℝ (gradient f)) y).le_opNorm u
    rw [sub_apply, sub_apply] at h
    rw [sub_apply] at h'
    exact h.trans (mul_le_mul_of_nonneg_right
      (h'.trans (mul_le_mul_of_nonneg_right h₃ (norm_nonneg u))) (norm_nonneg v))

lemma product_third_lipschitz {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x y : E)
    {a₀ a₁ a₂ a₃ p₃ b₀ b₁ b₂ b₃ q₃ : ℝ}
    (ha : 0 ≤ a₀ ∧ 0 ≤ a₁ ∧ 0 ≤ a₂ ∧ 0 ≤ a₃) (hb : 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ 0 ≤ b₂ ∧ 0 ≤ b₃)
    (hp : 0 ≤ p₃) (hq : 0 ≤ q₃)
    (f₀ : ∀ z, |f z| ≤ a₀) (f₁ : ∀ z, ‖gradient f z‖ ≤ a₁)
    (f₂ : ∀ z, ‖fderiv ℝ (gradient f) z‖ ≤ a₂)
    (f₃ : ∀ z, ‖fderiv ℝ (fderiv ℝ (gradient f)) z‖ ≤ a₃)
    (f₄ : ‖fderiv ℝ (fderiv ℝ (gradient f)) x - fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ p₃ * ‖x - y‖)
    (g₀ : ∀ z, |g z| ≤ b₀) (g₁ : ∀ z, ‖gradient g z‖ ≤ b₁)
    (g₂ : ∀ z, ‖fderiv ℝ (gradient g) z‖ ≤ b₂)
    (g₃ : ∀ z, ‖fderiv ℝ (fderiv ℝ (gradient g)) z‖ ≤ b₃)
    (g₄ : ‖fderiv ℝ (fderiv ℝ (gradient g)) x - fderiv ℝ (fderiv ℝ (gradient g)) y‖ ≤ q₃ * ‖x - y‖) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun z => f z * g z))) x -
        fderiv ℝ (fderiv ℝ (gradient (fun z => f z * g z))) y‖ ≤
      (a₁ * b₃ + a₀ * q₃ + 2 * (a₂ * b₂ + a₁ * b₃) + (a₃ * b₁ + a₂ * b₂) +
        (b₁ * a₃ + b₀ * p₃) + 2 * (b₂ * a₂ + b₁ * a₃) + (b₃ * a₁ + b₂ * a₂)) * ‖x - y‖ := by
  obtain ⟨ha₀, ha₁, ha₂, ha₃⟩ := ha
  obtain ⟨hb₀, hb₁, hb₂, hb₃⟩ := hb
  have hfd := LongTails.Proofs.GradientDependentLocal.derivative_chain hf
  have hgd := LongTails.Proofs.GradientDependentLocal.derivative_chain hg
  have lip₀ : ∀ {h : E → ℝ} {c : ℝ}, (∀ z, HasFDerivAt h (innerSL ℝ (gradient h z)) z) →
      (∀ z, ‖gradient h z‖ ≤ c) → |h x - h y| ≤ c * ‖x - y‖ := by
    intro h c hd hc
    have := lipschitz_of_bound hd (fun z => by rw [innerSL_apply_norm]; exact hc z) x y
    rwa [Real.norm_eq_abs] at this
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [sub_apply, sub_apply]
  have key := product_third_diff hf hg x y u v (norm_nonneg u) (norm_nonneg v) (norm_nonneg (x - y))
    ⟨ha₀, ha₁, ha₂⟩ ⟨ha₁, ha₂, ha₃⟩ ⟨hb₀, hb₁, hb₂⟩ ⟨hb₁, hb₂, hb₃⟩
    (norm_bound f x u v (f₀ x) (f₁ x) (f₂ x) (f₃ x)) (norm_bound f y u v (f₀ y) (f₁ y) (f₂ y) (f₃ y))
    (norm_diff f x y u v (lip₀ hfd.1 f₁) (lipschitz_of_bound hfd.2.1 f₂ x y)
      (lipschitz_of_bound hfd.2.2 f₃ x y) f₄)
    (norm_bound g x u v (g₀ x) (g₁ x) (g₂ x) (g₃ x)) (norm_bound g y u v (g₀ y) (g₁ y) (g₂ y) (g₃ y))
    (norm_diff g x y u v (lip₀ hgd.1 g₁) (lipschitz_of_bound hgd.2.1 g₂ x y)
      (lipschitz_of_bound hgd.2.2 g₃ x y) g₄)
  refine key.trans (le_of_eq ?_)
  ring

end LongTails.Proofs.ThirdOrderJetDifference
