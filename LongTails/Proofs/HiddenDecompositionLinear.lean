import LongTails.Proofs.HiddenDecompositionPolynomial
import LongTails.Proofs.QuadraticTemporalEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace

namespace OracleTemplate.HiddenDecompositionLinear

variable {ι : Type*} [Fintype ι]

noncomputable def diagonal (ζ : ι → ℂ) :
    EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι where
  toFun x := WithLp.toLp 2 (fun i => ζ i * x i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' r x := by ext i; simp [mul_left_comm]

omit [Fintype ι] in
@[simp]
lemma diagonal_apply (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) (i : ι) :
    diagonal ζ x i = ζ i * x i := rfl

lemma diagonal_norm_sq (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    ‖diagonal ζ x‖ ^ 2 = ∑ i, ‖ζ i‖ ^ 2 * ‖x i‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, mul_pow]

lemma diagonal_inner (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    ⟪diagonal ζ x, x⟫ = ∑ i, (ζ i).re * ‖x i‖ ^ 2 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonal_apply, real_inner_eq_re_inner ℂ]
  simp [RCLike.inner_apply, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  ring

lemma diagonal_lipschitz (ζ : ι → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hζ : ∀ i, ‖ζ i‖ ≤ L) (x y : EuclideanSpace ℂ ι) :
    ‖diagonal ζ x - diagonal ζ y‖ ≤ L * ‖x - y‖ := by
  rw [← map_sub]
  have hs : ‖diagonal ζ (x - y)‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    rw [diagonal_norm_sq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [hζ i, norm_nonneg (ζ i)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  simpa only [mul_pow] using hs

lemma diagonal_strong (ζ : ι → ℂ) {μ : ℝ}
    (hζ : ∀ i, μ ≤ (ζ i).re) (x y : EuclideanSpace ℂ ι) :
    μ * ‖x - y‖ ^ 2 ≤ ⟪diagonal ζ x - diagonal ζ y, x - y⟫ := by
  rw [← map_sub, diagonal_inner, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hζ i) (sq_nonneg _)

noncomputable def polynomialVector (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι)
    (p : Polynomial ℝ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (p.map Complex.ofRealHom).eval (ζ i) * x i)

noncomputable def weightedRoot (w : ι → ℝ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (Real.sqrt (w i) : ℂ))

lemma weightedRoot_norm_sq (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ‖weightedRoot w‖ ^ 2 = ∑ i, w i := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change ‖(Real.sqrt (w i) : ℂ)‖ ^ 2 = w i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw i)]

lemma polynomialVector_weighted_norm (ζ : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (p : Polynomial ℝ) :
    ‖polynomialVector ζ (weightedRoot w) p‖ ^ 2 =
      ∑ i, w i * ‖(p.map Complex.ofRealHom).eval (ζ i)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change ‖(p.map Complex.ofRealHom).eval (ζ i) * (Real.sqrt (w i) : ℂ)‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw i), mul_comm]

omit [Fintype ι] in
lemma polynomialVector_one (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    polynomialVector ζ x 1 = x := by
  ext i
  simp [polynomialVector]

omit [Fintype ι] in
lemma polynomialVector_add (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) (p q : Polynomial ℝ) :
    polynomialVector ζ x (p + q) = polynomialVector ζ x p + polynomialVector ζ x q := by
  ext i
  simp [polynomialVector, add_mul]

omit [Fintype ι] in
lemma polynomialVector_sub (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) (p q : Polynomial ℝ) :
    polynomialVector ζ x (p - q) = polynomialVector ζ x p - polynomialVector ζ x q := by
  ext i
  simp [polynomialVector, sub_mul]

omit [Fintype ι] in
lemma polynomialVector_X_mul (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) (p : Polynomial ℝ) :
    polynomialVector ζ x (Polynomial.X * p) = diagonal ζ (polynomialVector ζ x p) := by
  ext i
  simp [polynomialVector, mul_assoc]

lemma finite_linear_witness (n : ℕ) (μ L s : ℝ)
    (hμ : 0 < μ) (hμs : μ ≤ s) (hsL : 4 * s ≤ L) :
    ∃ (ζ : HiddenDecompositionPolynomial.SpectralIndex n → ℂ)
      (x : EuclideanSpace ℂ (HiddenDecompositionPolynomial.SpectralIndex n)),
      (∀ i, μ ≤ (ζ i).re ∧ (ζ i).re ≤ L ∧ |(ζ i).im| ≤ s) ∧
      ‖x‖ = 1 ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ n → p.eval 0 = 1 →
        1 / (3 * Real.exp (6 * (n : ℝ) * μ / Real.sqrt (L * s))) ≤
          ‖polynomialVector ζ x p‖ := by
  obtain ⟨ζ, w, hbox, hw, hsum, hp⟩ :=
    HiddenDecompositionPolynomial.finite_hard_spectrum n μ L s hμ hμs hsL
  refine ⟨ζ, weightedRoot w, hbox, ?_, ?_⟩
  · have h := weightedRoot_norm_sq w hw
    rw [hsum] at h
    nlinarith [norm_nonneg (weightedRoot w)]
  · intro p hdeg hzero
    have h := hp p hdeg hzero
    rw [← polynomialVector_weighted_norm ζ w hw p] at h
    have hC : 0 < 3 * Real.exp (6 * (n : ℝ) * μ / Real.sqrt (L * s)) := by positivity
    apply (div_le_iff₀ hC).mpr
    have hn := norm_nonneg (polynomialVector ζ (weightedRoot w) p)
    have hh := mul_nonneg hC.le hn
    nlinarith [sq_nonneg (3 * Real.exp (6 * (n : ℝ) * μ / Real.sqrt (L * s)) *
      ‖polynomialVector ζ (weightedRoot w) p‖ - 1)]

lemma diagonal_real_symmetric (r : ι → ℝ) :
    (diagonal (fun i => (r i : ℂ))).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪(r i : ℂ) * x i, y i⟫ = ⟪x i, (r i : ℂ) * y i⟫
  rw [← Complex.real_smul, ← Complex.real_smul,
    real_inner_smul_left, real_inner_smul_right]

set_option maxHeartbeats 800000 in
lemma diagonal_real_quadratic_gradient (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (u x : EuclideanSpace ℂ ι) :
    HasGradientAt
      (fun y => ‖diagonal (fun i => (Real.sqrt (r i) : ℂ)) (y - u)‖ ^ 2 / 2)
      (diagonal (fun i => (r i : ℂ)) (x - u)) x := by
  let D := (diagonal (fun i => (Real.sqrt (r i) : ℂ))).toContinuousLinearMap
  have hD : D.adjoint = D :=
    (diagonal_real_symmetric (fun i => Real.sqrt (r i))).clm_adjoint_eq
  have h := TemporalDiscrepancy.factorized_quadratic_gradient D u x
  rw [hD] at h
  have he : D (D (x - u)) = diagonal (fun i => (r i : ℂ)) (x - u) := by
    ext i
    change (Real.sqrt (r i) : ℂ) * ((Real.sqrt (r i) : ℂ) * (x - u) i) =
      (r i : ℂ) * (x - u) i
    rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (hr i)]
  rw [he] at h
  exact h

set_option maxHeartbeats 800000 in
lemma diagonal_potential_decomposition (ζ : ι → ℂ) {L s : ℝ}
    (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hζ : ∀ i, 0 ≤ (ζ i).re ∧ (ζ i).re ≤ L ∧ |(ζ i).im| ≤ s)
    (u : EuclideanSpace ℂ ι) :
    ∃ φ : EuclideanSpace ℂ ι → ℝ,
      (∀ x, HasGradientAt φ (gradient φ x) x) ∧
      (∀ x, gradient φ x = diagonal (fun i => ((ζ i).re : ℂ)) (x - u)) ∧
      (∀ x y, ‖gradient φ x - gradient φ y‖ ≤ L * ‖x - y‖) ∧
      (∀ x y,
        ‖(diagonal ζ (x - u) - gradient φ x) - (diagonal ζ (y - u) - gradient φ y)‖ ≤
          s * ‖x - y‖) := by
  let φ := fun x => ‖diagonal (fun i => (Real.sqrt ((ζ i).re) : ℂ)) (x - u)‖ ^ 2 / 2
  have hg := diagonal_real_quadratic_gradient (fun i => (ζ i).re) (fun i => (hζ i).1) u
  have hgrad : ∀ x, gradient φ x = diagonal (fun i => ((ζ i).re : ℂ)) (x - u) :=
    fun x => (hg x).gradient
  refine ⟨φ, (fun x => by rw [hgrad]; exact hg x), hgrad, ?_, ?_⟩
  · intro x y
    rw [hgrad, hgrad]
    have h := diagonal_lipschitz (fun i => ((ζ i).re : ℂ)) hL
      (fun i => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hζ i).1]
        using (hζ i).2.1) (x - u) (y - u)
    simpa only [sub_sub_sub_cancel_right] using h
  · intro x y
    rw [hgrad, hgrad]
    let σ := fun i => ζ i - ((ζ i).re : ℂ)
    have hn : ∀ i, ‖σ i‖ ≤ s := by
      intro i
      have h := Complex.norm_le_abs_re_add_abs_im (σ i)
      simp only [σ, Complex.sub_re, Complex.ofReal_re, sub_self, abs_zero,
        Complex.sub_im, Complex.ofReal_im, sub_zero, zero_add] at h
      exact h.trans (hζ i).2.2
    have he : ∀ x, diagonal ζ (x - u) - diagonal (fun i => ((ζ i).re : ℂ)) (x - u) =
        diagonal σ (x - u) := by
      intro x
      ext i
      simp [σ, sub_mul]
      ring
    rw [he, he]
    simpa only [sub_sub_sub_cancel_right] using diagonal_lipschitz σ hs hn (x - u) (y - u)

omit [Fintype ι] in
lemma polynomialVector_zero (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    polynomialVector ζ x 0 = 0 := by
  ext i
  simp [polynomialVector]

omit [Fintype ι] in
lemma polynomialVector_smul (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) (r : ℝ)
    (p : Polynomial ℝ) :
    polynomialVector ζ x (r • p) = r • polynomialVector ζ x p := by
  ext i
  simp [polynomialVector, Polynomial.smul_eq_C_mul, Complex.real_smul, mul_assoc]

omit [Fintype ι] in
lemma polynomialVector_power (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) (n : ℕ) :
    polynomialVector ζ x (Polynomial.X ^ n) = (diagonal ζ : _ → _)^[n] x := by
  induction n with
  | zero => simpa using polynomialVector_one ζ x
  | succ n ih =>
      rw [pow_succ', polynomialVector_X_mul, ih, Function.iterate_succ_apply']

omit [Fintype ι] in
lemma polynomialVector_diagonal (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) (p : Polynomial ℝ) :
    polynomialVector ζ (diagonal ζ x) p = polynomialVector ζ x (Polynomial.X * p) := by
  ext i
  simp [polynomialVector]
  ring

omit [Fintype ι] in
lemma polynomialVector_smul_root (ζ : ι → ℂ) (x : EuclideanSpace ℂ ι) (r : ℝ)
    (p : Polynomial ℝ) :
    polynomialVector ζ (r • x) p = r • polynomialVector ζ x p := by
  ext i
  simp [polynomialVector, Complex.real_smul]
  ring

lemma diagonal_injective (ζ : ι → ℂ) {μ : ℝ} (hμ : 0 < μ)
    (hζ : ∀ i, μ ≤ (ζ i).re) : Function.Injective (diagonal ζ) := by
  intro x y hxy
  have h := diagonal_strong ζ hζ x y
  rw [hxy, sub_self, inner_zero_left] at h
  have hn : ‖x - y‖ ^ 2 = 0 :=
    le_antisymm ((mul_le_mul_iff_of_pos_left hμ).mp (by simpa using h)) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

lemma diagonal_residual_inner (ζ : ι → ℂ) (x y : EuclideanSpace ℂ ι) :
    ⟪(diagonal ζ x - diagonal (fun i => ((ζ i).re : ℂ)) x) -
      (diagonal ζ y - diagonal (fun i => ((ζ i).re : ℂ)) y), x - y⟫ = 0 := by
  have he : (diagonal ζ x - diagonal (fun i => ((ζ i).re : ℂ)) x) -
      (diagonal ζ y - diagonal (fun i => ((ζ i).re : ℂ)) y) =
      diagonal (fun i => ζ i - ((ζ i).re : ℂ)) (x - y) := by
    ext i
    simp [sub_mul]
  rw [he, diagonal_inner]
  simp

end OracleTemplate.HiddenDecompositionLinear
