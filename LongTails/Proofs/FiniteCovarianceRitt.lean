import LongTails.Proofs.GeometricBlockSector
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace OracleTemplate.MarkovProduct

section PositiveBounds

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_positive_map_selfAdjoint_le (Φ : A →L[ℂ] A) (hmono : Monotone Φ)
    (hself : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Φ a)) (hone : Φ 1 ≤ 1)
    (a : A) (ha : IsSelfAdjoint a) : ‖Φ a‖ ≤ ‖a‖ := by
  nontriviality A
  have hs : Φ (algebraMap ℝ A ‖a‖) = ‖a‖ • Φ 1 := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, Complex.coe_smul]
  have hu : Φ a ≤ algebraMap ℝ A ‖a‖ := by
    calc
      Φ a ≤ Φ (algebraMap ℝ A ‖a‖) := hmono (ha.le_algebraMap_norm_self a)
      _ = ‖a‖ • Φ 1 := hs
      _ ≤ ‖a‖ • (1 : A) := smul_le_smul_of_nonneg_left hone (norm_nonneg a)
      _ = _ := (Algebra.algebraMap_eq_smul_one _).symm
  have hl : -algebraMap ℝ A ‖a‖ ≤ Φ a := by
    calc
      -algebraMap ℝ A ‖a‖ = -(‖a‖ • (1 : A)) := by rw [Algebra.algebraMap_eq_smul_one]
      _ ≤ -(‖a‖ • Φ 1) := neg_le_neg (smul_le_smul_of_nonneg_left hone (norm_nonneg a))
      _ = Φ (-algebraMap ℝ A ‖a‖) := by rw [map_neg, hs]
      _ ≤ Φ a := hmono (ha.neg_algebraMap_norm_le_self a)
  have hn := IsSelfAdjoint.norm_le_max_of_le_of_le hl hu (hself a ha)
  simp only [norm_neg, max_self] at hn
  exact hn.trans (by simp [norm_algebraMap'])

open scoped ComplexStarModule in
lemma norm_positive_map_le_two (Φ : A →L[ℂ] A) (hmono : Monotone Φ)
    (hself : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Φ a)) (hone : Φ 1 ≤ 1) :
    ‖Φ‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  calc
    ‖Φ a‖ = ‖Φ ((ℜ a : A) + Complex.I • (ℑ a : A))‖ := by
      rw [realPart_add_I_smul_imaginaryPart]
    _ ≤ ‖Φ (ℜ a : A)‖ + ‖Φ (ℑ a : A)‖ := by
      rw [map_add, map_smul]
      simpa [norm_smul] using norm_add_le (Φ (ℜ a : A)) (Complex.I • Φ (ℑ a : A))
    _ ≤ ‖(ℜ a : A)‖ + ‖(ℑ a : A)‖ := add_le_add
      (norm_positive_map_selfAdjoint_le Φ hmono hself hone _ (ℜ a).2)
      (norm_positive_map_selfAdjoint_le Φ hmono hself hone _ (ℑ a).2)
    _ ≤ 2 * ‖a‖ := by
      have hr := realPart.norm_le a
      have hi := imaginaryPart.norm_le a
      change ‖(ℜ a : A)‖ ≤ ‖a‖ at hr
      change ‖(ℑ a : A)‖ ≤ ‖a‖ at hi
      linarith

noncomputable def covarianceCorrection (Ψ Θ : A →L[ℂ] A) : ℕ → A →L[ℂ] A
  | 0 => 0
  | n + 1 => Θ * Ψ ^ n + Ψ * covarianceCorrection Ψ Θ n

omit [StarOrderedRing A] in
lemma monotone_clm_pow (Ψ : A →L[ℂ] A) (hΨ : Monotone Ψ) :
    ∀ n : ℕ, Monotone (Ψ ^ n) := by
  intro n
  induction n with
  | zero => simpa using (monotone_id : Monotone (id : A → A))
  | succ n ih =>
    intro a b hab
    simpa only [pow_succ', mul_apply_eq_comp] using hΨ (ih hab)

omit [StarOrderedRing A] in
lemma clm_pow_one_le (Ψ : A →L[ℂ] A) (hΨ : Monotone Ψ) (hone : Ψ 1 ≤ 1) :
    ∀ n, (Ψ ^ n) 1 ≤ 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [pow_succ', mul_apply_eq_comp] using (hΨ ih).trans hone

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjoint_clm_pow (Ψ : A →L[ℂ] A)
    (hΨ : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Ψ a)) :
    ∀ n a, IsSelfAdjoint a → IsSelfAdjoint ((Ψ ^ n) a) := by
  intro n
  induction n with
  | zero => intro a ha; simpa using ha
  | succ n ih => intro a ha; simpa only [pow_succ', mul_apply_eq_comp] using hΨ _ (ih a ha)

lemma covarianceCorrection_monotone (Ψ Θ : A →L[ℂ] A)
    (hΨ : Monotone Ψ) (hΘ : Monotone Θ) : ∀ n : ℕ, Monotone (covarianceCorrection Ψ Θ n) := by
  intro n
  induction n with
  | zero => intro a b hab; simp [covarianceCorrection]
  | succ n ih =>
    intro a b hab
    simpa only [covarianceCorrection, add_apply, mul_apply_eq_comp] using
      add_le_add (hΘ (monotone_clm_pow Ψ hΨ n hab)) (hΨ (ih hab))

omit [PartialOrder A] [StarOrderedRing A] in
lemma covarianceCorrection_selfAdjoint (Ψ Θ : A →L[ℂ] A)
    (hΨ : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Ψ a))
    (hΘ : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Θ a)) :
    ∀ n a, IsSelfAdjoint a → IsSelfAdjoint (covarianceCorrection Ψ Θ n a) := by
  intro n
  induction n with
  | zero => intro a ha; simp [covarianceCorrection]
  | succ n ih =>
    intro a ha
    simpa only [covarianceCorrection, add_apply, mul_apply_eq_comp] using
      (hΘ _ (selfAdjoint_clm_pow Ψ hΨ n a ha)).add (hΨ _ (ih a ha))

lemma covarianceCorrection_one_le (Ψ Θ : A →L[ℂ] A)
    (hΨ : Monotone Ψ) (hΘ : Monotone Θ) (hone : Ψ 1 ≤ 1)
    (hgap : Θ 1 ≤ 1 - Ψ 1) :
    ∀ n, covarianceCorrection Ψ Θ n 1 ≤ 1 - (Ψ ^ n) 1 := by
  intro n
  induction n with
  | zero => simp [covarianceCorrection]
  | succ n ih =>
    have hfirst := (hΘ (clm_pow_one_le Ψ hΨ hone n)).trans hgap
    have hsecond := hΨ ih
    calc
      covarianceCorrection Ψ Θ (n + 1) 1 ≤ (1 - Ψ 1) + Ψ (1 - (Ψ ^ n) 1) :=
        add_le_add hfirst hsecond
      _ = 1 - (Ψ ^ (n + 1)) 1 := by
        rw [map_sub, pow_succ', mul_apply_eq_comp]
        abel

lemma norm_covarianceCorrection_le (Ψ Θ : A →L[ℂ] A)
    (hΨ : Monotone Ψ) (hΘ : Monotone Θ)
    (hsΨ : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Ψ a))
    (hsΘ : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Θ a))
    (hone : Ψ 1 ≤ 1) (hgap : Θ 1 ≤ 1 - Ψ 1) (n : ℕ) :
    ‖covarianceCorrection Ψ Θ n‖ ≤ 2 := by
  apply norm_positive_map_le_two _ (covarianceCorrection_monotone Ψ Θ hΨ hΘ n)
    (covarianceCorrection_selfAdjoint Ψ Θ hsΨ hsΘ n)
  have hp : 0 ≤ (Ψ ^ n) 1 := by
    simpa using monotone_clm_pow Ψ hΨ n (show (0 : A) ≤ 1 by exact zero_le_one)
  exact (covarianceCorrection_one_le Ψ Θ hΨ hΘ hone hgap n).trans (sub_le_self _ hp)

noncomputable def covariancePolynomial (Ψ Θ : A →L[ℂ] A) (z : ℂ) : A →L[ℂ] A :=
  Ψ + z • (1 - Ψ - Θ) + z ^ 2 • Θ

noncomputable def covarianceTangent (Ψ Θ : A →L[ℂ] A) : ℕ → A →L[ℂ] A
  | 0 => 0
  | n + 1 => (1 - Ψ - Θ) * Ψ ^ n + Ψ * covarianceTangent Ψ Θ n

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma covariancePolynomial_zero (Ψ Θ : A →L[ℂ] A) :
    covariancePolynomial Ψ Θ 0 = Ψ := by
  ext a
  simp [covariancePolynomial]

omit [PartialOrder A] [StarOrderedRing A] in
lemma differentiable_covariancePolynomial (Ψ Θ : A →L[ℂ] A) :
    Differentiable ℂ (covariancePolynomial Ψ Θ) := by
  unfold covariancePolynomial
  fun_prop

omit [PartialOrder A] [StarOrderedRing A] in
lemma hasDerivAt_covariancePolynomial (Ψ Θ : A →L[ℂ] A) :
    HasDerivAt (covariancePolynomial Ψ Θ) (1 - Ψ - Θ) 0 := by
  have h := ((hasDerivAt_const (0 : ℂ) Ψ).add
    ((hasDerivAt_id (0 : ℂ)).smul_const (1 - Ψ - Θ))).add
    (((hasDerivAt_id (0 : ℂ)).pow 2).smul_const Θ)
  convert! h using 1
  ext a
  simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma hasDerivAt_covariancePolynomial_pow (Ψ Θ : A →L[ℂ] A) :
    ∀ n, HasDerivAt (fun z => covariancePolynomial Ψ Θ z ^ n) (covarianceTangent Ψ Θ n) 0 := by
  intro n
  induction n with
  | zero => simpa [covarianceTangent] using hasDerivAt_const (0 : ℂ) (1 : A →L[ℂ] A)
  | succ n ih =>
    simpa only [pow_succ', covariancePolynomial_zero, covarianceTangent] using!
      (hasDerivAt_covariancePolynomial Ψ Θ).mul ih

omit [PartialOrder A] [StarOrderedRing A] in
lemma covarianceTangent_add_correction (Ψ Θ : A →L[ℂ] A) (n : ℕ) :
    covarianceTangent Ψ Θ (n + 1) + covarianceCorrection Ψ Θ (n + 1) =
      (n + 1) • (Ψ ^ n * (1 - Ψ)) := by
  induction n with
  | zero => simp [covarianceTangent, covarianceCorrection]
  | succ n ih =>
    have hcomm : (1 - Ψ) * Ψ ^ (n + 1) = Ψ ^ (n + 1) * (1 - Ψ) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, ← pow_succ', ← pow_succ]
    calc
      _ = (1 - Ψ) * Ψ ^ (n + 1) + Ψ *
        (covarianceTangent Ψ Θ (n + 1) + covarianceCorrection Ψ Θ (n + 1)) := by
          change ((1 - Ψ - Θ) * Ψ ^ (n + 1) + Ψ * covarianceTangent Ψ Θ (n + 1)) +
            (Θ * Ψ ^ (n + 1) + Ψ * covarianceCorrection Ψ Θ (n + 1)) = _
          simp only [sub_mul, mul_add]
          abel
      _ = Ψ ^ (n + 1) * (1 - Ψ) + Ψ * ((n + 1) • (Ψ ^ n * (1 - Ψ))) := by
        rw [hcomm, ih]
      _ = (n + 1 + 1) • (Ψ ^ (n + 1) * (1 - Ψ)) := by
        have hm (S : A →L[ℂ] A) : Ψ * ((n + 1) • S) = (n + 1) • (Ψ * S) := by
          ext a
          simp only [mul_apply_eq_comp, smul_apply, map_nsmul]
        rw [hm, ← mul_assoc, ← pow_succ', add_nsmul, one_nsmul]
        simp only [add_nsmul, one_nsmul, add_assoc, add_comm, add_left_comm]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_covarianceTangent_le (Ψ Θ : A →L[ℂ] A)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖covariancePolynomial Ψ Θ z‖ ≤ 1) (n : ℕ) :
    ‖covarianceTangent Ψ Θ n‖ ≤ 2 := by
  have hd : Differentiable ℂ (fun z => covariancePolynomial Ψ Θ z ^ n) :=
    (differentiable_covariancePolynomial Ψ Θ).pow n
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ),
      ‖covariancePolynomial Ψ Θ z ^ n‖ ≤ 1 := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 / 2 := le_of_eq (by simpa [Metric.mem_sphere, dist_zero_right] using hz)
    clear hd
    induction n with
    | zero => exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans (by nlinarith [hdisk z hz', norm_nonneg (covariancePolynomial Ψ Θ z), norm_nonneg (covariancePolynomial Ψ Θ z ^ n)])
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 2)
    hd.diffContOnCl hbound
  rw [(hasDerivAt_covariancePolynomial_pow Ψ Θ n).deriv] at hc
  norm_num at hc ⊢
  exact hc

lemma covariance_ritt_bound (Ψ Θ : A →L[ℂ] A)
    (hΨ : Monotone Ψ) (hΘ : Monotone Θ)
    (hsΨ : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Ψ a))
    (hsΘ : ∀ a, IsSelfAdjoint a → IsSelfAdjoint (Θ a))
    (hone : Ψ 1 ≤ 1) (hgap : Θ 1 ≤ 1 - Ψ 1)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖covariancePolynomial Ψ Θ z‖ ≤ 1) (n : ℕ) :
    (n + 1 : ℝ) * ‖Ψ ^ n - Ψ ^ (n + 1)‖ ≤ 4 := by
  have hsum := norm_add_le (covarianceTangent Ψ Θ (n + 1))
    (covarianceCorrection Ψ Θ (n + 1))
  rw [covarianceTangent_add_correction, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul] at hsum
  have heq : Ψ ^ n * (1 - Ψ) = Ψ ^ n - Ψ ^ (n + 1) := by
    rw [mul_sub, mul_one, pow_succ]
  rw [heq] at hsum
  push_cast at hsum
  linarith [norm_covarianceTangent_le Ψ Θ hdisk (n + 1),
    norm_covarianceCorrection_le Ψ Θ hΨ hΘ hsΨ hsΘ hone hgap (n + 1)]

end PositiveBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma finite_weighted_inner_bound {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ i, 0 ≤ w i) (u v : Ω → E) (X : E →L[ℂ] E)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : ∑ i, w i * ‖u i‖ ^ 2 ≤ C ^ 2)
    (hv : ∑ i, w i * ‖v i‖ ^ 2 ≤ D ^ 2) :
    ‖∑ i, (w i : ℂ) * inner ℂ (u i) (X (v i))‖ ≤ ‖X‖ * C * D := by
  have hcs : (∑ i, w i * ‖u i‖ * ‖v i‖) ^ 2 ≤
      (∑ i, w i * ‖u i‖ ^ 2) * (∑ i, w i * ‖v i‖ ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i hi; exact mul_nonneg (hw i) (sq_nonneg _)
    · intro i hi; exact mul_nonneg (hw i) (sq_nonneg _)
    · intro i hi; exact le_of_eq (by ring)
  have hprod : (∑ i, w i * ‖u i‖ ^ 2) * (∑ i, w i * ‖v i‖ ^ 2) ≤ C ^ 2 * D ^ 2 :=
    mul_le_mul hu hv (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) (sq_nonneg C)
  have hs : ∑ i, w i * ‖u i‖ * ‖v i‖ ≤ C * D := by
    nlinarith [mul_nonneg hC hD]
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * inner ℂ (u i) (X (v i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖X‖ * (w i * ‖u i‖ * ‖v i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      have hb := (norm_inner_le_norm (𝕜 := ℂ) (u i) (X (v i))).trans
        (mul_le_mul_of_nonneg_left (X.le_opNorm (v i)) (norm_nonneg (u i)))
      convert mul_le_mul_of_nonneg_left hb (hw i) using 1
      ring
    _ = ‖X‖ * (∑ i, w i * ‖u i‖ * ‖v i‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖X‖ * C * D := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (norm_nonneg X)

noncomputable def dualConjugation (W : E →L[ℂ] E) :
    (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) W.adjoint W

@[simp] lemma dualConjugation_apply (W X : E →L[ℂ] E) :
    dualConjugation W X = W.adjoint * X * W := rfl

lemma norm_dualConjugation_le (W : E →L[ℂ] E) : ‖dualConjugation W‖ ≤ ‖W‖ ^ 2 := by
  simpa only [dualConjugation, LinearIsometryEquiv.norm_map, pow_two] using
    ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ (E →L[ℂ] E) W.adjoint W

omit [CompleteSpace E] in
lemma norm_operator_le_of_inner (T : E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, ‖inner ℂ x (T y)‖ ≤ C * ‖x‖ * ‖y‖) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro y
  by_cases hy : ‖T y‖ = 0
  · rw [hy]
    positivity
  · have hp : 0 < ‖T y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
    have hb := h (T y) y
    rw [← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm] at hb
    apply le_of_mul_le_mul_left (a := ‖T y‖) _ hp
    nlinarith

lemma inner_dualConjugation (W X : E →L[ℂ] E) (x y : E) :
    inner ℂ x (dualConjugation W X y) = inner ℂ (W x) (X (W y)) := by
  change inner ℂ x (W.adjoint (X (W y))) = _
  exact W.adjoint_inner_right _ _

lemma dualConjugation_mul (V W : E →L[ℂ] E) :
    dualConjugation (V * W) = dualConjugation W * dualConjugation V := by
  apply ContinuousLinearMap.ext
  intro X
  simp only [mul_apply_eq_comp, dualConjugation_apply]
  rw [show (V * W).adjoint = W.adjoint * V.adjoint by
    exact ContinuousLinearMap.adjoint_comp V W]
  noncomm_ring

noncomputable def finiteCovariance {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  ∑ i, (w i : ℂ) • dualConjugation (W i)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
lemma norm_finiteCovariance_le {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hW : ∀ i, ‖W i‖ ≤ 1) :
    ‖finiteCovariance w W‖ ≤ 1 := by
  let : NormedSpace ℂ (E →L[ℂ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedSpace ℂ ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedSpace
  unfold finiteCovariance
  calc
    ‖∑ i, (w i : ℂ) • dualConjugation (W i)‖ ≤
        ∑ i, ‖(w i : ℂ) • dualConjugation (W i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      have hb : ‖dualConjugation (W i)‖ ≤ 1 := by
        have hn := norm_dualConjugation_le (W i)
        nlinarith [hW i, norm_nonneg (W i)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (hw i)
    _ = 1 := hs

lemma dualConjugation_monotone (W : E →L[ℂ] E) : Monotone (dualConjugation W) := by
  intro X Y hXY
  simpa only [dualConjugation_apply, ContinuousLinearMap.star_eq_adjoint] using
    star_left_conjugate_le_conjugate hXY W

lemma dualConjugation_selfAdjoint (W X : E →L[ℂ] E) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (dualConjugation W X) := by
  exact hX.adjoint_conj W

lemma finiteCovariance_monotone {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E) (hw : ∀ i, 0 ≤ w i) :
    Monotone (finiteCovariance w W) := by
  intro X Y hXY
  simp only [finiteCovariance, sum_apply, smul_apply]
  apply Finset.sum_le_sum
  intro i hi
  rw [Complex.coe_smul, Complex.coe_smul]
  exact smul_le_smul_of_nonneg_left (dualConjugation_monotone (W i) hXY) (hw i)

lemma finiteCovariance_selfAdjoint {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (finiteCovariance w W X) := by
  simp only [finiteCovariance, sum_apply, smul_apply]
  apply isSelfAdjoint_sum
  intro i hi
  rw [Complex.coe_smul]
  exact (IsSelfAdjoint.all (w i)).smul (dualConjugation_selfAdjoint (W i) X hX)

lemma inner_finiteCovariance {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E) (X : E →L[ℂ] E) (x y : E) :
    inner ℂ x (finiteCovariance w W X y) =
      ∑ i, (w i : ℂ) * inner ℂ (W i x) (X (W i y)) := by
  simp only [finiteCovariance, sum_apply, smul_apply, inner_sum,
    inner_smul_right, inner_dualConjugation]

lemma finiteCovariance_one_re {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E) (x : E) :
    (inner ℂ x (finiteCovariance w W 1 x)).re = ∑ i, w i * ‖W i x‖ ^ 2 := by
  rw [inner_finiteCovariance]
  change Complex.reCLM (∑ i, (w i : ℂ) * inner ℂ (W i x) (W i x)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change ((w i : ℂ) * inner ℂ (W i x) (W i x)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show (inner ℂ (W i x) (W i x)).re = ‖W i x‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) _]

lemma finiteCovariance_one_le {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E)
    (henergy : ∀ x, ∑ i, w i * ‖W i x‖ ^ 2 ≤ ‖x‖ ^ 2) :
    finiteCovariance w W 1 ≤ 1 := by
  apply ContinuousLinearMap.le_def.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(IsSelfAdjoint.one (E →L[ℂ] E)).sub (finiteCovariance_selfAdjoint w W 1 (IsSelfAdjoint.one _)), ?_⟩
  intro x
  change 0 ≤ RCLike.re (inner ℂ ((1 - finiteCovariance w W 1) x) x)
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ x ((1 - finiteCovariance w W 1) x)).re
  rw [sub_apply, one_apply_eq_self, inner_sub_right, Complex.sub_re, finiteCovariance_one_re]
  rw [show (inner ℂ x x).re = ‖x‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) _]
  exact sub_nonneg.mpr (henergy x)

lemma finiteCovariance_gap_le {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E)
    (henergy : ∀ x, (∑ i, w i * ‖(1 - W i) x‖ ^ 2) +
      (∑ i, w i * ‖W i x‖ ^ 2) ≤ ‖x‖ ^ 2) :
    finiteCovariance w (fun i => 1 - W i) 1 ≤ 1 - finiteCovariance w W 1 := by
  apply ContinuousLinearMap.le_def.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨((IsSelfAdjoint.one (E →L[ℂ] E)).sub (finiteCovariance_selfAdjoint w W 1 (IsSelfAdjoint.one _))).sub
    (finiteCovariance_selfAdjoint w (fun i => 1 - W i) 1 (IsSelfAdjoint.one _)), ?_⟩
  intro x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  simp only [sub_apply, one_apply_eq_self, inner_sub_right, map_sub, inner_self_eq_norm_sq]
  change 0 ≤ ‖x‖ ^ 2 - (inner ℂ x (finiteCovariance w W 1 x)).re -
    (inner ℂ x (finiteCovariance w (fun i => 1 - W i) 1 x)).re
  rw [finiteCovariance_one_re, finiteCovariance_one_re]
  linarith [henergy x]

lemma covariancePolynomial_dual_apply (W X : E →L[ℂ] E) (z : ℂ) :
    covariancePolynomial (dualConjugation W) (dualConjugation (1 - W)) z X =
      (W.adjoint + z • (1 - W.adjoint)) * X * (W + z • (1 - W)) := by
  simp only [covariancePolynomial, add_apply, smul_apply, sub_apply, one_apply_eq_self,
    dualConjugation_apply, map_sub, ContinuousLinearMap.adjoint_one]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, smul_add, smul_sub]
  module

lemma covariancePolynomial_finiteCovariance {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E) (hs : ∑ i, w i = 1) (z : ℂ) :
    covariancePolynomial (finiteCovariance w W) (finiteCovariance w (fun i => 1 - W i)) z =
      ∑ i, (w i : ℂ) • covariancePolynomial (dualConjugation (W i))
        (dualConjugation (1 - W i)) z := by
  have hc : ∑ i, (w i : ℂ) = 1 := by exact_mod_cast hs
  unfold covariancePolynomial finiteCovariance
  simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [smul_comm (w _ : ℂ) z, smul_comm (w _ : ℂ) (z ^ 2)]
  simp_rw [← Finset.smul_sum]
  rw [← Finset.sum_smul, hc, one_smul]

lemma inner_covariancePolynomial_dual (W X : E →L[ℂ] E) (z : ℂ) (x y : E) :
    inner ℂ x (covariancePolynomial (dualConjugation W) (dualConjugation (1 - W)) z X y) =
      inner ℂ ((W + (starRingEnd ℂ z) • (1 - W)) x)
        (X ((W + z • (1 - W)) y)) := by
  have ha : (W + (starRingEnd ℂ z) • (1 - W)).adjoint =
      W.adjoint + z • (1 - W.adjoint) := by
    rw [map_add, map_smulₛₗ]
    simp
  rw [covariancePolynomial_dual_apply, ← ha]
  exact (W + (starRingEnd ℂ z) • (1 - W)).adjoint_inner_right _ _

lemma norm_covariancePolynomial_finite_le {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ∀ x,
      ∑ i, w i * ‖(W i + z • (1 - W i)) x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖covariancePolynomial (finiteCovariance w W)
      (finiteCovariance w (fun i => 1 - W i)) z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro X
  simp only [one_mul]
  apply norm_operator_le_of_inner _ (norm_nonneg X)
  intro x y
  rw [covariancePolynomial_finiteCovariance w W hs]
  simp only [sum_apply, smul_apply, inner_sum, inner_smul_right,
    inner_covariancePolynomial_dual]
  apply finite_weighted_inner_bound w hw _ _ X (norm_nonneg x) (norm_nonneg y)
  · exact hdisk _ (by simpa using hz) x
  · exact hdisk z hz y

lemma finite_covariance_ritt {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (W : Ω → E →L[ℂ] E) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hgap : ∀ x, (∑ i, w i * ‖(1 - W i) x‖ ^ 2) +
      (∑ i, w i * ‖W i x‖ ^ 2) ≤ ‖x‖ ^ 2)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ∀ x,
      ∑ i, w i * ‖(W i + z • (1 - W i)) x‖ ^ 2 ≤ ‖x‖ ^ 2) (n : ℕ) :
    (n + 1 : ℝ) * ‖finiteCovariance w W ^ n - finiteCovariance w W ^ (n + 1)‖ ≤ 4 := by
  apply covariance_ritt_bound (finiteCovariance w W) (finiteCovariance w (fun i => 1 - W i))
    (finiteCovariance_monotone w W hw) (finiteCovariance_monotone w _ hw)
    (finiteCovariance_selfAdjoint w W) (finiteCovariance_selfAdjoint w _)
  · apply finiteCovariance_one_le
    intro x
    simpa using hdisk 0 (by norm_num) x
  · exact finiteCovariance_gap_le w W hgap
  · exact norm_covariancePolynomial_finite_le w W hw hs hdisk

lemma covariance_ritt_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    (Ψ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E))
    (Φ : ι → (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E))
    (hlim : Filter.Tendsto Φ l (nhds Ψ))
    (hbound : ∀ i (n : ℕ), (n + 1 : ℝ) * ‖Φ i ^ n - Φ i ^ (n + 1)‖ ≤ 4) (n : ℕ) :
    (n + 1 : ℝ) * ‖Ψ ^ n - Ψ ^ (n + 1)‖ ≤ 4 := by
  exact le_of_tendsto (((hlim.pow n).sub (hlim.pow (n + 1))).norm.const_mul (n + 1 : ℝ))
    (Filter.Eventually.of_forall fun i => hbound i n)

end OracleTemplate.MarkovProduct
