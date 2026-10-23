import LongTails.Proofs.VarianceReducedWeakMintyStep
import LongTails.Algorithms.VarianceReducedWeakMinty
import LongTails.Proofs.SvrgConvex
import LongTails.Proofs.FiniteVarianceBatch

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.VarianceReducedWeakMinty

lemma expect_fin_succ {Ω V : Type*} [Fintype Ω] [AddCommMonoid V] [Module ℚ≥0 V]
    {k : ℕ} (f : (Fin (k + 1) → Ω) → V) :
    (𝔼 ξ, f ξ) = 𝔼 a : Ω, 𝔼 ξ : Fin k → Ω, f (Fin.cons a ξ) := by
  rw [Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Ω)).symm
    f (fun ξ => f (Fin.cons ξ.1 ξ.2)) (by
      intro ξ
      exact congrArg f ((Fin.consEquiv (fun _ : Fin (k + 1) => Ω)).apply_symm_apply ξ).symm)]
  exact Finset.expect_product Finset.univ Finset.univ _

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype Ω] [Nonempty Ω]

omit [InnerProductSpace ℝ E] [Nonempty Ω] in
lemma batch_sum_zero (X : Ω → E) (hX : ∑ ω, X ω = 0) (b : ℕ) :
    (∑ ξ : Fin b → Ω, ∑ i, X (ξ i)) = 0 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (b + 1) => Ω)).symm
      (fun ξ => ∑ i, X (ξ i))
      (fun (ξ : Ω × (Fin b → Ω)) => ∑ i : Fin (b + 1), X (Fin.cons (α := fun _ : Fin (b + 1) => Ω) ξ.1 ξ.2 i)) (by
        intro ξ
        exact congrArg (fun ξ => ∑ i, X (ξ i))
          ((Fin.consEquiv (fun _ : Fin (b + 1) => Ω)).apply_symm_apply ξ).symm)]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ih, add_zero]
    rw [← Finset.smul_sum, hX, smul_zero]

lemma batch_sum_second_moment (X : Ω → E) (hX : ∑ ω, X ω = 0) (b : ℕ) :
    (𝔼 ξ : Fin b → Ω, ‖∑ i, X (ξ i)‖ ^ 2) =
      (b : ℝ) * (𝔼 ω, ‖X ω‖ ^ 2) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [expect_fin_succ, Finset.expect_comm]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hadd (ξ : Fin b → Ω) :
        (𝔼 a, ‖X a + ∑ i, X (ξ i)‖ ^ 2) =
          ‖∑ i, X (ξ i)‖ ^ 2 + (𝔼 a, ‖X a‖ ^ 2) := by
      simpa only [add_comm] using mean_norm_add_sq (∑ i, X (ξ i)) X hX
    simp_rw [hadd]
    rw [Finset.expect_add_distrib, Fintype.expect_const, ih]
    push_cast
    ring

lemma batch_mean_second_moment (X : Ω → E) (hX : ∑ ω, X ω = 0)
    {b : ℕ} (hb : 0 < b) :
    (𝔼 ξ : Fin b → Ω, ‖(b : ℝ)⁻¹ • ∑ i, X (ξ i)‖ ^ 2) =
      (𝔼 ω, ‖X ω‖ ^ 2) / b := by
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← Finset.mul_expect]
  rw [batch_sum_second_moment X hX b]
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  field_simp

open LongTails.Setups.FiniteSumWeakMintyInclusion

omit [Fintype Ω] [Nonempty Ω] in
lemma batch_error_centered {n b : ℕ} (F : Fin n → E → E) (w y : E)
    (hb : 0 < b) (ξ : Fin b → Fin n) :
    batchValue F w y ξ - operator F y =
      (b : ℝ)⁻¹ • ∑ i, ((F (ξ i) y - F (ξ i) w) -
        (n : ℝ)⁻¹ • ∑ j, (F j y - F j w)) := by
  have h := RobustGradient.finite_mean_centered
    (X := fun i : Fin n => F i y - F i w)
    ((n : ℝ)⁻¹ • ∑ j, (F j y - F j w)) b hb ξ
  simp only [one_div, Finset.sum_sub_distrib, smul_sub] at h
  unfold batchValue operator
  simp only [Finset.sum_sub_distrib, smul_sub]
  convert h using 1
  abel

omit [Fintype Ω] [Nonempty Ω] in
lemma component_centered_sum {n : ℕ} (hn : 0 < n) (v : Fin n → E) :
    (∑ i, (v i - (n : ℝ)⁻¹ • ∑ j, v j)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn',
    one_smul, sub_self]

omit [Fintype Ω] [Nonempty Ω] in
lemma batch_error_sum_zero {n b : ℕ} (F : Fin n → E → E) (w y : E)
    (hn : 0 < n) (hb : 0 < b) :
    (∑ ξ : Fin b → Fin n, (batchValue F w y ξ - operator F y)) = 0 := by
  simp_rw [batch_error_centered F w y hb]
  rw [← Finset.smul_sum,
    batch_sum_zero _ (component_centered_sum hn (fun i => F i y - F i w)) b,
    smul_zero]

omit [Fintype Ω] [Nonempty Ω] in
lemma batch_error_variance {n b : ℕ} [NeZero n] (F : Fin n → E → E) (w y : E)
    (hb : 0 < b) {Λ : ℝ}
    (hv : (n : ℝ)⁻¹ * ∑ i, ‖F i y - F i w‖ ^ 2 ≤ Λ ^ 2 * ‖y - w‖ ^ 2) :
    (𝔼 ξ : Fin b → Fin n, ‖batchValue F w y ξ - operator F y‖ ^ 2) ≤
      Λ ^ 2 * ‖y - w‖ ^ 2 / b := by
  simp_rw [batch_error_centered F w y hb]
  rw [batch_mean_second_moment
    (fun i => (F i y - F i w) - (n : ℝ)⁻¹ • ∑ j, (F j y - F j w))
    (component_centered_sum (Nat.pos_of_ne_zero (NeZero.ne n)) (fun i => F i y - F i w)) hb]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg b)
  apply (FiniteSum.centered_second_moment (fun i => F i y - F i w)).trans
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_eq_mul_inv,
    mul_comm] using hv

omit [Fintype Ω] [Nonempty Ω] in
lemma estimator_error_sum_zero {n b : ℕ} (exact : Bool) (F : Fin n → E → E)
    (w y : E) (hn : 0 < n) (hb : 0 < b) :
    (∑ ξ : Fin b → Fin n, (estimatorValue exact F w y ξ - operator F y)) = 0 := by
  cases exact with
  | false => exact batch_error_sum_zero F w y hn hb
  | true => simp [estimatorValue]

omit [Fintype Ω] [Nonempty Ω] in
lemma estimator_error_variance {n b : ℕ} [NeZero n] (exact : Bool)
    (F : Fin n → E → E) (w y : E) (hb : 0 < b) {Λ : ℝ}
    (hv : (n : ℝ)⁻¹ * ∑ i, ‖F i y - F i w‖ ^ 2 ≤ Λ ^ 2 * ‖y - w‖ ^ 2) :
    (𝔼 ξ : Fin b → Fin n, ‖estimatorValue exact F w y ξ - operator F y‖ ^ 2) ≤
      (if exact then 0 else Λ ^ 2 / b) * ‖y - w‖ ^ 2 := by
  cases exact with
  | false => simpa only [estimatorValue, Bool.false_eq_true, ↓reduceIte, div_mul_eq_mul_div]
      using batch_error_variance F w y hb hv
  | true => simp [estimatorValue]

end OracleTemplate.VarianceReducedWeakMinty
