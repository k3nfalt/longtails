import LongTails.Proofs.SvrgConvex
import LongTails.Algorithms.RecursiveGradient

open InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.NonconvexFiniteSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inexact_gradient_descent {f : E → ℝ} {g : E → E} {L η : ℝ}
     (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x v : E) :
    f (x - η • v) ≤ f x - η / 2 * ‖g x‖ ^ 2 -
      η / 2 * (1 - L * η) * ‖v‖ ^ 2 + η / 2 * ‖v - g x‖ ^ 2 := by
  have h := Gradient.smooth_upper_bound hg hlip x (x - η • v)
  rw [show x - η • v - x = -η • v by module] at h
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  rw [norm_sub_sq_real, ← real_inner_comm v (g x)]
  nlinarith

omit [CompleteSpace E] in
lemma norm_mean_sq_le {n : ℕ} [NeZero n] (a : Fin n → E) :
    ‖(n : ℝ)⁻¹ • ∑ i, a i‖ ^ 2 ≤ (𝔼 i, ‖a i‖ ^ 2) := by
  have h : 0 ≤ (𝔼 i, ‖a i - (n : ℝ)⁻¹ • ∑ j, a j‖ ^ 2) :=
    Finset.expect_nonneg (fun i _ => sq_nonneg _)
  simp only [norm_sub_sq_real, Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, FiniteSum.expect_inner_left, real_inner_self_eq_norm_sq,
    Fintype.expect_const] at h
  linarith

omit [CompleteSpace E] in
lemma fullGradient_lipschitz_of_mean_square {n : ℕ} [NeZero n]
    {g : Fin n × E → E} {L : ℝ} (hL : 0 ≤ L)
    (hmean : ∀ x y, (𝔼 i, ‖g (i, x) - g (i, y)‖ ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2)
    (x y : E) :
    ‖FiniteSum.fullGradient g x - FiniteSum.fullGradient g y‖ ≤ L * ‖x - y‖ := by
  have h := (norm_mean_sq_le (fun i => g (i, x) - g (i, y))).trans (hmean x y)
  have heq : (n : ℝ)⁻¹ • ∑ i, (g (i, x) - g (i, y)) =
      FiniteSum.fullGradient g x - FiniteSum.fullGradient g y := by
    simp [FiniteSum.fullGradient, Finset.sum_sub_distrib, smul_sub]
  rw [heq] at h
  nlinarith [norm_nonneg (FiniteSum.fullGradient g x - FiniteSum.fullGradient g y),
    mul_nonneg hL (norm_nonneg (x - y))]

omit [CompleteSpace E] in
lemma recursive_error_identity {n : ℕ} [NeZero n]
    (a : Fin n → E) (e : E) :
    (𝔼 i, ‖e + a i - (n : ℝ)⁻¹ • ∑ j, a j‖ ^ 2) =
      ‖e‖ ^ 2 + (𝔼 i, ‖a i - (n : ℝ)⁻¹ • ∑ j, a j‖ ^ 2) := by
  have hmean : (n : ℝ)⁻¹ • ∑ i, (a i - (n : ℝ)⁻¹ • ∑ j, a j) = 0 := by
    simp [Finset.sum_sub_distrib, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, NeZero.ne n]
  simp_rw [show ∀ i, e + a i - (n : ℝ)⁻¹ • ∑ j, a j =
    (a i - (n : ℝ)⁻¹ • ∑ j, a j) + e from fun i => by module,
    norm_add_sq_real]
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect,
    FiniteSum.expect_inner_left, hmean, inner_zero_left, mul_zero,
    Fintype.expect_const]
  ring

omit [CompleteSpace E] in
lemma recursive_error_bound {n : ℕ} [NeZero n]
    (a : Fin n → E) (e : E) :
    (𝔼 i, ‖e + a i - (n : ℝ)⁻¹ • ∑ j, a j‖ ^ 2) ≤
      ‖e‖ ^ 2 + (𝔼 i, ‖a i‖ ^ 2) := by
  rw [recursive_error_identity]
  exact add_le_add le_rfl (FiniteSum.centered_second_moment a)

omit [CompleteSpace E] in
lemma independent_sum_second_moment {n : ℕ} [NeZero n]
    (a : Fin n → E) (ha : (n : ℝ)⁻¹ • ∑ i, a i = 0) (b : ℕ) (e : E) :
    (𝔼 seed : Fin b → Fin n, ‖e + ((List.ofFn seed).map a).sum‖ ^ 2) =
      ‖e‖ ^ 2 + (b : ℝ) * (𝔼 i, ‖a i‖ ^ 2) := by
  induction b generalizing e with
  | zero => simp
  | succ b ih =>
      rw [FiniteSum.expect_tape_succ (fun samples => ‖e + (samples.map a).sum‖ ^ 2)]
      simp only [List.map_cons, List.sum_cons, ← add_assoc, ih,
        Finset.expect_add_distrib, Fintype.expect_const]
      have h := recursive_error_identity a e
      rw [ha] at h
      simp only [sub_zero] at h
      rw [h]
      push_cast
      ring

omit [CompleteSpace E] in
lemma batch_error_bound {n b : ℕ} [NeZero n] (hb : 0 < b)
    (a : Fin n → E) (e : E) :
    (𝔼 seed : Fin b → Fin n,
      ‖e + (b : ℝ)⁻¹ • ∑ j, a (seed j) - (n : ℝ)⁻¹ • ∑ i, a i‖ ^ 2) ≤
      ‖e‖ ^ 2 + (𝔼 i, ‖a i‖ ^ 2) / b := by
  let μ := (n : ℝ)⁻¹ • ∑ i, a i
  let d := fun i => (b : ℝ)⁻¹ • (a i - μ)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hzero : (n : ℝ)⁻¹ • ∑ i, (a i - μ) = 0 := by
    simp [μ, Finset.sum_sub_distrib, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, NeZero.ne n]
  have hd : (n : ℝ)⁻¹ • ∑ i, d i = 0 := by
    simp only [d, ← Finset.smul_sum]
    rw [smul_comm, hzero, smul_zero]
  have h := independent_sum_second_moment d hd b e
  have heq (seed : Fin b → Fin n) :
      ((List.ofFn seed).map d).sum = (b : ℝ)⁻¹ • ∑ j, a (seed j) - μ := by
    simp [List.map_ofFn, Function.comp_def, List.sum_ofFn, d, ← Finset.smul_sum,
      Finset.sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, hb0]
  simp only [heq, ← add_sub_assoc] at h
  have hv := FiniteSum.centered_second_moment a
  have hscale : (𝔼 i, ‖d i‖ ^ 2) = (b : ℝ)⁻¹ ^ 2 *
      (𝔼 i, ‖a i - μ‖ ^ 2) := by
    simp only [d, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_expect]
  rw [hscale] at h
  have hcoef : (b : ℝ) * ((b : ℝ)⁻¹ ^ 2 * (𝔼 i, ‖a i - μ‖ ^ 2)) =
      (𝔼 i, ‖a i - μ‖ ^ 2) / b := by field_simp
  rw [hcoef] at h
  change (𝔼 seed : Fin b → Fin n,
    ‖e + (b : ℝ)⁻¹ • ∑ j, a (seed j) - μ‖ ^ 2) ≤ _
  rw [h]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hv (Nat.cast_nonneg b))

omit [CompleteSpace E] in
lemma recursive_estimator_error {n b : ℕ} [NeZero n]
    (hb : 0 < b) {g : Fin n × E → E} {L : ℝ}
    (hmean : ∀ x y, (𝔼 i, ‖g (i, x) - g (i, y)‖ ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2)
    (x y v : E) :
    (𝔼 seed : Fin b → Fin n,
      ‖v + differenceBatch g b y x (List.ofFn seed) - FiniteSum.fullGradient g y‖ ^ 2) ≤
      ‖v - FiniteSum.fullGradient g x‖ ^ 2 + L ^ 2 * ‖y - x‖ ^ 2 / b := by
  have h := batch_error_bound hb (fun i => g (i, y) - g (i, x))
    (v - FiniteSum.fullGradient g x)
  have heq (seed : Fin b → Fin n) :
      v - FiniteSum.fullGradient g x + (b : ℝ)⁻¹ • ∑ j, (g (seed j, y) - g (seed j, x)) -
          (n : ℝ)⁻¹ • ∑ i, (g (i, y) - g (i, x)) =
        v + differenceBatch g b y x (List.ofFn seed) - FiniteSum.fullGradient g y := by
    simp only [differenceBatch, List.map_ofFn, Function.comp_def, List.sum_ofFn,
      Finset.sum_sub_distrib, smul_sub, FiniteSum.fullGradient]
    module
  simp only [heq] at h
  exact h.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right (hmean y x) (Nat.cast_nonneg b)))

end OracleTemplate.NonconvexFiniteSum
