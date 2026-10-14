import LongTails.Algorithms.BatchedChebyshev
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.BatchedChebyshev

lemma reciprocal_sqrt_telescope {x : ℝ} (hx : 1 ≤ x) :
    1 / (x * Real.sqrt x) ≤ 4 * (1 / Real.sqrt x - 1 / Real.sqrt (x + 1)) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have hx0 : 0 < x := by linarith
  have ha : 0 < a := Real.sqrt_pos.mpr hx0
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx0.le
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hba : b ≤ 2 * a := by nlinarith
  have habound : a * b ≤ 2 * x := by nlinarith [mul_le_mul_of_nonneg_left hba ha.le]
  have hbound : b * (b + a) ≤ 4 * x := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hbound (sub_nonneg.mpr hab)
  have heq : b * (b + a) * (b - a) = b := by
    have hdiff : b ^ 2 - a ^ 2 = 1 := by linarith
    calc
      _ = b * (b ^ 2 - a ^ 2) := by ring
      _ = b := by rw [hdiff, mul_one]
  rw [heq] at hscale
  change 1 / (x * a) ≤ 4 * (1 / a - 1 / b)
  apply (div_le_iff₀ (mul_pos hx0 ha)).mpr
  have hid : 4 * (1 / a - 1 / b) * (x * a) = (4 * x * (b - a)) / b := by
    field_simp
  rw [hid]
  exact (one_le_div hb).mpr hscale

lemma reciprocal_sqrt_sum_le (T : ℕ) :
    ∑ i ∈ Finset.range T, (1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))) ≤ 4 := by
  have hstrong : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, (1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))) ≤
        4 * (1 - 1 / Real.sqrt ((n : ℝ) + 1)) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := reciprocal_sqrt_telescope (x := (n : ℝ) + 1) (by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith)
      push_cast
      linarith
  apply (hstrong T).trans
  have : 0 ≤ 1 / Real.sqrt ((T : ℝ) + 1) := by positivity
  linarith

lemma weight_nonneg (T i : ℕ) : 0 ≤ weight T i := by
  unfold weight
  positivity

lemma weight_sum_le {T : ℕ} (hT : 0 < T) :
    ∑ i ∈ Finset.range T, weight T (i + 1) ≤ 128 * (T : ℝ) := by
  have hs := reciprocal_sqrt_sum_le T
  have heq : (∑ i ∈ Finset.range T, weight T (i + 1)) =
      4 * (2 * (T : ℝ) + 1) *
        (∑ i ∈ Finset.range T, 1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))) +
      17 * (T : ℝ) := by
    simp only [weight, Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib,
      div_eq_mul_inv, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * (2 * (T : ℝ) + 1) by positivity)
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  nlinarith

lemma batch_pos (T M i : ℕ) : 0 < batch T M i := by
  unfold batch
  omega

lemma batch_sum_le {T : ℕ} (hT : 0 < T) (M : ℕ) :
    ∑ i ∈ Finset.range T, batch T M (i + 1) ≤ 2 * T + M := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hpoint (i : ℕ) : (batch T M (i + 1) : ℝ) ≤
      2 + (M : ℝ) * weight T (i + 1) / (128 * (T : ℝ)) := by
    have hv : 0 ≤ (M : ℝ) * weight T (i + 1) / (128 * (T : ℝ)) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_nonneg _ _)) (by positivity)
    have hceil := (Nat.ceil_lt_add_one hv).le
    simp only [batch, Nat.cast_add, Nat.cast_one]
    linarith
  have hs := Finset.sum_le_sum (s := Finset.range T) (fun i _ => hpoint i)
  have heq : (∑ i ∈ Finset.range T,
      (2 + (M : ℝ) * weight T (i + 1) / (128 * (T : ℝ)))) =
      2 * (T : ℝ) + (M : ℝ) * (∑ i ∈ Finset.range T, weight T (i + 1)) /
        (128 * (T : ℝ)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_div, ← Finset.mul_sum]
    ring
  rw [heq] at hs
  have hweights := mul_le_mul_of_nonneg_left (weight_sum_le hT) (Nat.cast_nonneg M)
  have hfrac : (M : ℝ) * (∑ i ∈ Finset.range T, weight T (i + 1)) /
      (128 * (T : ℝ)) ≤ M := by
    apply (div_le_iff₀ (by positivity : 0 < 128 * (T : ℝ))).mpr
    exact hweights
  have hreal : (∑ i ∈ Finset.range T, (batch T M (i + 1) : ℝ)) ≤
      2 * (T : ℝ) + M := by linarith
  exact_mod_cast hreal

lemma allocated_variance_sum_le {T M : ℕ} (hT : 0 < T) (hM : 0 < M) :
    ∑ i ∈ Finset.range T, weight T (i + 1) ^ 2 / (batch T M (i + 1) : ℝ) ≤
      16384 * (T : ℝ) ^ 2 / M := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hpoint (i : ℕ) : weight T i ^ 2 / (batch T M i : ℝ) ≤
      (128 * (T : ℝ) / M) * weight T i := by
    have hb : (0 : ℝ) < batch T M i := by exact_mod_cast batch_pos T M i
    have hceil : (M : ℝ) * weight T i / (128 * (T : ℝ)) ≤ (batch T M i : ℝ) := by
      exact (Nat.le_ceil _).trans (by simp only [batch, Nat.cast_add, Nat.cast_one]; linarith)
    have hscale := (div_le_iff₀ (by positivity : 0 < 128 * (T : ℝ))).mp hceil
    have hmul := mul_le_mul_of_nonneg_right hscale (weight_nonneg T i)
    apply (div_le_iff₀ hb).mpr
    apply (mul_le_mul_iff_of_pos_left hM').mp
    convert hmul using 1 <;> field_simp
  calc
    _ ≤ ∑ i ∈ Finset.range T, (128 * (T : ℝ) / M) * weight T (i + 1) :=
      Finset.sum_le_sum (fun i _ => hpoint (i + 1))
    _ = (128 * (T : ℝ) / M) * ∑ i ∈ Finset.range T, weight T (i + 1) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (128 * (T : ℝ) / M) * (128 * (T : ℝ)) :=
      mul_le_mul_of_nonneg_left (weight_sum_le hT) (by positivity)
    _ = 16384 * (T : ℝ) ^ 2 / M := by ring

end OracleTemplate.BatchedChebyshev
