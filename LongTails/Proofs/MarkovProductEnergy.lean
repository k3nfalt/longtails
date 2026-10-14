import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MarkovProduct

variable {E : Type*} [NormedAddCommGroup E]

lemma weighted_norm_add (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (x y : E) :
    r * (1 - r) * ‖x + y‖ ^ 2 ≤ (1 - r) * ‖x‖ ^ 2 + r * ‖y‖ ^ 2 := by
  have hn : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    nlinarith [norm_add_le x y, norm_nonneg (x + y), norm_nonneg x, norm_nonneg y]
  have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg hr (sub_nonneg.mpr hr1))
  nlinarith [sq_nonneg ((1 - r) * ‖x‖ - r * ‖y‖)]

lemma geometric_path_energy (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (x : ℕ → E) (n : ℕ) :
    (1 - r) ^ 2 * (∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x k - x 0‖ ^ 2) +
      (1 - r) * r ^ (2 * n) * ‖x n - x 0‖ ^ 2 ≤
      r ^ 2 * ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := weighted_norm_add r hr hr1 (x n - x 0) (x (n + 1) - x n)
    rw [show (x n - x 0) + (x (n + 1) - x n) = x (n + 1) - x 0 by abel] at hs
    have hm := mul_le_mul_of_nonneg_left hs
      (mul_nonneg hr (pow_nonneg hr (2 * n)))
    have hp : r ^ (2 * (n + 1)) = r ^ (2 * n) * r ^ 2 := by
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    simp only [Finset.sum_range_succ, hp]
    nlinarith

lemma geometric_displacement_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (x : ℕ → E) (n : ℕ) :
    (∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x k - x 0‖ ^ 2) ≤
      r ^ 2 / (1 - r) ^ 2 *
        ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by
  have hs := geometric_path_energy r hr hr1.le x n
  have hb : 0 ≤ (1 - r) * r ^ (2 * n) * ‖x n - x 0‖ ^ 2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hr1))).mpr
  nlinarith

lemma discounted_firm_energy (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (x : ℕ → E) (u : E)
    (hstep : ∀ k, ‖x (k + 1) - u‖ ^ 2 +
      ‖x (k + 1) - x k‖ ^ 2 ≤ ‖x k - u‖ ^ 2) (n : ℕ) :
    (∑ k ∈ Finset.range n, q ^ k * ‖x (k + 1) - x k‖ ^ 2) +
      q ^ n * ‖x n - u‖ ^ 2 ≤ ‖x 0 - u‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := mul_le_mul_of_nonneg_left (hstep n) (pow_nonneg hq n)
    have he := mul_le_mul_of_nonneg_right hq1
      (mul_nonneg (pow_nonneg hq n) (sq_nonneg ‖x (n + 1) - u‖))
    rw [Finset.sum_range_succ, pow_succ q n]
    nlinarith

lemma geometric_displacement_rescaled (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (x : ℕ → E) (n : ℕ) :
    (1 - r ^ 2) ^ 2 * (∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x k - x 0‖ ^ 2) ≤
      4 * ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by
  have hs := geometric_path_energy r hr hr1 x n
  have ht : 0 ≤ (1 - r) * r ^ (2 * n) * ‖x n - x 0‖ ^ 2 := by positivity
  have hb : (1 - r) ^ 2 * (∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x k - x 0‖ ^ 2) ≤
      r ^ 2 * ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (1 + r))
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hrs : (1 + r) ^ 2 ≤ 4 := by nlinarith
  have hc : (1 + r) ^ 2 * r ^ 2 ≤ 4 := by
    calc
      _ ≤ 4 * 1 := mul_le_mul hrs hr2 (sq_nonneg r) (by norm_num)
      _ = 4 := by norm_num
  have hsum : 0 ≤ ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by
    positivity
  calc
    _ = (1 + r) ^ 2 * ((1 - r) ^ 2 *
        (∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x k - x 0‖ ^ 2)) := by ring
    _ ≤ (1 + r) ^ 2 * (r ^ 2 *
        ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2) := hm
    _ = ((1 + r) ^ 2 * r ^ 2) *
        ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hsum

end OracleTemplate.MarkovProduct
