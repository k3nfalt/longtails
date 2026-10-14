import LongTails.Proofs.RenewalCoefficient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace OracleTemplate.MarkovProduct

lemma refresh_weight_sum (α : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, α * (1 - α) ^ k = 1 - (1 - α) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma refresh_tail_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (h T : ℕ)
    (hT : 1 ≤ T) (hhalf : T ≤ 2 * (h + 1)) : (1 - α) ^ h ≤ 2 / (α * T) := by
  have hq : 0 ≤ 1 - α := by linarith
  have hq1 : 1 - α ≤ 1 := by linarith
  have hsum : ((h : ℝ) + 1) * (α * (1 - α) ^ h) ≤
      ∑ k ∈ Finset.range (h + 1), α * (1 - α) ^ k := by
    have hh := Finset.sum_le_sum (s := Finset.range (h + 1)) (f := fun _ => α * (1 - α) ^ h)
      (g := fun k => α * (1 - α) ^ k) (fun k hk =>
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq hq1 (by have := Finset.mem_range.mp hk; omega)) hα.le)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hh
  rw [refresh_weight_sum] at hsum
  have hle : (T : ℝ) ≤ 2 * ((h : ℝ) + 1) := by exact_mod_cast hhalf
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  apply (le_div_iff₀ (mul_pos hα hTp)).mpr
  have hh := mul_le_mul_of_nonneg_right hle (mul_nonneg hα.le (pow_nonneg hq h))
  nlinarith [pow_nonneg hq (h + 1)]

lemma refresh_weighted_split {α B : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hB : 0 ≤ B)
    (c : ℕ → ℝ) (n h : ℕ) (hhn : h ≤ n)
    (hfirst : ∀ k < h, c k ≤ B) (hlast : ∀ k, c k ≤ 2) :
    2 * (1 - α) ^ n + (∑ k ∈ Finset.range n, α * (1 - α) ^ k * c k) ≤
      B + 2 * (1 - α) ^ h := by
  have hq : 0 ≤ 1 - α := by linarith
  have hq1 : 1 - α ≤ 1 := by linarith
  have he : n = h + (n - h) := by omega
  have hsplit : (∑ k ∈ Finset.range n, α * (1 - α) ^ k * c k) ≤
      B * (1 - (1 - α) ^ h) + 2 * ((1 - α) ^ h - (1 - α) ^ n) := by
    rw [he, Finset.sum_range_add]
    have ha : (∑ k ∈ Finset.range h, α * (1 - α) ^ k * c k) ≤ B * (1 - (1 - α) ^ h) := by
      calc
        _ ≤ ∑ k ∈ Finset.range h, α * (1 - α) ^ k * B := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (hfirst k (Finset.mem_range.mp hk)) (by positivity)
        _ = _ := by rw [← Finset.sum_mul, refresh_weight_sum]; ring
    have hb : (∑ k ∈ Finset.range (n - h), α * (1 - α) ^ (h + k) * c (h + k)) ≤
        2 * ((1 - α) ^ h - (1 - α) ^ (h + (n - h))) := by
      calc
        _ ≤ ∑ k ∈ Finset.range (n - h), α * (1 - α) ^ (h + k) * 2 := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (hlast _) (by positivity)
        _ = 2 * (1 - α) ^ h * (∑ k ∈ Finset.range (n - h), α * (1 - α) ^ k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [pow_add]
          ring
        _ = _ := by rw [refresh_weight_sum, pow_add]; ring
    exact add_le_add ha hb
  have hp : 0 ≤ B * (1 - α) ^ h := mul_nonneg hB (pow_nonneg hq h)
  linarith

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

lemma renewal_arbitrary_initial_source (Φ V W : ℕ → B →L[ℂ] B) (A : B →L[ℂ] B)
    (hΦ : ∀ k, ‖Φ k‖ ≤ 1) (hV : ∀ k, ‖V k‖ ≤ 1) (hA : ‖A‖ ≤ 2)
    {α C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hstationary : ∀ t : ℕ, 1 ≤ t → ‖V t * A‖ ≤ C / (α * t))
    (hrec : ∀ n, W (n + 1) = (((1 - α : ℝ) : ℂ)) ^ n • Φ (n + 1) + ∑ k ∈ Finset.range n,
      ((α : ℂ) * (((1 - α : ℝ) : ℂ)) ^ k) • (Φ (k + 1) * V (n - k)))
    (T : ℕ) (hT : 1 ≤ T) : ‖W T * A‖ ≤ (2 * C + 4) / (α * T) := by
  have hq : 0 ≤ 1 - α := by linarith
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  let n := T - 1
  let h := T / 2
  have hTn : T = n + 1 := by dsimp [n]; omega
  have hhn : h ≤ n := by dsimp [h, n]; omega
  have hhalf : T ≤ 2 * (h + 1) := by dsimp [h]; omega
  have hVA (k : ℕ) : ‖V k * A‖ ≤ 2 := by
    exact (norm_mul_le _ _).trans (by simpa only [one_mul] using mul_le_mul (hV k) hA (norm_nonneg _) zero_le_one)
  have hΦA (k : ℕ) : ‖Φ k * A‖ ≤ 2 := by
    exact (norm_mul_le _ _).trans (by simpa only [one_mul] using mul_le_mul (hΦ k) hA (norm_nonneg _) zero_le_one)
  have hearly (k : ℕ) (hk : k < h) : ‖V (n - k) * A‖ ≤ 2 * C / (α * T) := by
    have ht : 1 ≤ n - k := by dsimp [h, n] at *; omega
    have htw : T ≤ 2 * (n - k) := by dsimp [h, n] at *; omega
    have htp : (0 : ℝ) < (n - k : ℕ) := by exact_mod_cast ht
    have htw' : (T : ℝ) ≤ 2 * (n - k : ℕ) := by exact_mod_cast htw
    apply (hstationary _ ht).trans
    apply (div_le_div_iff₀ (mul_pos hα htp) (mul_pos hα hTp)).mpr
    have hh := mul_le_mul_of_nonneg_left htw' (mul_nonneg hC hα.le)
    nlinarith
  have hnorm : ‖W T * A‖ ≤ 2 * (1 - α) ^ n +
      ∑ k ∈ Finset.range n, α * (1 - α) ^ k * ‖V (n - k) * A‖ := by
    rw [hTn, hrec, add_mul, Finset.sum_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [smul_mul_assoc, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
      nlinarith [hΦA (n + 1), pow_nonneg hq n]
    · apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      rw [smul_mul_assoc, norm_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hα.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
      rw [mul_assoc (Φ (k + 1)) (V (n - k)) A]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_mul_le _ _).trans
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (hΦ (k + 1)) (norm_nonneg (V (n - k) * A)))
  have hb := refresh_weighted_split hα.le hα1 (by positivity : 0 ≤ 2 * C / (α * T))
    (fun k => ‖V (n - k) * A‖) n h hhn hearly (fun k => hVA (n - k))
  have ht := refresh_tail_bound hα hα1 h T hT hhalf
  calc
    _ ≤ 2 * C / (α * T) + 2 * (1 - α) ^ h := hnorm.trans hb
    _ ≤ 2 * C / (α * T) + 2 * (2 / (α * T)) := by gcongr
    _ = _ := by ring

end OracleTemplate.MarkovProduct
