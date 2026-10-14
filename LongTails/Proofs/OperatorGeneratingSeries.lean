import LongTails.Proofs.MarkovOperatorRenewal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum

open scoped BigOperators Topology
open Filter

namespace OracleTemplate.MarkovProduct

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

noncomputable def operatorSeries (a : ℕ → V) (z : ℂ) : V := ∑' k : ℕ, z ^ k • a k

lemma summable_operatorSeries (a : ℕ → V) {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun k : ℕ => z ^ k • a k) := by
  apply ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right C).of_norm_bounded
  intro k
  rw [norm_smul, norm_pow]
  exact mul_le_mul_of_nonneg_left (ha k) (pow_nonneg (norm_nonneg z) k)

omit [CompleteSpace V] in
lemma norm_operatorSeries_le (a : ℕ → V) {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖operatorSeries a z‖ ≤ C / (1 - ‖z‖) := by
  have hs := (hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_right C
  have hb : ‖operatorSeries a z‖ ≤ (1 - ‖z‖)⁻¹ * C := by
    apply tsum_of_norm_bounded hs
    intro k
    rw [norm_smul, norm_pow]
    exact mul_le_mul_of_nonneg_left (ha k) (pow_nonneg (norm_nonneg z) k)
  simpa only [div_eq_mul_inv, mul_comm] using hb

omit [CompleteSpace V] in
lemma tendsto_operatorSeries_tail (a : ℕ → V) {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) : Tendsto (fun n : ℕ => z ^ n • a n) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun n : ℕ => ‖z‖ ^ n * C)
  · intro n
    rw [norm_smul, norm_pow]
    exact mul_le_mul_of_nonneg_left (ha n) (pow_nonneg (norm_nonneg z) n)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz).mul_const C

lemma operatorSeries_abel_first (a : ℕ → V) {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) • operatorSeries a z = a 0 + z • operatorSeries (fun k => a (k + 1) - a k) z := by
  have hd : ∀ k, ‖a (k + 1) - a k‖ ≤ 2 * C := fun k =>
    (norm_sub_le _ _).trans (by linarith [ha (k + 1), ha k])
  have hl := ((summable_operatorSeries a ha hz).hasSum.tendsto_sum_nat).const_smul (1 - z)
  simp_rw [abel_first_sum] at hl
  have hsum := ((summable_operatorSeries _ hd hz).hasSum.const_smul z).tendsto_sum_nat
  simp only [← mul_smul, ← pow_succ'] at hsum
  have hr := ((tendsto_const_nhds (x := a 0)).sub (tendsto_operatorSeries_tail a ha hz)).add hsum
  simpa only [sub_zero, operatorSeries] using tendsto_nhds_unique hl hr

lemma operatorSeries_abel_second (a : ℕ → V) {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) ^ 2 • operatorSeries a z =
      (1 - z) • a 0 + z • (a 1 - a 0) +
      z ^ 2 • operatorSeries (fun k => a (k + 2) - 2 • a (k + 1) + a k) z := by
  have hd : ∀ k, ‖a (k + 1) - a k‖ ≤ 2 * C := fun k =>
    (norm_sub_le _ _).trans (by linarith [ha (k + 1), ha k])
  rw [pow_two, mul_smul, operatorSeries_abel_first a ha hz, smul_add,
    smul_comm (1 - z) z, operatorSeries_abel_first _ hd hz]
  simp only [smul_add, ← mul_smul, ← pow_two, Nat.zero_add]
  have he : (fun k => a (k + 1 + 1) - a (k + 1) - (a (k + 1) - a k)) =
      (fun k => a (k + 2) - 2 • a (k + 1) + a k) := by
    funext k
    abel
  rw [he]
  abel

end OracleTemplate.MarkovProduct
