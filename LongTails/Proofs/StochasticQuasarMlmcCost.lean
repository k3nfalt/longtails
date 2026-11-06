import LongTails.Proofs.StochasticQuasarInnerMoments
import LongTails.Proofs.StochasticQuasarMlmcMoments

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.StochasticQuasar

lemma inner_calls_any_radius {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (σ D : ℝ) :
    (innerCalls L σ D (innerStageCount D r) : ℝ) ≤
      4 * innerStageCount D r + (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2) := by
  by_cases hDr : r < D
  · exact inner_calls_accuracy hL hr hDr
  · have hz := inner_stage_zero hr (le_of_not_gt hDr)
    rw [hz, innerCalls]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    positivity

lemma inner_dyadic_stage_count {r : ℝ} (hr : 0 < r) (D : ℝ) (j : ℕ) :
    innerStageCount D (mlmcRadius r j) ≤ innerStageCount D r + j := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  apply Nat.ceil_le.mpr
  push_cast
  have hp : 0 < mlmcRadius r j := by unfold mlmcRadius; positivity
  apply (div_le_iff₀ hp).mpr
  have he : (2 : ℝ) ^ (innerStageCount D r + j) * mlmcRadius r j =
      r * (2 : ℝ) ^ innerStageCount D r := by
    rw [mlmcRadius, pow_add]
    field_simp
  rw [he]
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ innerStageCount D r)).mp (inner_stage_target hr)

lemma inner_dyadic_calls {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (σ D : ℝ) (j : ℕ) :
    (innerCalls L σ D (innerStageCount D (mlmcRadius r j)) : ℝ) ≤
      4 * (innerStageCount D r + j : ℝ) +
        (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2) * (4 : ℝ) ^ j := by
  have hp : 0 < mlmcRadius r j := by unfold mlmcRadius; positivity
  have hc := inner_calls_any_radius hL hp σ D
  have hk : (innerStageCount D (mlmcRadius r j) : ℝ) ≤ innerStageCount D r + j := by
    exact_mod_cast inner_dyadic_stage_count hr D j
  have he : (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * mlmcRadius r j ^ 2) =
      (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2) * (4 : ℝ) ^ j := by
    have hh : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    unfold mlmcRadius
    rw [div_pow]
    field_simp
    rw [hh]
  rw [he] at hc
  linarith

lemma mlmc_calls_level {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (σ D : ℝ) (j : ℕ) :
    (mlmcCalls L σ D r j : ℝ) ≤ 12 * innerStageCount D r + 8 * (j + 1 : ℝ) +
      (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2) +
        2 * ((32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2)) * (4 : ℝ) ^ (j + 1) := by
  have hb := inner_calls_any_radius hL hr σ D
  have hu := inner_dyadic_calls hL hr σ D (j + 1)
  have hl := inner_dyadic_calls hL hr σ D j
  have hp : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ (j + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
  have hm := mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2))
  unfold mlmcCalls
  push_cast at hu ⊢
  nlinarith

lemma mlmc_weight_upper (m : ℕ) (j : Fin (m + 1)) :
    mlmcWeight m j ≤ (1 / 4 : ℝ) ^ j.val := by
  unfold mlmcWeight
  exact div_le_self (by positivity) (mlmc_normalizer_bounds m).1

lemma mlmc_index_pow_bound (j : ℕ) : (j : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    push_cast
    nlinarith [show (0 : ℝ) ≤ j by positivity]

lemma mlmc_half_sum (m : ℕ) : (∑ j : Fin (m + 1), (1 / 2 : ℝ) ^ j.val) ≤ 2 := by
  have he : (∑ j : Fin (m + 1), (1 / 2 : ℝ) ^ j.val) =
      2 * (1 - (1 / 2 : ℝ) ^ (m + 1)) := by
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    ring
  rw [he]
  have hn : 0 ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
  linarith

lemma mlmc_level_mean (m : ℕ) :
    (∫ j : Fin (m + 1), (j.val + 1 : ℝ) ∂(mlmcLevelLaw m : Measure _)) ≤ 2 := by
  change (∫ j : Fin (m + 1), (j.val + 1 : ℝ) ∂(mlmcLevelPMF m).toMeasure) ≤ _
  rw [PMF.integral_eq_sum]
  simp only [mlmc_level_probability, smul_eq_mul]
  apply (Finset.sum_le_sum (fun j _ => ?_)).trans (mlmc_half_sum m)
  have hh := mul_le_mul (mlmc_weight_upper m j) (mlmc_index_pow_bound j.val)
    (by positivity : 0 ≤ (j.val : ℝ) + 1) (by positivity : 0 ≤ (1 / 4 : ℝ) ^ j.val)
  convert hh using 1
  rw [← mul_pow]
  norm_num

lemma mlmc_geometric_work_mean (m : ℕ) :
    (∫ j : Fin (m + 1), (4 : ℝ) ^ (j.val + 1) ∂(mlmcLevelLaw m : Measure _)) ≤
      4 * (m + 1 : ℝ) := by
  change (∫ j : Fin (m + 1), (4 : ℝ) ^ (j.val + 1) ∂(mlmcLevelPMF m).toMeasure) ≤ _
  rw [PMF.integral_eq_sum]
  simp only [mlmc_level_probability, smul_eq_mul]
  have hb (j : Fin (m + 1)) : mlmcWeight m j * (4 : ℝ) ^ (j.val + 1) ≤ 4 := by
    have hh := mul_le_mul_of_nonneg_right (mlmc_weight_upper m j)
      (by positivity : 0 ≤ (4 : ℝ) ^ (j.val + 1))
    have he : (1 / 4 : ℝ) ^ j.val * (4 : ℝ) ^ (j.val + 1) = 4 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]
      norm_num
    exact hh.trans_eq he
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hh
  linarith

lemma mlmc_expected_calls {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (σ D : ℝ) (m : ℕ) :
    (∫ j : Fin (m + 1), (mlmcCalls L σ D r j.val : ℝ) ∂(mlmcLevelLaw m : Measure _)) ≤
      12 * innerStageCount D r + 16 + 96 * (m + 1 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2) := by
  let B := (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hii (F : Fin (m + 1) → ℝ) : Integrable F (mlmcLevelLaw m : Measure _) := Integrable.of_finite
  have hi := integral_mono (hii (fun j => (mlmcCalls L σ D r j.val : ℝ)))
    (hii (fun j => 12 * innerStageCount D r + 8 * (j.val + 1 : ℝ) + B + 2 * B * (4 : ℝ) ^ (j.val + 1)))
    (fun j => mlmc_calls_level hL hr σ D j.val)
  simp only [integral_add (hii _) (hii _), integral_const_mul, integral_const,
    probReal_univ, one_smul] at hi
  have h1 := mul_le_mul_of_nonneg_left (mlmc_level_mean m) (by norm_num : (0 : ℝ) ≤ 8)
  simp only [integral_add (hii _) (hii _), integral_const, probReal_univ, one_smul] at h1
  have h2 := mul_le_mul_of_nonneg_left (mlmc_geometric_work_mean m) (by positivity : 0 ≤ 2 * B)
  have h3 : 0 ≤ (m : ℝ) * B := by positivity
  have he : 96 * (m + 1 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2) = 9 * (m + 1 : ℝ) * B := by
    dsimp [B]
    ring
  rw [he]
  nlinarith

lemma mlmc_max_calls {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (σ D : ℝ) (m : ℕ)
    (j : Fin (m + 1)) :
    (mlmcCalls L σ D r j.val : ℝ) ≤ 12 * innerStageCount D r + 8 * (m + 1 : ℝ) +
      32 * σ ^ 2 / (L ^ 2 * r ^ 2) * (4 : ℝ) ^ (m + 1) := by
  let B := (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hc := mlmc_calls_level hL hr σ D j.val
  change _ ≤ 12 * innerStageCount D r + 8 * (j.val + 1 : ℝ) + B + 2 * B * (4 : ℝ) ^ (j.val + 1) at hc
  have hj : (j.val + 1 : ℝ) ≤ m + 1 := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hp : (4 : ℝ) ^ (j.val + 1) ≤ (4 : ℝ) ^ (m + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt j.isLt)
  have h1 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * B)
  have h2 := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (n := m + 1)) hB
  have he : 32 * σ ^ 2 / (L ^ 2 * r ^ 2) * (4 : ℝ) ^ (m + 1) = 3 * B * (4 : ℝ) ^ (m + 1) := by
    dsimp [B]
    ring
  rw [he]
  nlinarith

end OracleTemplate.StochasticQuasar
