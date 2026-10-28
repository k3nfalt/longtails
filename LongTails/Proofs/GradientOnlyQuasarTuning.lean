import LongTails.Proofs.GradientOnlyQuasarProbability

open scoped BigOperators

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

lemma stageWeight_target {q : Params} (hv : spec.valid q) :
    energyLevel q ≤ q.ε * stageWeight q (stageCount q) := by
  have hε := hv.2.2.2.2.2.2.1
  have hΔ := hv.2.2.2.1
  have hc : 8 * q.Δ / q.ε ≤ (2 : ℝ) ^ stageCount q := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈8 * q.Δ / q.ε⌉₊
  have hh := (div_le_iff₀ hε).mp hc
  have hs := mul_le_mul_of_nonneg_right hh (initialWeight_pos hv).le
  have he : 8 * q.Δ * initialWeight q = 4 * q.R ^ 2 := by
    unfold initialWeight
    field_simp
    ring
  rw [he] at hs
  unfold energyLevel stageWeight
  nlinarith [sq_nonneg q.R]

lemma half_pow_momentOrder {q : Params} (hv : spec.valid q) :
    (1 / 2 : ℝ) ^ momentOrder q ≤ q.δ / 8 := by
  have hδ := hv.2.2.2.2.2.2.2.1
  have hc : 4 / q.δ ≤ (2 : ℝ) ^ Nat.clog 2 ⌈4 / q.δ⌉₊ := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈4 / q.δ⌉₊
  have hh := (div_le_iff₀ hδ).mp hc
  have hp : 8 ≤ q.δ * (2 : ℝ) ^ momentOrder q := by
    unfold momentOrder
    rw [pow_add]
    norm_num
    nlinarith
  have hs := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (1 / 2 : ℝ) ^ momentOrder q)
  have he : (2 : ℝ) ^ momentOrder q * (1 / 2 : ℝ) ^ momentOrder q = 1 := by
    rw [← mul_pow]
    norm_num
  nlinarith [he]

lemma stageWeight_succ (q : Params) (j : ℕ) : stageWeight q (j + 1) = 2 * stageWeight q j := by
  simp only [stageWeight, pow_succ]
  ring

lemma sqrt_stage_increment {q : Params} (hv : spec.valid q) (j : ℕ) :
    Real.sqrt (stageWeight q j) ≤
      4 * (Real.sqrt (stageWeight q (j + 1)) - Real.sqrt (stageWeight q j)) := by
  have h0 := Real.sqrt_nonneg (stageWeight q j)
  have h1 := Real.sqrt_nonneg (stageWeight q (j + 1))
  have hs0 := Real.sq_sqrt (stageWeight_pos hv j).le
  have hs1 := Real.sq_sqrt (stageWeight_pos hv (j + 1)).le
  have he := stageWeight_succ q j
  have hh : (5 * Real.sqrt (stageWeight q j)) ^ 2 ≤
      (4 * Real.sqrt (stageWeight q (j + 1))) ^ 2 := by
    nlinarith [stageWeight_pos hv j]
  have hn := (sq_le_sq₀ (by positivity) (by positivity)).mp hh
  linarith

lemma sum_sqrt_stageWeight {q : Params} (hv : spec.valid q) (n : ℕ) :
    ∑ j ∈ Finset.range n, Real.sqrt (stageWeight q j) ≤ 4 * Real.sqrt (stageWeight q n) := by
  have hh : ∀ n, (∑ j ∈ Finset.range n, Real.sqrt (stageWeight q j)) ≤
      4 * Real.sqrt (stageWeight q n) - 4 * Real.sqrt (stageWeight q 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        linarith [sqrt_stage_increment hv n]
  exact (hh n).trans (by linarith [Real.sqrt_nonneg (stageWeight q 0)])

lemma stageWeight_final_upper {q : Params} (hv : spec.valid q) (hS : 0 < stageCount q) :
    stageWeight q (stageCount q) ≤ 16 * q.R ^ 2 / q.ε := by
  have hε := hv.2.2.2.2.2.2.1
  have hΔ := hv.2.2.2.1
  have hn : 1 < ⌈8 * q.Δ / q.ε⌉₊ := by
    have hh := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp hS
    simpa only [pow_zero] using hh
  have ha : (1 : ℝ) < 8 * q.Δ / q.ε := by exact_mod_cast (Nat.lt_ceil.mp hn)
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have hs : (2 : ℝ) ^ (stageCount q - 1) < (⌈8 * q.Δ / q.ε⌉₊ : ℝ) := by exact_mod_cast hp
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 8 * q.Δ / q.ε by positivity)
  have hpow : (2 : ℝ) ^ stageCount q < 32 * q.Δ / q.ε := by
    have he : (2 : ℝ) ^ stageCount q = 2 * (2 : ℝ) ^ (stageCount q - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hS]
    rw [he]
    simp only [div_eq_mul_inv] at ha hc hs ⊢
    linarith
  have hm := mul_le_mul_of_nonneg_right hpow.le (initialWeight_pos hv).le
  have he : 32 * q.Δ / q.ε * initialWeight q = 16 * q.R ^ 2 / q.ε := by
    unfold initialWeight
    field_simp
    ring
  rw [he] at hm
  exact hm

lemma stage_sqrt_bound {q : Params} (hv : spec.valid q) (j : ℕ) :
    Real.sqrt (q.L0 * stageWeight q j + q.L1 ^ 2 * energyLevel q) ≤
      Real.sqrt q.L0 * Real.sqrt (stageWeight q j) + 2 * q.L1 * q.R := by
  have hL0 := hv.1
  have hL1 := hv.2.1
  have hR := hv.2.2.1
  have hs0 := Real.sq_sqrt (mul_nonneg hL0.le (stageWeight_pos hv j).le)
  rw [Real.sqrt_mul hL0.le] at hs0
  apply (Real.sqrt_le_left (by positivity)).2
  unfold energyLevel
  nlinarith [mul_nonneg (show 0 ≤ Real.sqrt q.L0 * Real.sqrt (stageWeight q j) by positivity)
    (show 0 ≤ q.L1 * q.R by positivity)]

lemma final_sqrt_bound {q : Params} (hv : spec.valid q) (hS : 0 < stageCount q) :
    Real.sqrt q.L0 * Real.sqrt (stageWeight q (stageCount q)) ≤
      4 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) := by
  have hL0 := hv.1
  have hε := hv.2.2.2.2.2.2.1
  rw [← Real.sqrt_mul hL0.le]
  have hh := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (stageWeight_final_upper hv hS) hL0.le)
  have he : Real.sqrt (q.L0 * (16 * q.R ^ 2 / q.ε)) =
      4 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) := by
    rw [show q.L0 * (16 * q.R ^ 2 / q.ε) = 16 * (q.L0 * q.R ^ 2 / q.ε) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  exact hh.trans_eq he

lemma total_time_bound {q : Params} (hv : spec.valid q) :
    stageStart q (stageCount q) ≤ 4096 * (momentOrder q : ℝ) / q.γ *
      (Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + q.L1 * q.R * stageCount q) := by
  have hγ := hv.2.2.2.2.1
  have hL1 := hv.2.1
  have hR := hv.2.2.1
  by_cases hS : stageCount q = 0
  · rw [hS, stageStart_zero]
    positivity
  have hSp : 0 < stageCount q := Nat.pos_of_ne_zero hS
  have hs := Finset.sum_le_sum (s := Finset.range (stageCount q))
    (fun j _ => stage_sqrt_bound hv j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hsum := mul_le_mul_of_nonneg_left (sum_sqrt_stageWeight hv (stageCount q))
    (Real.sqrt_nonneg q.L0)
  have hfinal := final_sqrt_bound hv hSp
  have hraw : (∑ j ∈ Finset.range (stageCount q),
      Real.sqrt (q.L0 * stageWeight q j + q.L1 ^ 2 * energyLevel q)) ≤
      16 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + 2 * q.L1 * q.R * stageCount q := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hraw
    (show 0 ≤ 256 * (momentOrder q : ℝ) / q.γ by positivity)
  have he : stageStart q (stageCount q) = 256 * (momentOrder q : ℝ) / q.γ *
      ∑ j ∈ Finset.range (stageCount q),
        Real.sqrt (q.L0 * stageWeight q j + q.L1 ^ 2 * energyLevel q) := by
    simp only [stageStart, stageDuration, Finset.mul_sum]
  rw [he]
  apply hh.trans
  have hn : 0 ≤ (momentOrder q : ℝ) / q.γ * (q.L1 * q.R * stageCount q) := by positivity
  simp only [div_eq_mul_inv] at hn ⊢
  nlinarith

lemma calls_cover_time {q : Params} (hv : spec.valid q) :
    2 * stageStart q (stageCount q) + 2 * momentOrder q ≤ (calls q : ℝ) := by
  have hγ := hv.2.2.2.2.1
  have hγ1 := hv.2.2.2.2.2.1
  have hL1 := hv.2.1
  have hR := hv.2.2.1
  have hp : (0 : ℝ) ≤ momentOrder q := by positivity
  have hc : 65536 * (momentOrder q : ℝ) *
      (1 + Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + q.L1 * q.R * (1 + stageCount q)) / q.γ ≤
      (calls q : ℝ) := by
    simpa only [calls, momentOrder, stageCount, Nat.cast_add, Nat.cast_one] using
      (Nat.le_ceil (65536 * (momentOrder q : ℝ) *
        (1 + Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + q.L1 * q.R * (1 + stageCount q)) / q.γ))
  apply le_trans _ hc
  have ht := total_time_bound hv
  apply (le_div_iff₀ hγ).2
  have htt := mul_le_mul_of_nonneg_right ht hγ.le
  have he : (4096 * (momentOrder q : ℝ) / q.γ *
      (Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + q.L1 * q.R * stageCount q)) * q.γ =
      4096 * (momentOrder q : ℝ) *
      (Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + q.L1 * q.R * stageCount q) := by field_simp
  rw [he] at htt
  have hg := mul_le_mul_of_nonneg_left hγ1 hp
  nlinarith [mul_nonneg hp (Real.sqrt_nonneg (q.L0 * q.R ^ 2 / q.ε)),
    mul_nonneg hp (show 0 ≤ q.L1 * q.R by positivity),
    mul_nonneg hp (show 0 ≤ q.L1 * q.R * stageCount q by positivity)]

lemma half_pow_le_exp (k : ℕ) : (1 / 2 : ℝ) ^ k ≤ Real.exp (-(k : ℝ) / 2) := by
  have hl : Real.log (1 / 2 : ℝ) ≤ -1 / 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [one_div, Real.log_inv]
    norm_num at hh
    linarith
  have he : (1 / 2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (1 / 2 : ℝ)) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ k by positivity)
  linarith

lemma exp_neg_nat_le_half_pow (k : ℕ) : Real.exp (-(k : ℝ)) ≤ (1 / 2 : ℝ) ^ k := by
  have hl : -1 ≤ Real.log (1 / 2 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [one_div, Real.log_inv]
    linarith
  have he : (1 / 2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (1 / 2 : ℝ)) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ k by positivity)
  linarith

lemma budget_clock_tail {q : Params} (hv : spec.valid q) :
    (RelativeQuasar.samplesLaw (calls q) : MeasureTheory.Measure (Fin (calls q) → ℝ))
      {samples | clockSum samples < stageStart q (stageCount q)} ≤ ENNReal.ofReal (q.δ / 8) := by
  apply (clock_lower_tail (calls q) (stageStart q (stageCount q))).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (stageStart q (stageCount q)) * Real.exp (-(calls q : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (half_pow_le_exp (calls q)) (Real.exp_pos _).le
    _ = Real.exp (stageStart q (stageCount q) - (calls q : ℝ) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(momentOrder q : ℝ)) := Real.exp_le_exp.mpr (by linarith [calls_cover_time hv])
    _ ≤ (1 / 2 : ℝ) ^ momentOrder q := exp_neg_nat_le_half_pow _
    _ ≤ q.δ / 8 := half_pow_momentOrder hv

end OracleTemplate.GradientOnlyQuasar
