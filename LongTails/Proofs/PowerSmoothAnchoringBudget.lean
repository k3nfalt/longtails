import LongTails.Proofs.PowerSmoothAnchoringTuning

namespace LongTails.Proofs.PowerSmoothAnchoringBudget

open LongTails.Setups.StochasticPowerSmoothFixedPoint
open LongTails.Algorithms.PowerSmoothAnchoring PowerSmoothAnchoringTuning

lemma levels_bounds (q : Params) (hD : 0 ≤ q.D) (hε : 0 < q.ε) :
    (2 : ℝ) ^ levels q ≤ 32 * q.D / q.ε + 4 ∧
      (levels q + 1 : ℝ) ≤ 3 + Real.logb 2 (1 + 16 * q.D / q.ε) := by
  have hr : 0 ≤ 16 * q.D / q.ε := by positivity
  have hre : 32 * q.D / q.ε = 2 * (16 * q.D / q.ε) := by ring
  have hl : 0 ≤ Real.logb 2 (1 + 16 * q.D / q.ε) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  rcases Nat.eq_zero_or_pos (levels q) with hz | hp
  · rw [hz]
    norm_num
    constructor <;> linarith [hre]
  · have hn : 1 < ⌈16 * q.D / q.ε⌉₊ + 1 := by
      by_contra hh
      push Not at hh
      have he : levels q = 0 := Nat.clog_of_right_le_one hh 2
      omega
    have hpow := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hn
    have hpow' : (2 : ℝ) ^ (levels q - 1) < (⌈16 * q.D / q.ε⌉₊ : ℝ) + 1 := by
      exact_mod_cast hpow
    have hc := Nat.ceil_lt_add_one hr
    have hb : (2 : ℝ) ^ (levels q - 1) < 16 * q.D / q.ε + 2 := by linarith
    have he : (2 : ℝ) ^ levels q = 2 * (2 : ℝ) ^ (levels q - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hp, pow_succ]
      ring
    constructor
    · rw [he]
      linarith
    · have hb' : (2 : ℝ) ^ (levels q - 1) < 2 * (1 + 16 * q.D / q.ε) := by linarith
      have hg : ((levels q - 1 : ℕ) : ℝ) <
          Real.logb 2 (2 * (1 + 16 * q.D / q.ε)) := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast]
        exact hb'
      rw [Real.logb_mul (by norm_num) (by positivity),
        Real.logb_self_eq_one (by norm_num)] at hg
      have he' : ((levels q - 1 : ℕ) : ℝ) = (levels q : ℝ) - 1 := by
        rw [Nat.cast_sub hp]
        simp
      linarith

lemma total_steps_bound (q : Params) (hs : 1 < q.exponent) (hK : 0 ≤ q.K)
    (hD : 0 ≤ q.D) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    ((levels q + 1) * innerSteps q : ℕ) ≤
      ⌈512 * (1 + q.D / q.ε + (65536 * q.K * (q.σ / q.ε) ^ q.exponent) ^
        (1 / (q.exponent - 1))) * (3 + Real.logb 2 (1 + 16 * q.D / q.ε)) ^
          (2 + q.exponent / (q.exponent - 1))⌉₊ := by
  let S : ℝ := levels q + 1
  let L := 3 + Real.logb 2 (1 + 16 * q.D / q.ε)
  let A := 65536 * q.K * (q.σ / q.ε) ^ q.exponent
  let t := 1 / (q.exponent - 1)
  have hS : 1 ≤ S := by dsimp [S]; have := Nat.cast_nonneg (α := ℝ) (levels q); linarith
  have hSp : 0 < S := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hst : 0 ≤ q.exponent * t := mul_nonneg (by linarith) ht
  have hbounds := levels_bounds q hD hε
  have hSL : S ≤ L := hbounds.2
  have hL : 1 ≤ L := hS.trans hSL
  have hLp : 0 < L := by linarith
  have hN : (innerSteps q : ℝ) ≤ 8 * S / relaxation q + 1 := by
    exact (Nat.ceil_lt_add_one (div_nonneg (by positivity)
      (relaxation_pos q hK hσ hε).le)).le
  have hpow : (A * S ^ q.exponent) ^ t = A ^ t * S ^ (q.exponent * t) := by
    rw [Real.mul_rpow hA (by positivity), ← Real.rpow_mul hSp.le]
  have hden : 8 * S / relaxation q =
      8 * S * (1 + (2 : ℝ) ^ levels q + A ^ t * S ^ (q.exponent * t)) := by
    unfold relaxation
    change 8 * S / (1 / (1 + (2 : ℝ) ^ levels q + (A * S ^ q.exponent) ^ t)) = _
    rw [div_div_eq_mul_div, div_one, hpow]
  rw [hden] at hN
  have hS2 : S ^ 2 ≤ L ^ (2 + q.exponent * t) := by
    have h1 : S ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hSL _
    have h2 := Real.rpow_le_rpow_of_exponent_le hL (show (2 : ℝ) ≤ 2 + q.exponent * t by linarith)
    norm_num at h2
    exact h1.trans h2
  have hS1 : S ≤ L ^ (2 + q.exponent * t) := by nlinarith [sq_nonneg (S - 1)]
  have hSbig : S ^ 2 * S ^ (q.exponent * t) ≤ L ^ (2 + q.exponent * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hSp]
    exact Real.rpow_le_rpow hSp.le hSL (by linarith)
  have hP := hbounds.1
  rw [show 32 * q.D / q.ε = 32 * (q.D / q.ε) by ring] at hP
  have hR : 0 ≤ q.D / q.ε := by positivity
  have hAt : 0 ≤ A ^ t := Real.rpow_nonneg hA _
  have hcost : S * innerSteps q ≤
      512 * (1 + q.D / q.ε + A ^ t) * L ^ (2 + q.exponent * t) := by
    have hn := mul_le_mul_of_nonneg_left hN hSp.le
    have hp := mul_le_mul_of_nonneg_left hP (show 0 ≤ 8 * S ^ 2 by positivity)
    have hbasic := mul_le_mul_of_nonneg_left hS2 (show 0 ≤ 40 + 256 * (q.D / q.ε) by positivity)
    have hnoise := mul_le_mul_of_nonneg_left hSbig (show 0 ≤ 8 * A ^ t by positivity)
    have hLpow : 0 ≤ L ^ (2 + q.exponent * t) := Real.rpow_nonneg hLp.le _
    nlinarith [mul_nonneg hR hLpow, mul_nonneg hAt hLpow]
  have he : q.exponent * t = q.exponent / (q.exponent - 1) := by dsimp [t]; ring
  rw [he] at hcost
  have hfinal := hcost.trans (Nat.le_ceil
    (512 * (1 + q.D / q.ε + A ^ t) * L ^ (2 + q.exponent / (q.exponent - 1))))
  change ((levels q : ℝ) + 1) * innerSteps q ≤ _ at hfinal
  exact_mod_cast hfinal

end LongTails.Proofs.PowerSmoothAnchoringBudget
