import LongTails.Proofs.DistributedJacobianStrongGrowthBudgetAlgebra
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeSchedule

namespace LongTails.Proofs.DistributedJacobianStrongGrowthBudgetCommunication

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open DistributedJacobianStrongGrowthParameters
open DistributedJacobianStrongGrowthTimeSchedule

lemma log2_real_bound (n : ℕ) (hn : 0 < n) :
    (Nat.log2 n : ℝ) + 1 ≤ 2 * Real.log (2 * (n : ℝ)) := by
  have hpn : 2 ^ Nat.log2 n ≤ n := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hn.ne'
  have hp : (2 : ℝ) ^ Nat.log2 n ≤ (n : ℝ) := by exact_mod_cast hpn
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log2 n) hp
  rw [Real.log_pow] at hl
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (Nat.log2 n) : (0 : ℝ) ≤ Nat.log2 n)
  rw [Real.log_mul (by norm_num) (by positivity : (n : ℝ) ≠ 0)]
  nlinarith

lemma countWidth_real_bound (n : ℕ) (hn : 0 < n) :
    (countWidth n : ℝ) ≤ 2 * Real.log (2 * (n : ℝ)) := by
  simpa only [countWidth, Nat.cast_add, Nat.cast_one] using log2_real_bound n hn

lemma quantizationWidth_real_bound {x : ℝ} (hx : 1 ≤ x) :
    ((Nat.log2 ⌈x⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.log (4 * x) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hn : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hxpos
  have hceil : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have hh := Nat.ceil_lt_add_one hxpos.le
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (⌈x⌉₊ : ℝ))
    (show 2 * (⌈x⌉₊ : ℝ) ≤ 4 * x by linarith)
  have hh := log2_real_bound ⌈x⌉₊ hn
  push_cast
  linarith

lemma warmWidth_real_bound (p : Params) (hp : valid p) (T : ℕ) :
    (warmWidth p T : ℝ) ≤ 128 * (1 + Real.log ((p.d : ℝ) * (p.R / radius p T))) := by
  have hr := radius_properties p hp T
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hdpos : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hspos := Real.sqrt_pos.mpr hdpos
  have hsquare := Real.sq_sqrt hdpos.le
  have hsnonneg := Real.sqrt_nonneg (p.d : ℝ)
  have hsone : 1 ≤ Real.sqrt (p.d : ℝ) := by nlinarith
  have hsle : Real.sqrt (p.d : ℝ) ≤ p.d := by nlinarith
  have hq : 1 ≤ p.R / radius p T := (one_le_div hr.1).mpr hr.2.1
  have he : 2 * p.R / warmSpacing p T = 16 * Real.sqrt (p.d : ℝ) * (p.R / radius p T) := by
    simp only [warmSpacing, div_div_eq_mul_div]
    ring
  have hx : 1 ≤ 2 * p.R / warmSpacing p T := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hsone (by linarith : 0 ≤ p.R / radius p T)]
  have hupper : 4 * (2 * p.R / warmSpacing p T) ≤ 64 * ((p.d : ℝ) * (p.R / radius p T)) := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hsle (by linarith : 0 ≤ p.R / radius p T)]
  have hwidth := quantizationWidth_real_bound hx
  have hlog := Real.log_le_log (by positivity : 0 < 4 * (2 * p.R / warmSpacing p T)) hupper
  rw [Real.log_mul (by norm_num) (by positivity : (p.d : ℝ) * (p.R / radius p T) ≠ 0)] at hlog
  have h64 : Real.log 64 ≤ 63 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 64)
    linarith
  have hA := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hq)
  change ((Nat.log2 ⌈2 * p.R / warmSpacing p T⌉₊ + 1 : ℕ) : ℝ) ≤ _
  linarith

lemma ceiling_overhead_absorption {a startup cost C : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ startup) (hc : 0 ≤ cost) (hC : 0 ≤ C)
    (hsmall : a < 1 → cost ≤ C * startup) :
    startup + (⌈256 * a⌉₊ : ℝ) * cost ≤ (C + 1) * startup + 257 * a * cost := by
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 256 * a)).le
  have hm := mul_le_mul_of_nonneg_right hceil hc
  by_cases hlarge : 1 ≤ a
  · nlinarith [mul_nonneg hC hs, mul_le_mul_of_nonneg_right hlarge hc]
  · have hh := hsmall (lt_of_not_ge hlarge)
    nlinarith [mul_nonneg ha hc]

lemma positive_part_ceil (a : ℝ) : ⌈256 * a⌉₊ = ⌈256 * max a 0⌉₊ := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
  · rw [max_eq_right (le_of_not_ge ha)]
    rw [Nat.ceil_eq_zero.mpr (by linarith)]
    norm_num

lemma logarithmic_payload_bound {X n Y : ℝ} (hX : 1 ≤ X) (hn : 0 < n)
    (hY : 0 < Y) (hnY : n ≤ 2 * Y) (hupper : X ≤ 262144 * n ^ 2 * Y) :
    ((Nat.log2 ⌈X⌉₊ + 1 : ℕ) : ℝ) + 2 * Real.log (2 * n) ≤
      64 * Real.log (2 + Y) := by
  have hw := quantizationWidth_real_bound hX
  have hlog := Real.log_le_log (by positivity : 0 < 4 * X)
    (show 4 * X ≤ 1048576 * n ^ 2 * Y by linarith)
  have hc : Real.log 1048576 = 20 * Real.log 2 := by
    have he : (1048576 : ℝ) = 2 ^ (20 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
  rw [Real.log_mul (by positivity : (1048576 : ℝ) * n ^ 2 ≠ 0) hY.ne',
    Real.log_mul (by norm_num) (pow_ne_zero _ hn.ne'), Real.log_pow, hc] at hlog
  have hln := Real.log_le_log hn hnY
  rw [Real.log_mul (by norm_num) hY.ne'] at hln
  have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + Y)
  have hlY := Real.log_le_log hY (by linarith : Y ≤ 2 + Y)
  have hlcount := Real.log_le_log (by positivity : 0 < 2 * n)
    (show 2 * n ≤ (2 + Y) ^ 2 by nlinarith [sq_nonneg Y])
  rw [Real.log_pow] at hlcount
  have hlpos : 0 ≤ Real.log (2 + Y) := Real.log_nonneg (by linarith)
  norm_num only [Nat.cast_ofNat] at hlog hlcount
  linarith

lemma worker_growth_bounds {κ B n : ℝ} (hκ : 1 ≤ κ) (hB : 1 ≤ B)
    (hn : 64 * κ * B ≤ n) : κ ≤ n ∧ B + 1 ≤ n ∧ 2 ≤ n := by
  have hκB := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ κ)
  have hBκ := mul_le_mul_of_nonneg_right hκ (by linarith : 0 ≤ B)
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma refinementWidth_real_bound (p : Params) (hp : valid p) (T : ℕ)
    (hT : 1 ≤ T) (hTk : (T : ℝ) ≤ p.L / p.μ)
    (hworkers : 64 * (p.L / p.μ) * growth p ^ T ≤ (p.n : ℝ))
    (hx : (1 : ℝ) / 2 < radius p T / p.ε) :
    ((refinementWidth p T + countWidth p.n : ℕ) : ℝ) ≤
      64 * Real.log (2 + (p.n : ℝ) * p.d * (radius p T / p.ε)) := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 1 ≤ p.L / p.μ := (one_le_div hμ).mpr hp.2.2.2.2.2.2.2.1
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hdpos : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hsquare := Real.sq_sqrt hdpos.le
  have hsnonneg := Real.sqrt_nonneg (p.d : ℝ)
  have hsone : 1 ≤ Real.sqrt (p.d : ℝ) := by nlinarith
  have hsle : Real.sqrt (p.d : ℝ) ≤ p.d := by nlinarith
  have hB : 1 ≤ growth p ^ T := one_le_pow₀ (growth_gt_one p hp).le
  have hb := worker_growth_bounds hk hB hworkers
  have hratio : 1 ≤ (p.L / p.μ) / (T : ℝ) := (one_le_div (by linarith)).mpr hTk
  have hratioUpper : (p.L / p.μ) / (T : ℝ) ≤ (p.n : ℝ) := by
    apply le_trans _ hb.1
    exact div_le_self (by linarith) ht
  have hnorm : 2 * clipRadius p T / refinementSpacing p T =
      262144 * ((p.L / p.μ) / (T : ℝ)) ^ 2 * (growth p ^ T + 1) *
        Real.sqrt (p.d : ℝ) * (radius p T / p.ε) := by
    simp only [clipRadius, refinementSpacing, contraction]
    field_simp
    ring
  have hX : 1 ≤ 2 * clipRadius p T / refinementSpacing p T := by
    rw [hnorm]
    have hprod : 1 ≤ ((p.L / p.μ) / (T : ℝ)) ^ 2 * (growth p ^ T + 1) * Real.sqrt (p.d : ℝ) := by
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hratio) (by linarith)) hsone
    nlinarith [mul_le_mul_of_nonneg_right hprod (by linarith : 0 ≤ radius p T / p.ε)]
  have hXupper : 2 * clipRadius p T / refinementSpacing p T ≤
      262144 * (p.n : ℝ) ^ 2 * ((p.n : ℝ) * p.d * (radius p T / p.ε)) := by
    rw [hnorm]
    calc
      _ ≤ 262144 * (p.n : ℝ) ^ 2 * (p.n : ℝ) * (p.d : ℝ) * (radius p T / p.ε) := by
        gcongr
        exact hb.2.1
      _ = _ := by ring
  have hnpos : 0 < (p.n : ℝ) := by exact_mod_cast p.n.pos
  have hxpos : 0 < radius p T / p.ε := by linarith
  have hYpos : 0 < (p.n : ℝ) * p.d * (radius p T / p.ε) := by positivity
  have hnY : (p.n : ℝ) ≤ 2 * ((p.n : ℝ) * p.d * (radius p T / p.ε)) := by
    have hh := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ radius p T / p.ε)
    have hh' : 1 ≤ 2 * (p.d : ℝ) * (radius p T / p.ε) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh' hnpos.le]
  have hwidth := logarithmic_payload_bound hX hnpos hYpos hnY hXupper
  have hcount := countWidth_real_bound p.n p.n.pos
  change ((Nat.log2 ⌈2 * clipRadius p T / refinementSpacing p T⌉₊ + 1 + countWidth p.n : ℕ) : ℝ) ≤ _
  push_cast at hwidth ⊢
  nlinarith

lemma positive_log_small {c x : ℝ} (hc : 1 ≤ c)
    (hsmall : c * max (Real.log (2 * x)) 0 < 1) : x < 2 := by
  by_contra h
  have hx2 : 2 ≤ x := le_of_not_gt h
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show 4 ≤ 2 * x by linarith)
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have he : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
  rw [h4] at hl
  have hmax : 1 ≤ max (Real.log (2 * x)) 0 := by linarith [le_max_left (Real.log (2 * x)) (0 : ℝ)]
  have hm := one_le_mul_of_one_le_of_one_le hc hmax
  linarith

lemma small_refinement_log {n d q x : ℝ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : 1 ≤ q) (hx : 0 < x) (hx2 : x ≤ 2) :
    Real.log (2 + n * d * x) ≤ 4 * (1 + Real.log (d * q)) * Real.log (2 * n) := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hnd := one_le_mul_of_one_le_of_one_le hn hd
  have hupper : 2 + n * d * x ≤ 4 * n * d := by
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by positivity : 0 ≤ n * d)]
  have hl := Real.log_le_log (by positivity : 0 < 2 + n * d * x) hupper
  rw [Real.log_mul (by positivity : 4 * n ≠ 0) hdpos.ne',
    Real.log_mul (by norm_num) hnpos.ne'] at hl
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have he : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
  rw [h4] at hl
  have hB : Real.log (2 * n) = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hnpos.ne'
  have hA : Real.log (d * q) = Real.log d + Real.log q := Real.log_mul hdpos.ne' hqpos.ne'
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hnlog := Real.log_nonneg hn
  have hdlog := Real.log_nonneg hd
  have hqlog := Real.log_nonneg hq
  have hbhalf : (1 : ℝ) / 2 ≤ Real.log (2 * n) := by linarith
  have haone : 1 ≤ 1 + Real.log (d * q) := by linarith
  have hab := mul_le_mul_of_nonneg_right haone (by linarith : 0 ≤ Real.log (2 * n))
  have hba := mul_le_mul_of_nonneg_left hbhalf (by linarith : 0 ≤ 1 + Real.log (d * q))
  nlinarith

lemma small_refinement_cost {ℓ β n d q x : ℝ} (hℓ : 0 ≤ ℓ) (hβ : 0 ≤ β)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 1 ≤ q) (hx : 0 < x) (hx2 : x ≤ 2) :
    ℓ + β * (64 + d * Real.log (2 + n * d * x)) ≤
      4 * (1 + Real.log (d * q)) * (ℓ + β * (64 + d * Real.log (2 * n))) := by
  have hl := small_refinement_log hn hd hq hx hx2
  have hA : 1 ≤ 1 + Real.log (d * q) := by
    have hh := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hq)
    linarith
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ β * d by positivity)
  have hb := mul_le_mul_of_nonneg_right hA (show 0 ≤ ℓ + 64 * β by positivity)
  nlinarith

end LongTails.Proofs.DistributedJacobianStrongGrowthBudgetCommunication
