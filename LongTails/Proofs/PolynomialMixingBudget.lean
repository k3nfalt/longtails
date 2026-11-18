import LongTails.Proofs.PolynomialMixingExecution
import LongTails.Proofs.AdaptiveHistoryAlgebra

namespace LongTails.Proofs.PolynomialMixingBudget

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingExecution

lemma bridge {a τ β : ℝ} (ha : 1 ≤ a) (hτ : 0 < τ) (hβ : 0 < β) {t : ℕ}
    (ht : τ * a ^ (1 / β) ≤ t) : (1 + (t : ℝ) / τ) ^ (-β) ≤ a⁻¹ := by
  have ha' : 0 < a := by linarith
  have hh : a ^ (1 / β) ≤ 1 + (t : ℝ) / τ := by
    have h := (le_div_iff₀ hτ).mpr (by simpa only [mul_comm τ] using ht)
    linarith
  have h := (Real.rpow_le_rpow_iff_of_neg (by positivity : 0 < 1 + (t : ℝ) / τ)
    (Real.rpow_pos_of_pos ha' _) (neg_lt_zero.mpr hβ)).mpr hh
  rwa [← Real.rpow_mul ha'.le, show 1 / β * -β = -1 by field_simp, Real.rpow_neg_one] at h

lemma trial_bounds {δ : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1 / 32) :
    let L := Real.log (8 / δ)
    let k := ⌈8 * L⌉₊
    1 ≤ L ∧ 0 < k ∧ (k : ℝ) + 1 ≤ 16 * L ∧ ((k : ℝ) + 1) * (1/2 : ℝ)^k ≤ δ / 2 := by
  intro L k
  have hd8 : 8 ≤ 8 / δ := (le_div_iff₀ hd).mpr (by linarith)
  have hL : 1 ≤ L := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hd8
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at this
    dsimp [L]; linarith [Real.log_two_gt_d9]
  have hlo : 8 * L ≤ k := Nat.le_ceil _
  have hup := Nat.ceil_lt_add_one (show 0 ≤ 8 * L by linarith)
  change (k : ℝ) < 8 * L + 1 at hup
  have hk : 0 < k := Nat.ceil_pos.mpr (by linarith)
  refine ⟨hL, hk, by linarith, ?_⟩
  have h1 := AdaptiveHistoryAlgebra.half_power_exponential k
  have hh : Real.exp (-(k : ℝ) / 2) ≤ Real.exp (-4 * L) := Real.exp_le_exp.mpr (by linarith)
  have hx : Real.exp L = 8 / δ := Real.exp_log (by positivity)
  have h2 : Real.exp (-4 * L) = (δ / 8) ^ 4 := by
    rw [neg_mul, Real.exp_neg, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul, hx]; field_simp
  have hLup : L ≤ 8 / δ := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  apply (mul_le_mul_of_nonneg_left (h1.trans (hh.trans_eq h2)) (by positivity : 0 ≤ (k : ℝ) + 1)).trans
  apply (mul_le_mul_of_nonneg_right (show (k : ℝ) + 1 ≤ 16 * (8 / δ) by linarith)
    (by positivity : 0 ≤ (δ / 8) ^ 4)).trans
  field_simp
  nlinarith [pow_le_pow_left₀ hd.le (show δ ≤ 1 by linarith) 3]

lemma cost_bound (q : Params) (hp : spec.valid q) : (cost (schedule q) : ℝ) ≤
    q.τ * (32 * Real.log (8 / q.δ)) ^ 2 * ((16777216 * q.G * q.R / q.ε) ^
      (q.p / (q.p - 1) * (1 + 1 / q.β)) + ((32 * Real.log (8 / q.δ)) ^ 2 / q.δ) ^ (1 / q.β)) := by
  obtain ⟨_, hR, hG, hp1, _, hβ, hτ, hε, hscale, hd, hd'⟩ := hp
  let L := Real.log (8 / q.δ)
  let c := schedule q
  let x := 32768 * q.G * q.R / q.ε
  let k := q.p / (q.p - 1)
  let T := (512 * x) ^ k
  have hx : 1 ≤ x := (le_div_iff₀ hε).mpr (by nlinarith)
  have hk : 1 ≤ k := (le_div_iff₀ (by linarith)).mpr (by linarith)
  have hτ' : 0 < q.τ := by linarith
  have hpow := Real.one_le_rpow hx (show 0 ≤ k by linarith)
  have hN : (c.samples : ℝ) ≤ 2 * x ^ k := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ x ^ k by linarith)
    change (c.samples : ℝ) < x ^ k + 1 at h; linarith
  have hNp : 0 < c.samples := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith : 0 < x) _)
  have hscaleN : 256 * c.samples ≤ T := by
    have hh := Real.self_le_rpow_of_one_le (by norm_num : (1 : ℝ) ≤ 512) hk
    dsimp [T]; rw [Real.mul_rpow (by norm_num) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hh (by linarith : 0 ≤ x ^ k)]
  obtain ⟨hL, hK, hUp, _⟩ := trial_bounds hd hd'
  change (c.trials : ℝ) + 1 ≤ 16 * L at hUp
  change 1 ≤ L at hL
  let J := (c.trials : ℝ) * (c.trials + 1)
  let H := (32 * L)^2
  have hJ : 4 * J ≤ H := by
    have hh := mul_le_mul (show (c.trials : ℝ) ≤ 16 * L by linarith) hUp
      (by positivity) (by linarith)
    dsimp only [J,H]; nlinarith
  have hJ1 : 1 ≤ J := by
    have : (1 : ℝ) ≤ c.trials := by exact_mod_cast hK
    dsimp [J]; nlinarith
  have hpos : 1 ≤ 4 * J / q.δ := (le_div_iff₀ hd).mpr (by linarith)
  have hceil {a : ℝ} (ha : 1 ≤ a) : (⌈q.τ * a ^ (1 / q.β)⌉₊ : ℝ) + 1 ≤ 3 * (q.τ * a ^ (1 / q.β)) := by
    have hh := Real.one_le_rpow ha (by positivity : 0 ≤ 1 / q.β)
    have ht := one_le_mul_of_one_le_of_one_le hτ hh
    linarith [Nat.ceil_lt_add_one (show 0 ≤ q.τ * a ^ (1 / q.β) by linarith)]
  have hN1 : (1 : ℝ) ≤ c.samples := by exact_mod_cast hNp
  have hIn := hceil (show 1 ≤ 256 * (c.samples : ℝ) by linarith)
  change (c.innerSkip : ℝ) + 1 ≤ _ at hIn
  have hOut := hceil hpos
  have eqJ : 4 * J = 4 * (c.trials : ℝ) * (c.trials + 1) := by dsimp [J]; ring
  nth_rw 1 [eqJ] at hOut
  change (c.outerSkip : ℝ) + 1 ≤ _ at hOut
  have hT : 0 < T := by linarith
  have hInner : ((c.innerSkip : ℝ) + 1) * c.samples ≤ q.τ * T ^ (1 + 1 / q.β) := by
    rw [Real.rpow_add hT, Real.rpow_one]
    have hnpow := Real.rpow_le_rpow (by positivity) hscaleN (by positivity : 0 ≤ 1 / q.β)
    have hh := mul_le_mul (show 3 * (c.samples : ℝ) ≤ T by linarith) hnpow
      (Real.rpow_nonneg (by positivity) _) hT.le
    nlinarith only [mul_le_mul_of_nonneg_left hh hτ'.le, mul_le_mul_of_nonneg_right hIn (Nat.cast_nonneg c.samples)]
  have hOuter : (c.outerSkip : ℝ) ≤ 3 * (q.τ * (H / q.δ) ^ (1 / q.β)) := by
    have hh := Real.rpow_le_rpow (by linarith : 0 ≤ 4 * J / q.δ)
      (div_le_div_of_nonneg_right hJ hd.le) (by positivity : 0 ≤ 1 / q.β)
    linarith [mul_le_mul_of_nonneg_left hh hτ'.le]
  have heq : T ^ (1 + 1 / q.β) = (16777216 * q.G * q.R / q.ε) ^ (k * (1 + 1 / q.β)) := by
    dsimp [T]; rw [← Real.rpow_mul (by dsimp [x]; positivity)]; congr 1; dsimp [x]; ring
  have h1 := mul_le_mul hInner (show J ≤ H by linarith) (by linarith : 0 ≤ J)
    (mul_nonneg hτ'.le (Real.rpow_nonneg hT.le _))
  have h2 := mul_le_mul_of_nonneg_right hOuter (by linarith : 0 ≤ J)
  have h3 := mul_le_mul_of_nonneg_right (show 3 * J ≤ H by linarith)
    (mul_nonneg hτ'.le (Real.rpow_nonneg (show 0 ≤ H / q.δ by dsimp [H]; positivity) (1 / q.β)))
  change (((c.outerSkip + (c.innerSkip + 1) * c.samples) * (c.trials + 1) * c.trials : ℕ) : ℝ) ≤ _
  push_cast
  rw [← heq]
  change _ ≤ q.τ * H * (T ^ (1 + 1 / q.β) + (H / q.δ) ^ (1 / q.β))
  dsimp only [J] at h1 h2 h3
  nlinarith only [h1, h2, h3]

end LongTails.Proofs.PolynomialMixingBudget
