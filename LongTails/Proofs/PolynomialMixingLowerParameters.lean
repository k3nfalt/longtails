import LongTails.Proofs.PolynomialMixingBurstCalibration

namespace LongTails.Proofs.PolynomialMixingLowerParameters

open LongTails.Proofs.PolynomialMixingBurst

lemma rare_calibration {p x : ℝ} (hp : 1 < p) (hp' : p ≤ 2) (hx : 1 ≤ x) :
    let k := p / (p - 1)
    let a := (2 * x) ^ (-k)
    0 < a ∧ a ≤ 1 / 4 ∧ a * a ^ (-(1 / p)) = 1 / (2 * x) ∧
      a * (a ^ (-(1 / p))) ^ p = 1 ∧ 2 * a ≤ (x ^ k)⁻¹ := by
  let k := p / (p - 1)
  let a := (2 * x) ^ (-k)
  have hp0 : 0 < p := by linarith
  have hk : 2 ≤ k := (le_div_iff₀ (by linarith : 0 < p - 1)).mpr (by linarith)
  have hx0 : 0 < x := by linarith
  have hb : 0 < 2 * x := by positivity
  have ha : 0 < a := Real.rpow_pos_of_pos hb _
  have ha1 : a ≤ 1 / 4 := by
    have h₁ := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 2 * x) hk
    rw [Real.rpow_two] at h₁
    have h₂ : 4 ≤ (2 * x) ^ k := by nlinarith [sq_nonneg (x - 1)]
    change (2 * x) ^ (-k) ≤ _
    rw [Real.rpow_neg hb.le, inv_eq_one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) h₂
  refine ⟨ha, ha1, ?_, ?_, ?_⟩
  · change a * a ^ (-(1 / p)) = _
    nth_rw 1 [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    dsimp only [a]
    rw [← Real.rpow_mul hb.le, show -k * (1 + -(1 / p)) = -1 by
      dsimp [k]; field_simp [ne_of_gt (sub_pos.mpr hp), hp0.ne']; ring, Real.rpow_neg_one, one_div]
  · change a * (a ^ (-(1 / p))) ^ p = 1
    rw [← Real.rpow_mul ha.le, show -(1 / p) * p = -1 by field_simp,
      Real.rpow_neg_one, mul_inv_cancel₀ ha.ne']
  · change 2 * (2 * x) ^ (-k) ≤ (x ^ k)⁻¹
    rw [Real.rpow_neg hb.le, Real.mul_rpow (by norm_num) hx0.le, mul_inv_rev]
    have h₂ : 2 ≤ (2 : ℝ) ^ k := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ k by linarith)
    have hi : 2 * ((2 : ℝ) ^ k)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact h₂
    nlinarith [mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr (Real.rpow_nonneg hx0.le k))]

lemma rare_budget_le {x p β τ : ℝ} (hx : 1 ≤ x) (hp : 1 < p) (hp' : p ≤ 2)
    (hβ : 0 < β) (hτ : 0 < τ) :
    let k := p / (p - 1)
    let a := (2 * x) ^ (-k)
    τ * x ^ (k * (1 + 1 / β)) / (4 * (1 + 2 * β)) ≤ width a β τ / (2 * a) := by
  let k := p / (p - 1)
  let a := (2 * x) ^ (-k)
  obtain ⟨ha, ha', _, _, hax⟩ := rare_calibration hp hp' hx
  have hx0 : 0 < x := by linarith
  change 2 * a ≤ (x ^ k)⁻¹ at hax
  have hpow : x ^ k * (2 * a) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hax (Real.rpow_nonneg hx0.le k)
    simpa only [mul_inv_cancel₀ (Real.rpow_pos_of_pos hx0 k).ne'] using hh
  have h₂ : (x ^ k) ^ (1 / β) ≤ (2 * a) ^ (-(1 / β)) := by
    have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 2 * a) hax
      (neg_nonpos.mpr (by positivity : 0 ≤ 1 / β))
    simpa only [Real.inv_rpow (Real.rpow_nonneg hx0.le k), Real.rpow_neg (Real.rpow_nonneg hx0.le k),
      inv_inv] using hh
  have hw := width_lower ha ha' hβ hτ.le
  change τ * x ^ (k * (1 + 1 / β)) / (4 * (1 + 2 * β)) ≤ width a β τ / (2 * a)
  rw [Real.rpow_mul hx0.le, Real.rpow_add (Real.rpow_pos_of_pos hx0 k), Real.rpow_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity : 0 < 2 * a)).mpr
  have h₃ := mul_le_mul hpow h₂ (Real.rpow_nonneg (Real.rpow_nonneg hx0.le k) _) zero_le_one
  have hw' := (div_le_iff₀ (by positivity)).mp hw
  nlinarith [mul_le_mul_of_nonneg_left h₃ hτ.le]

end LongTails.Proofs.PolynomialMixingLowerParameters
