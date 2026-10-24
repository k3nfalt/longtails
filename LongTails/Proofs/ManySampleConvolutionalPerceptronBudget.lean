import LongTails.Proofs.ManySampleConvolutionalPerceptronParameters

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronBudget

open ManySampleConvolutionalPerceptronParameters

noncomputable def logarithm (p : Tuning) : ℝ := Real.log (1 / p.δ)

lemma logarithm_ge_one (p : Tuning) : 1 ≤ logarithm p := by
  have hl := Real.log_le_log p.delta_pos p.delta_le
  rw [Real.log_exp] at hl
  simp only [logarithm, one_div, Real.log_inv]
  linarith

lemma log_scaled_ge_one (p : Tuning) : 1 ≤ logarithm p / p.ρ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos p.rho_pos)).mpr
  have hr : p.ρ ^ 2 ≤ 1 := by nlinarith [p.rho_pos, p.rho_le]
  linarith [logarithm_ge_one p]

lemma burnin_budget (p : Tuning) : (burnIn p.ρ p.δ : ℝ) + 1 ≤ 12 * (logarithm p / p.ρ ^ 2) := by
  have hl := logarithm_ge_one p
  have hx : 0 ≤ 8 / p.ρ ^ 2 * Real.log (1 / p.δ) := by
    have hlog : 0 ≤ Real.log (1 / p.δ) := by change 0 ≤ logarithm p; linarith
    positivity
  have hc := Nat.ceil_lt_add_one hx
  have hr := log_scaled_ge_one p
  have hid : 8 / p.ρ ^ 2 * Real.log (1 / p.δ) = 8 * (logarithm p / p.ρ ^ 2) := by
    unfold logarithm
    ring
  simp only [burnIn, Nat.cast_add, Nat.cast_ofNat]
  rw [hid] at hc ⊢
  linarith

lemma unit_budget (p : Tuning) : p.unit ≤ 12 * (logarithm p / (p.ρ ^ 2 * p.κ)) := by
  have hb := div_le_div_of_nonneg_right (burnin_budget p) p.kappa_pos.le
  change ((burnIn p.ρ p.δ : ℝ) + 1) / p.κ ≤ _
  convert hb using 1; ring

lemma negative_budget (p : Tuning) : (p.negatives : ℝ) + 1 ≤
    1048576 * (logarithm p / (p.ρ ^ 2 * p.κ)) ^ 2 := by
  have hu := unit_budget p
  have hu0 := p.unit_ge_one
  have hM := p.negatives_upper
  have hz : 0 ≤ logarithm p / (p.ρ ^ 2 * p.κ) := by
    have := logarithm_ge_one p
    have := p.rho_pos
    have := p.kappa_pos
    positivity
  have hs : p.unit ^ 2 ≤ 144 * (logarithm p / (p.ρ ^ 2 * p.κ)) ^ 2 := by nlinarith
  nlinarith

lemma log_eight_le_three : Real.log (8 : ℝ) ≤ 3 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
  norm_num at h ⊢
  linarith

lemma reference_log (p : Tuning) : Real.log (8 / p.δ ^ 2) = Real.log 8 + 2 * logarithm p := by
  rw [Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero 2 (ne_of_gt p.delta_pos)), Real.log_pow]
  simp only [logarithm, one_div, Real.log_inv, Nat.cast_ofNat]
  ring

lemma reference_budget (p : Tuning) : (p.referenceLength : ℝ) ≤ 23 * (logarithm p / p.ρ) := by
  have hl := logarithm_ge_one p
  have hr1 : p.ρ ≤ 1 := p.rho_le.trans (by norm_num)
  have hz : 1 ≤ logarithm p / p.ρ := (le_div_iff₀ p.rho_pos).mpr (by linarith)
  have hlog : 0 ≤ Real.log (8 / p.δ ^ 2) := by
    rw [reference_log]
    have h8 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hx : 0 ≤ 4 / p.ρ * Real.log (8 / p.δ ^ 2) :=
    mul_nonneg (div_nonneg (by norm_num) p.rho_pos.le) hlog
  have hc := Nat.ceil_lt_add_one hx
  have hupper : Real.log (8 / p.δ ^ 2) ≤ 5 * logarithm p := by
    rw [reference_log]
    linarith [log_eight_le_three]
  have hm := mul_le_mul_of_nonneg_left hupper (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) p.rho_pos.le)
  have hid : 4 / p.ρ * (5 * logarithm p) = 20 * (logarithm p / p.ρ) := by ring
  rw [hid] at hm
  simp only [Tuning.referenceLength, Nat.cast_add, Nat.cast_ofNat]
  linarith

lemma block_budget (p : Tuning) (N : ℕ) :
    ((p.negatives + 1) * (N + p.referenceLength) : ℝ) ≤
      33554432 * (logarithm p / (p.ρ ^ 2 * p.κ)) ^ 2 * (N + logarithm p / p.ρ) := by
  have hM := negative_budget p
  have hL := reference_budget p
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlog := logarithm_ge_one p
  have hz : 0 ≤ logarithm p / p.ρ := div_nonneg (by linarith) p.rho_pos.le
  have hscan : (N : ℝ) + p.referenceLength ≤ 23 * (N + logarithm p / p.ρ) := by linarith
  have hmul := mul_le_mul hM hscan (by positivity : (0 : ℝ) ≤ N + p.referenceLength) (by positivity)
  have hpos : 0 ≤ (logarithm p / (p.ρ ^ 2 * p.κ)) ^ 2 * (N + logarithm p / p.ρ) := by positivity
  nlinarith

lemma scaled_block_budget (p : Tuning) (N : ℕ) {g R μ : ℝ}
    (hg : 0 < g) (hR : 0 < R) (hμ : 0 < μ)
    (hρ : p.ρ = g / (4 * R)) (hδ : p.δ = (μ / (4 * R)) ^ 2) :
    ((p.negatives + 1) * (N + p.referenceLength) : ℝ) ≤
      34359738368 * (R / g) ^ 4 * (Real.log (16 * R ^ 2 / μ ^ 2)) ^ 2 *
        (N + (R / g) * Real.log (16 * R ^ 2 / μ ^ 2)) / p.κ ^ 2 := by
  have hid : 1 / p.δ = 16 * R ^ 2 / μ ^ 2 := by
    rw [hδ]
    field_simp
    ring
  have hl : logarithm p = Real.log (16 * R ^ 2 / μ ^ 2) := by
    unfold logarithm
    rw [hid]
  have hb := block_budget p N
  have hnon : 0 ≤ logarithm p := (by norm_num : (0 : ℝ) ≤ 1).trans (logarithm_ge_one p)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hscale : 0 ≤ (R / g) * logarithm p := mul_nonneg (div_nonneg hR.le hg.le) hnon
  have heq : 33554432 * (logarithm p / (p.ρ ^ 2 * p.κ)) ^ 2 * (N + logarithm p / p.ρ) =
      8589934592 * (R / g) ^ 4 * (logarithm p) ^ 2 / p.κ ^ 2 *
        (N + 4 * (R / g) * logarithm p) := by
    rw [hρ]
    field_simp
    ring
  rw [heq] at hb
  rw [← hl]
  have hfactor : 0 ≤ 8589934592 * (R / g) ^ 4 * (logarithm p) ^ 2 / p.κ ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left
    (show (N : ℝ) + 4 * (R / g) * logarithm p ≤ 4 * (N + (R / g) * logarithm p) by linarith)
    hfactor
  calc
    _ ≤ _ := hb.trans hm
    _ = _ := by ring

end LongTails.Proofs.ManySampleConvolutionalPerceptronBudget
