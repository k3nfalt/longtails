import LongTails.Proofs.CertifiedLevelBroxStart
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma log_four_thirds_ge : 0.4 * Real.log 2 ≤ Real.log (4 / 3) := by
  have h : Real.log ((2 : ℝ) ^ 2) ≤ Real.log ((4 / 3 : ℝ) ^ 5) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

lemma phases_le {p : ℕ} {Y : ℝ} (hY : (4 / 3 : ℝ) ^ p ≤ Y) :
    (p : ℝ) ≤ 2.5 * Real.logb 2 Y := by
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY
  have h := Real.log_le_log (by positivity) hY
  rw [Real.log_pow] at h
  have hl := log_four_thirds_ge
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Real.logb, ← mul_div_assoc, le_div_iff₀ h2]
  nlinarith [mul_le_mul_of_nonneg_left hl hp]

lemma doublings_le {d : ℕ} {Y : ℝ} (hY : (2 : ℝ) ^ d ≤ 2 * Y) :
    (d : ℝ) ≤ 1 + Real.logb 2 Y := by
  have hY0 : 0 < Y := by
    have : (0 : ℝ) < 2 ^ d := by positivity
    linarith
  have h := Real.log_le_log (by positivity) hY
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hY0)] at h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb]
  have : (d : ℝ) ≤ 1 + Real.log Y / Real.log 2 := by
    rw [show (1 : ℝ) + Real.log Y / Real.log 2 = (Real.log 2 + Real.log Y) / Real.log 2 by
      field_simp]
    rw [le_div_iff₀ h2]; linarith
  exact this

lemma sqrt_one_add_le (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (1 + 2 * a) ≤ 1 + 1.4143 * Real.sqrt a := by
  rw [Real.sqrt_le_left (by positivity)]
  have hs := Real.sq_sqrt ha
  have hn := Real.sqrt_nonneg a
  nlinarith

lemma running_bound (c : Ctx E) {s : State E} {T : ℕ} (hp : Params c s) (hc : Count c s T)
    (hgt : c.ε < gap s) (hcalls : s.calls ≤ 4 * phaseK c.R s) :
    (T : ℝ) < 400 * Real.sqrt (c.L * c.R ^ 2 / c.ε) +
      40 * Real.logb 2 (2 + (c.Δ + c.L * c.R ^ 2) / c.ε) + 300 := by
  have he := c.ε_pos
  have hR := hp.R_pos
  have hgap : 0 < gap s := lt_trans he hgt
  set Y : ℝ := 2 + (c.Δ + c.L * c.R ^ 2) / c.ε with hYdef
  have hΔ : 0 ≤ c.Δ := le_trans (sub_nonneg.mpr (c.xs_min c.x0 c.x0_mem)) c.gap0
  have hLR : 0 ≤ c.L * c.R ^ 2 := mul_nonneg c.L_nonneg (sq_nonneg _)
  have hY2 : 2 ≤ Y := by rw [hYdef]; have : 0 ≤ (c.Δ + c.L * c.R ^ 2) / c.ε := by positivity
                         linarith
  have hlogY : 0 ≤ Real.logb 2 Y := Real.logb_nonneg (by norm_num) (by linarith)
  have hLh : s.Lh ≤ c.ε / c.R ^ 2 + 2 * c.L := by
    rcases hp.Lh_le with h0 | h0
    · rw [hp.Lh_eq, h0]; have := c.L_nonneg; simp; linarith
    · have : 0 ≤ c.ε / c.R ^ 2 := by positivity
      linarith
  have hL0 : 0 ≤ s.Lh := by rw [hp.Lh_eq]; positivity
  have hX : s.Lh * c.R ^ 2 / gap s ≤ 1 + 2 * (c.L * c.R ^ 2 / c.ε) := by
    rw [div_le_iff₀ hgap]
    have h1 : s.Lh * c.R ^ 2 ≤ (c.ε / c.R ^ 2 + 2 * c.L) * c.R ^ 2 :=
      mul_le_mul_of_nonneg_right hLh (sq_nonneg _)
    have h2 : (c.ε / c.R ^ 2 + 2 * c.L) * c.R ^ 2 = c.ε * (1 + 2 * (c.L * c.R ^ 2 / c.ε)) := by
      field_simp
    have h3 : c.ε * (1 + 2 * (c.L * c.R ^ 2 / c.ε)) ≤ (1 + 2 * (c.L * c.R ^ 2 / c.ε)) * gap s := by
      have : 0 ≤ 1 + 2 * (c.L * c.R ^ 2 / c.ε) := by positivity
      nlinarith
    linarith
  have hsX : Real.sqrt (s.Lh * c.R ^ 2 / gap s) ≤ 1 + 1.4143 * Real.sqrt (c.L * c.R ^ 2 / c.ε) :=
    le_trans (Real.sqrt_le_sqrt hX) (sqrt_one_add_le _ (by positivity))
  have hcost := run_cost c.R s.Lh (gap s)
  have hcr : (s.calls : ℝ) ≤ 4 * (phaseK c.R s : ℝ) := by exact_mod_cast hcalls
  unfold phaseK at hcr
  have hpY : (4 / 3 : ℝ) ^ s.phases ≤ Y := by
    have h := hp.shrink
    have hpos : 0 < (4 / 3 : ℝ) ^ s.phases := by positivity
    have h1 : c.ε * (4 / 3 : ℝ) ^ s.phases ≤ c.Δ + c.L * c.R ^ 2 / 2 := by nlinarith
    have h2 : c.Δ + c.L * c.R ^ 2 / 2 ≤ c.ε * Y := by
      rw [hYdef, mul_add, mul_div_cancel₀ _ (ne_of_gt he)]; nlinarith
    have := le_trans h1 h2
    exact le_of_mul_le_mul_left this he
  have hdY : (2 : ℝ) ^ s.doublings ≤ 2 * Y := by
    have h1 : c.ε / c.R ^ 2 * 2 ^ s.doublings ≤ c.ε / c.R ^ 2 + 2 * c.L := by
      rw [← hp.Lh_eq]; exact hLh
    have hpos : 0 < c.ε / c.R ^ 2 := by positivity
    have h2 : (2 : ℝ) ^ s.doublings ≤ 1 + 2 * (c.L * c.R ^ 2 / c.ε) := by
      rw [← mul_le_mul_iff_right₀ hpos]
      have : c.ε / c.R ^ 2 * (1 + 2 * (c.L * c.R ^ 2 / c.ε)) = c.ε / c.R ^ 2 + 2 * c.L := by
        field_simp
      rw [this]; exact h1
    have h3 : 1 + 2 * (c.L * c.R ^ 2 / c.ε) ≤ 2 * Y := by
      rw [hYdef]
      have : c.L * c.R ^ 2 / c.ε ≤ (c.Δ + c.L * c.R ^ 2) / c.ε :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt he)
      linarith
    linarith
  have hpb := phases_le hpY
  have hdb := doublings_le hdY
  unfold Count at hc
  have hsq := Real.sqrt_nonneg (s.Lh * c.R ^ 2 / gap s)
  have hsq2 := Real.sqrt_nonneg (c.L * c.R ^ 2 / c.ε)
  nlinarith

end OracleTemplate.CertifiedLevelBrox
