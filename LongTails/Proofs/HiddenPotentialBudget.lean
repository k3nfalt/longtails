import LongTails.Proofs.TwoSidedPLBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.HiddenPotential

lemma inner_steps_sufficient {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) :
    let T := ⌈16 * Real.sqrt (ℓ / m)⌉₊
    0 < T ∧ 256 * ℓ ≤ m * ((T : ℝ) * ((T : ℝ) + 1)) := by
  dsimp only
  have hratio : 0 < ℓ / m := div_pos hℓ hm
  have hs : 0 < 16 * Real.sqrt (ℓ / m) := by positivity
  have hT := Nat.le_ceil (16 * Real.sqrt (ℓ / m))
  have hTp : 0 < (⌈16 * Real.sqrt (ℓ / m)⌉₊ : ℝ) := hs.trans_le hT
  refine ⟨by exact_mod_cast hTp, ?_⟩
  have hsq := Real.sq_sqrt hratio.le
  have he : m * (ℓ / m) = ℓ := mul_div_cancel₀ ℓ hm.ne'
  have ht2 : 256 * (ℓ / m) ≤ (⌈16 * Real.sqrt (ℓ / m)⌉₊ : ℝ) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (ℓ / m)]
  have hh := mul_le_mul_of_nonneg_left ht2 hm.le
  nlinarith

lemma stage_steps_sufficient {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) :
    (1 : ℝ) / 2 ^ ⌈Real.log (2 * (μ + β) / μ) / Real.log 2⌉₊ ≤
      μ / (2 * (μ + β)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < 2 * (μ + β) / μ := by positivity
  have hc := Nat.le_ceil (Real.log (2 * (μ + β) / μ) / Real.log 2)
  have hh := (div_le_iff₀ hl2).mp hc
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log ha, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hi := one_div_le_one_div_of_le ha he
  convert hi using 1
  field_simp

lemma outer_steps_sufficient {μ β R ε : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hR : 0 ≤ R) (hε : 0 < ε) :
    (1 - μ / (2 * (μ + β))) ^ ⌈2 * (μ + β) / μ * Real.log (2 + R / ε)⌉₊ * R ≤ ε := by
  let C := 2 * (μ + β) / μ
  have hC : 1 ≤ C := by
    dsimp [C]
    apply (le_div_iff₀ hμ).mpr
    linarith
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have ha : 0 < 2 + R / ε := by positivity
  have hc := Nat.le_ceil (C * Real.log (2 + R / ε))
  have hd := TwoSidedPL.pow_le_exp_window hC ⌈C * Real.log (2 + R / ε)⌉₊
  have hh : Real.log (2 + R / ε) ≤ (⌈C * Real.log (2 + R / ε)⌉₊ : ℝ) / C :=
    (le_div_iff₀ hCp).mpr (by nlinarith [hc])
  have he := Real.exp_le_exp.mpr (neg_le_neg hh)
  rw [Real.exp_neg (Real.log (2 + R / ε)), Real.exp_log ha] at he
  have hi := mul_le_mul_of_nonneg_right (hd.trans he) hR
  have hfinal : (2 + R / ε)⁻¹ * R ≤ ε := by
    rw [inv_mul_eq_div, div_le_iff₀ ha]
    have hx : R / ε * ε = R := div_mul_cancel₀ R hε.ne'
    nlinarith
  have hid : 1 / C = μ / (2 * (μ + β)) := by dsimp [C]; field_simp
  rw [hid] at hi
  exact hi.trans hfinal

lemma logarithm_ge_half {r : ℝ} (hr : 0 ≤ r) : 1 / 2 ≤ Real.log (2 + r) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 + r)
  norm_num at h
  linarith

lemma stage_steps_bound {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) :
    (⌈Real.log (2 * (μ + 512 * s) / μ) / Real.log 2⌉₊ : ℝ) ≤
      24 * Real.log (2 + s / μ) := by
  have hr : 0 ≤ s / μ := by positivity
  have hA : 0 < 2 + s / μ := by positivity
  have hB : 0 < 2 * (μ + 512 * s) / μ := by positivity
  have hlogA := logarithm_ge_half hr
  have hlog2 : 1 / 2 ≤ Real.log 2 := by simpa using logarithm_ge_half (le_refl (0 : ℝ))
  have hl2 : 0 < Real.log 2 := by linarith
  have harg : 2 * (μ + 512 * s) / μ ≤ 1024 * (2 + s / μ) := by
    apply (div_le_iff₀ hμ).mpr
    have he : (2 + s / μ) * μ = 2 * μ + s := by field_simp
    nlinarith
  have hlog := Real.log_le_log hB harg
  rw [Real.log_mul (by norm_num) hA.ne',
    show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow] at hlog
  have hlog2A := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 + s / μ)
  have hfrac : Real.log (2 * (μ + 512 * s) / μ) / Real.log 2 ≤ 22 * Real.log (2 + s / μ) := by
    apply (div_le_iff₀ hl2).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog2) (show 0 ≤ Real.log (2 + s / μ) by linarith)]
  have hB1 : 1 ≤ 2 * (μ + 512 * s) / μ := by
    apply (le_div_iff₀ hμ).mpr
    linarith
  have hceil := Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg hB1) hl2.le)
  linarith

lemma inner_steps_bound {m ℓ : ℝ} (hm : 0 < m) (hmℓ : m ≤ ℓ) :
    (⌈16 * Real.sqrt (ℓ / m)⌉₊ : ℝ) ≤ 17 * Real.sqrt (ℓ / m) := by
  have hratio : 1 ≤ ℓ / m := (le_div_iff₀ hm).mpr (by simpa using hmℓ)
  have hsqrt : 1 ≤ Real.sqrt (ℓ / m) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ ℓ / m), Real.sqrt_nonneg (ℓ / m)]
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 16 * Real.sqrt (ℓ / m) by positivity)
  linarith

lemma outer_steps_bound {μ s R ε : ℝ}
    (hμ : 0 < μ) (hs : 0 ≤ s) (hR : 0 ≤ R) (hε : 0 < ε) :
    (⌈2 * (μ + 512 * s) / μ * Real.log (2 + R / ε)⌉₊ : ℝ) ≤
      4 * (μ + 512 * s) / μ * Real.log (2 + R / ε) := by
  have hl := logarithm_ge_half (show 0 ≤ R / ε by positivity)
  have ha : 2 ≤ 2 * (μ + 512 * s) / μ := by
    apply (le_div_iff₀ hμ).mpr
    linarith
  have hp : 1 ≤ 2 * (μ + 512 * s) / μ * Real.log (2 + R / ε) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ Real.log (2 + R / ε) by linarith)]
  have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * (μ + 512 * s) / μ * Real.log (2 + R / ε))
  have he : 4 * (μ + 512 * s) / μ * Real.log (2 + R / ε) =
      2 * (2 * (μ + 512 * s) / μ * Real.log (2 + R / ε)) := by ring
  rw [he]
  linarith

lemma mixed_condition_bound {μ L s : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L) (hs : 0 ≤ s) :
    (μ + 512 * s) * Real.sqrt ((L + μ + 512 * s) / (μ + 511 * s)) ≤
      1024 * Real.sqrt ((μ + s) * (L + μ + s)) := by
  let a := μ + 512 * s
  let m := μ + 511 * s
  let ℓ := L + μ + 512 * s
  let U := (μ + s) * (L + μ + s)
  have ha : 0 < a := by dsimp [a]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have ha2 : a ≤ 2 * m := by dsimp [a, m]; linarith
  have hap : a * ℓ ≤ 262144 * U := by
    have h₁ : a ≤ 512 * (μ + s) := by dsimp [a]; linarith
    have h₂ : ℓ ≤ 512 * (L + μ + s) := by dsimp [ℓ]; linarith
    have h := mul_le_mul h₁ h₂ hℓ.le (by positivity)
    dsimp [U]
    nlinarith [h]
  have hsq : m * (a * Real.sqrt (ℓ / m)) ^ 2 = a ^ 2 * ℓ := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hℓ.le hm.le)]
    field_simp
  have hbound : (a * Real.sqrt (ℓ / m)) ^ 2 ≤ 524288 * U := by
    apply (mul_le_mul_iff_of_pos_left hm).mp
    have h₁ := mul_le_mul_of_nonneg_right ha2 (mul_nonneg ha.le hℓ.le)
    have h₂ := mul_le_mul_of_nonneg_left hap (show 0 ≤ 2 * m by positivity)
    nlinarith
  have hroot := Real.sq_sqrt hU
  change a * Real.sqrt (ℓ / m) ≤ 1024 * Real.sqrt U
  have hnonneg : 0 ≤ a * Real.sqrt (ℓ / m) := by positivity
  have hright : 0 ≤ 1024 * Real.sqrt U := by positivity
  apply (sq_le_sq₀ hnonneg hright).mp
  nlinarith

lemma total_calls_bound {μ L s R ε : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hs : 0 ≤ s) (hR : 0 ≤ R) (hε : 0 < ε) :
    ⌈2 * (μ + 512 * s) / μ * Real.log (2 + R / ε)⌉₊ *
      (⌈Real.log (2 * (μ + 512 * s) / μ) / Real.log 2⌉₊ *
        ⌈16 * Real.sqrt ((L + μ + 512 * s) / (μ + 511 * s))⌉₊) ≤
      ⌈2097152 * Real.sqrt ((μ + s) * (L + μ + s)) / μ *
        Real.log (2 + s / μ) * Real.log (2 + R / ε)⌉₊ := by
  have hlogA : 0 ≤ Real.log (2 + R / ε) := by
    have := logarithm_ge_half (show 0 ≤ R / ε by positivity)
    linarith
  have hlogB : 0 ≤ Real.log (2 + s / μ) := by
    have := logarithm_ge_half (show 0 ≤ s / μ by positivity)
    linarith
  have ht := inner_steps_bound (show 0 < μ + 511 * s by positivity)
    (show μ + 511 * s ≤ L + μ + 512 * s by linarith)
  have hh := stage_steps_bound hμ hs
  have hn := outer_steps_bound hμ hs hR hε
  have hht := mul_le_mul hh ht (Nat.cast_nonneg _) (show 0 ≤ 24 * Real.log (2 + s / μ) by positivity)
  have hall := mul_le_mul hn hht
    (show 0 ≤ (⌈Real.log (2 * (μ + 512 * s) / μ) / Real.log 2⌉₊ : ℝ) *
      (⌈16 * Real.sqrt ((L + μ + 512 * s) / (μ + 511 * s))⌉₊ : ℝ) by positivity)
    (show 0 ≤ 4 * (μ + 512 * s) / μ * Real.log (2 + R / ε) by positivity)
  have hmix := mul_le_mul_of_nonneg_right (mixed_condition_bound hμ hL hs)
    (show 0 ≤ 1632 / μ * Real.log (2 + s / μ) * Real.log (2 + R / ε) by positivity)
  have he :
      (4 * (μ + 512 * s) / μ * Real.log (2 + R / ε)) *
        ((24 * Real.log (2 + s / μ)) *
          (17 * Real.sqrt ((L + μ + 512 * s) / (μ + 511 * s)))) =
      ((μ + 512 * s) * Real.sqrt ((L + μ + 512 * s) / (μ + 511 * s))) *
        (1632 / μ * Real.log (2 + s / μ) * Real.log (2 + R / ε)) := by ring
  rw [he] at hall
  have hc : 1024 * Real.sqrt ((μ + s) * (L + μ + s)) *
      (1632 / μ * Real.log (2 + s / μ) * Real.log (2 + R / ε)) ≤
      2097152 * Real.sqrt ((μ + s) * (L + μ + s)) / μ *
        Real.log (2 + s / μ) * Real.log (2 + R / ε) := by
    have hp : 0 ≤ Real.sqrt ((μ + s) * (L + μ + s)) / μ *
        Real.log (2 + s / μ) * Real.log (2 + R / ε) := by positivity
    convert mul_le_mul_of_nonneg_right (show (1671168 : ℝ) ≤ 2097152 by norm_num) hp using 1 <;> ring
  have hresult := hall.trans (hmix.trans hc)
  have hceil := Nat.le_ceil (2097152 * Real.sqrt ((μ + s) * (L + μ + s)) / μ *
    Real.log (2 + s / μ) * Real.log (2 + R / ε))
  exact_mod_cast hresult.trans hceil

end OracleTemplate.HiddenPotential
