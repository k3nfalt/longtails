import LongTails.Setups.AsgoFixedRadius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius

lemma horizon_positive (p : Params) : 1 ≤ horizon p := by
  change 1 ≤ _ + 1
  omega

lemma rate_to_accuracy (p : Params) (hp : Valid p) :
    4 * p.R ^ 2 * p.ell / (horizon p : ℝ) +
      2 * Real.sqrt 2 * p.R * p.v / Real.sqrt ((p.M : ℝ) * (horizon p : ℝ)) +
      2 * p.k * p.F ^ 2 / (p.R * (horizon p : ℝ)) ≤ p.delta := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    rcases hp with ⟨hR, hk, hM, _, hell, hv, hd⟩
    have hMr : 0 < (p.M : ℝ) := by exact_mod_cast (by omega : 0 < p.M)
    have hTr : 0 < (horizon p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (horizon_positive p))
    have hc :
        8 * p.R ^ 2 * p.ell / p.delta + 4 * p.k * p.F ^ 2 / (p.R * p.delta) +
          32 * p.R ^ 2 * p.v ^ 2 / ((p.M : ℝ) * p.delta ^ 2) ≤ (horizon p : ℝ) := by
      delta horizon
      rw [Nat.cast_add, Nat.cast_one]
      exact (Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le_one)
    have hfirst : 0 ≤ 8 * p.R ^ 2 * p.ell / p.delta := by positivity
    have hsecond : 0 ≤ 4 * p.k * p.F ^ 2 / (p.R * p.delta) := by positivity
    have hthird : 0 ≤ 32 * p.R ^ 2 * p.v ^ 2 / ((p.M : ℝ) * p.delta ^ 2) := by positivity
    have hdet :
        8 * p.R ^ 2 * p.ell / p.delta + 4 * p.k * p.F ^ 2 / (p.R * p.delta) ≤
          (horizon p : ℝ) := by linarith only [hc, hthird]
    have hdetfrac :
        (8 * p.R ^ 2 * p.ell + 4 * p.k * p.F ^ 2 / p.R) / p.delta ≤
          (horizon p : ℝ) := by
      rw [add_div, div_div]
      exact hdet
    have hdetnum := (div_le_iff₀ hd).mp hdetfrac
    have hdetfinal :
        4 * p.R ^ 2 * p.ell / (horizon p : ℝ) +
          2 * p.k * p.F ^ 2 / (p.R * (horizon p : ℝ)) ≤ p.delta / 2 := by
      rw [← div_div, ← add_div]
      apply (div_le_iff₀ hTr).mpr
      have he : 4 * p.k * p.F ^ 2 / p.R = 2 * (2 * p.k * p.F ^ 2 / p.R) := by ring
      rw [he] at hdetnum
      nlinarith only [hdetnum]
    have hnoise :
        32 * p.R ^ 2 * p.v ^ 2 / ((p.M : ℝ) * p.delta ^ 2) ≤
          (horizon p : ℝ) := by linarith only [hc, hfirst, hsecond]
    have hnoisenum := (div_le_iff₀ (mul_pos hMr (sq_pos_of_pos hd))).mp hnoise
    have hs : 0 < Real.sqrt ((p.M : ℝ) * (horizon p : ℝ)) :=
      Real.sqrt_pos.mpr (mul_pos hMr hTr)
    have hs2 := Real.sq_sqrt (mul_nonneg hMr.le hTr.le)
    have hN : 0 ≤ 2 * Real.sqrt 2 * p.R * p.v := by positivity
    have hD : 0 ≤ p.delta / 2 * Real.sqrt ((p.M : ℝ) * (horizon p : ℝ)) := by positivity
    have hsq :
        (2 * Real.sqrt 2 * p.R * p.v) ^ 2 ≤
          (p.delta / 2 * Real.sqrt ((p.M : ℝ) * (horizon p : ℝ))) ^ 2 := by
      calc
        _ = 8 * p.R ^ 2 * p.v ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        _ ≤ (p.delta / 2) ^ 2 * ((p.M : ℝ) * (horizon p : ℝ)) := by
          nlinarith only [hnoisenum]
        _ = _ := by rw [mul_pow, hs2]
    have hsmall := (sq_le_sq₀ hN hD).mp hsq
    have hnoisefinal :
        2 * Real.sqrt 2 * p.R * p.v /
          Real.sqrt ((p.M : ℝ) * (horizon p : ℝ)) ≤ p.delta / 2 :=
      (div_le_iff₀ hs).mpr hsmall
    linarith only [hdetfinal, hnoisefinal]
  )

end OracleTemplate.AsgoFixedRadius
