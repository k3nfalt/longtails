import LongTails.Setups.GeneralizedSmoothConvexFull
import LongTails.Proofs.GeneralizedSmoothTransientParameters
import Mathlib.Tactic

namespace LongTails.Proofs.FullGeneralizedSmoothParameters

lemma log_half_le (q : ℝ) (hq : 0 ≤ q) : 1 / 2 ≤ Real.log (2 + q) := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 + q)
  have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num [Real.log_div] at ht
  linarith

lemma budget_cases (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (N : ℕ)
    (hN : N ≤ ⌊(s + q / Real.log (2 + q)) / 8388608⌋₊) :
    N = 0 ∨ (8192 ≤ s ∧ N ≤ ⌊s / 16384⌋₊) ∨
      (1048576 ≤ q ∧ N ≤ ⌊q / (4096 * Real.log (2 + q))⌋₊) := by
  have hl := log_half_le q hq
  have hlp : 0 < Real.log (2 + q) := by linarith
  let v := q / Real.log (2 + q)
  have hv : 0 ≤ v := div_nonneg hq hlp.le
  have hvq : v ≤ 2 * q := by
    apply (div_le_iff₀ hlp).mpr
    nlinarith
  have htrans (hsv : s ≤ v) :
      N ≤ ⌊q / (4096 * Real.log (2 + q))⌋₊ := by
    apply hN.trans
    apply Nat.floor_le_floor
    change (s + v) / 8388608 ≤ _
    have he : q / (4096 * Real.log (2 + q)) = v / 4096 := by dsimp [v]; ring
    rw [he]
    linarith
  have hacc (hvs : v ≤ 256 * s) : N ≤ ⌊s / 16384⌋₊ := by
    apply hN.trans
    apply Nat.floor_le_floor
    change (s + v) / 8388608 ≤ s / 16384
    linarith
  by_cases hql : 1048576 ≤ q
  · by_cases hsv : s ≤ v
    · exact Or.inr (Or.inr ⟨hql, htrans hsv⟩)
    · have hu := GeneralizedSmoothTransientParameters.log_upper_linear q hql
      have hvbig : 32768 ≤ v := by
        apply (le_div_iff₀ hlp).mpr
        linarith
      exact Or.inr (Or.inl ⟨by linarith, hacc (by linarith)⟩)
  · by_cases hbig : 8192 ≤ s
    · exact Or.inr (Or.inl ⟨hbig, hacc (by linarith)⟩)
    · have hf : ⌊(s + q / Real.log (2 + q)) / 8388608⌋₊ < 1 := by
        apply (Nat.floor_lt (by positivity : 0 ≤ (s + q / Real.log (2 + q)) / 8388608)).mpr
        norm_num only [Nat.cast_one]
        change (s + v) / 8388608 < 1
        linarith
      exact Or.inl (by omega)

open LongTails.Setups.GeneralizedSmoothConvexFull

lemma dimension_pos (p : Params) (hp : spec.valid p) : 0 < p.d := by
  have hq : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hs := Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)
  have hh : 0 < 17592186044416 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5 := by
    positivity
  exact lt_of_lt_of_le (Nat.ceil_pos.mpr hh) hp.2.2.2.2.2

lemma valid_nonempty : ∃ p : Params, spec.valid p := by
  refine ⟨{ d := 54975581388800000, L0 := 1, L1 := 0, x0 := 0, R := 4, ε := 1 }, ?_⟩
  norm_num [spec, show Real.sqrt (16 : ℝ) = 4 by norm_num]

end LongTails.Proofs.FullGeneralizedSmoothParameters
