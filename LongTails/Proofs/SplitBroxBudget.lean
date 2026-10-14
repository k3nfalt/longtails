import LongTails.Setups.KnownValueSmoothConvexLocalLinear
import LongTails.Proofs.SplitBroxStep

noncomputable section

namespace OracleTemplate.SplitBrox

open LongTails.Setups.KnownValueSmoothConvexLocalLinear

def horizon (p : Public) : ℕ := ⌈Real.sqrt (10 * p.L * p.R ^ 2 / p.ε)⌉₊ + 1

def proofRadius (p : Public) : ℝ := Real.sqrt (p.R ^ 2 + p.ε / (10 * p.L))

def baseRadius (p : Public) : ℝ := proofRadius p / Real.sqrt (horizon p)

lemma horizon_pos (p : Public) : 0 < horizon p := by unfold horizon; omega

lemma horizon_weight_pos (p : Public) : 0 < potentialWeight (horizon p) := by
  unfold potentialWeight
  have h : (0 : ℝ) < horizon p := by exact_mod_cast horizon_pos p
  positivity

lemma tuning (p : Public) (hL : 0 < p.L) (he : 0 < p.ε) :
    0 < baseRadius p ∧ p.R ^ 2 ≤ proofRadius p ^ 2 ∧
    proofRadius p ^ 2 = (horizon p : ℝ) * baseRadius p ^ 2 ∧
    5 * p.L * proofRadius p ^ 2 ≤ potentialWeight (horizon p) * p.ε := by
  have hD : 0 < p.R ^ 2 + p.ε / (10 * p.L) := by positivity
  have hDs : proofRadius p ^ 2 = p.R ^ 2 + p.ε / (10 * p.L) := Real.sq_sqrt (le_of_lt hD)
  have hDp : 0 < proofRadius p := Real.sqrt_pos.mpr hD
  have hK : (0 : ℝ) < horizon p := by exact_mod_cast horizon_pos p
  have hKs : (Real.sqrt (horizon p)) ^ 2 = (horizon p : ℝ) := Real.sq_sqrt (le_of_lt hK)
  have hKp : 0 < Real.sqrt (horizon p) := Real.sqrt_pos.mpr hK
  refine ⟨div_pos hDp hKp, ?_, ?_, ?_⟩
  · rw [hDs]; exact le_add_of_nonneg_right (by positivity)
  · unfold baseRadius
    rw [div_pow, hKs]
    field_simp
  · let t : ℝ := 10 * p.L * p.R ^ 2 / p.ε
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hc : Real.sqrt t ≤ (⌈Real.sqrt t⌉₊ : ℝ) := Nat.le_ceil _
    have hcs : t ≤ (⌈Real.sqrt t⌉₊ : ℝ) ^ 2 := by
      have hh := pow_le_pow_left₀ (Real.sqrt_nonneg t) hc 2
      rwa [Real.sq_sqrt ht] at hh
    have hbound : t + 1 ≤ (horizon p : ℝ) * ((horizon p : ℝ) + 1) := by
      unfold horizon
      change t + 1 ≤ ((⌈Real.sqrt t⌉₊ + 1 : ℕ) : ℝ) * (((⌈Real.sqrt t⌉₊ + 1 : ℕ) : ℝ) + 1)
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) ⌈Real.sqrt t⌉₊]
    have hm := mul_le_mul_of_nonneg_right hbound (le_of_lt he)
    have hid : (t + 1) * p.ε = 10 * p.L * proofRadius p ^ 2 := by
      rw [hDs]
      dsimp [t]
      field_simp
    rw [hid] at hm
    unfold potentialWeight
    nlinarith

end OracleTemplate.SplitBrox
