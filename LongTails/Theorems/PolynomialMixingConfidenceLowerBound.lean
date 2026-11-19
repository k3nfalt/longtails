import LongTails.Setups.PolynomialMixingSubgradient
import LongTails.Proofs.PolynomialMixingHardInstance

namespace LongTails.Theorems.PolynomialMixingConfidenceLowerBound

open OracleTemplate LongTails.Setups.PolynomialMixingSubgradient
open LongTails.Proofs.PolynomialMixingHardInstance

noncomputable def budget : (let S := LongTails.Setups.PolynomialMixingSubgradient.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊q.τ * ((q.G * q.R / (8 * q.ε)) ^ (q.p / (q.p - 1) * (1 + 1 / q.β)) * Real.log (1 / (4 * q.δ)) + (16 * q.δ) ^ (-(1 / q.β))) / (8 * (1 + 2 * q.β))⌋₊

theorem result : NonConvergence LongTails.Setups.PolynomialMixingSubgradient.spec budget := by
  intro q hp alg _ b hb
  have he : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  change ∃ _ _, _ ∧ _
  rw [he]
  change Fails q alg (b 0)
  obtain ⟨_, hR, hG, hp1, _, hβ, hτ, hε, _, hδ, hδ'⟩ := And.intro hp.1 hp.2
  have hl : 0 ≤ Real.log (1 / (4 * q.δ)) := Real.log_nonneg ((one_le_div (by positivity)).mpr (by linarith))
  have hpos : 0 ≤ q.τ := by linarith
  have h := (Nat.cast_le.mpr (hb 0) : (b 0 : ℝ) ≤ (budget q 0 : ℝ))
  unfold budget at h
  have hh := h.trans (Nat.floor_le (by positivity))
  by_cases ha : (b 0 : ℝ) ≤ q.τ * (q.G * q.R / (8 * q.ε)) ^ (q.p / (q.p - 1) * (1 + 1 / q.β)) * Real.log (1 / (4 * q.δ)) / (4 * (1 + 2 * q.β))
  · exact accuracy_hard q hp alg _ ha
  · apply confidence_hard q hp alg
    push Not at ha
    field_simp at hh ha ⊢
    nlinarith

end LongTails.Theorems.PolynomialMixingConfidenceLowerBound
