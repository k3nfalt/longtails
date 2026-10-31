import LongTails.Setups.SpectralSmoothAdamComparison
import LongTails.Proofs.SeparationLower

namespace LongTails.Proofs.AdamComparisonTuning

open OracleTemplate MeasureTheory
open LongTails.Setups.SpectralSmoothAdamComparison

lemma base_valid {p : Public} (hp : spec.valid p) :
    LongTails.Setups.BatchedSpectralSmooth.spec.valid p.toBase :=
  ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1.le, hp.2.2.2.1⟩

lemma sgd_lower {p : Public} (hp : spec.valid p) : SgdLower p := by
  intro η hη B T hB A hA
  obtain ⟨f, O, hadm, hbound⟩ := LongTails.Proofs.SeparationLower.sgd_lower_bound
    p.toBase (base_valid hp) (by simpa [Public.toBase] using (show 2 ≤ p.r by omega))
    hp.2.2.2.2 hη hB hA
  refine ⟨f, O, hadm, fun hs => ?_⟩
  have h := hbound hs
  simp only [Public.toBase, min_self] at h
  have heps : 0 < p.ε ^ 2 := sq_pos_of_pos hp.2.2.2.1
  nlinarith

lemma strict_adam_separation {r : ℕ} {L Δ ε K N : ℝ}
    (hN : 0 ≤ N) (hK : N ≤ K)
    (hr₂ : 64 * K ^ 2 < (r - 1 : ℕ))
    (hr₃ : 4096 * ε ^ 2 * K ^ 3 < (r - 1 : ℕ) * L * Δ) :
    ¬ ((r - 1 : ℕ) ≤ 64 * N ^ 2 ∨
      (r - 1 : ℕ) * L * Δ ≤ 4096 * ε ^ 2 * N ^ 3) := by
  have h₂ := pow_le_pow_left₀ hN hK 2
  have h₃ := pow_le_pow_left₀ hN hK 3
  rintro (h | h)
  · linarith
  · have := mul_le_mul_of_nonneg_left h₃ (show 0 ≤ 4096 * ε ^ 2 by positivity)
    linarith

end LongTails.Proofs.AdamComparisonTuning
