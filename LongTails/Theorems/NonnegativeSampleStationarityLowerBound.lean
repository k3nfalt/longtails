import LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
import LongTails.Proofs.SampleLossLowerBound

namespace LongTails.Theorems.NonnegativeSampleStationarityLowerBound

open OracleTemplate LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossInstance LongTails.Proofs.SampleLossLowerBound

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊Real.sqrt (q.L * q.Δ) / (2 ^ 32 * q.ε)⌋₊ ^ 3

theorem result : NonConvergence LongTails.Setups.NonnegativeSmoothSampleLossEuclidean.spec budget := by
  intro q hq A _ b hb
  have h : b 0 ≤ stages q ^ 3 := by
    simpa only [budget, stages, show (2 : ℝ) ^ 32 = 4294967296 by norm_num] using hb 0
  obtain ⟨π,hπ⟩ := hard_instance q hq A b h
  exact ⟨objective q π, oracle q π, admissible q hq π, hπ⟩

end LongTails.Theorems.NonnegativeSampleStationarityLowerBound
