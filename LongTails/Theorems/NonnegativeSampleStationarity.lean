import LongTails.Setups.NonnegativeSmoothSampleLoss
import LongTails.Proofs.NonnegativeSampleStorm

namespace LongTails.Theorems.NonnegativeSampleStationarity

open OracleTemplate OracleTemplate.NormalizedStorm
open LongTails.Setups.NonnegativeSmoothSampleLoss LongTails.Proofs.NonnegativeSampleStorm

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈8192 * Real.sqrt (1 + q.L * q.Δ / q.ε ^ 2) ^ 3⌉₊

theorem result : Convergence LongTails.Setups.NonnegativeSmoothSampleLoss.spec budget := by
  refine ⟨fun q => normalizedStorm (tEta q.L q.L 0 q.Δ q.ε) (tA q.L q.L 0 q.Δ q.ε)
    (tB0 q.L q.L 0 q.Δ q.ε) (tT q.L q.L 0 q.Δ q.ε) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O hO
  exact output_accurate q hq f O hO _ (enough_calls hq.1 hq.2.1 hq.2.2)

end LongTails.Theorems.NonnegativeSampleStationarity
