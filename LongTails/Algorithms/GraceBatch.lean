import LongTails.Setups.GraphBandwidthSmoothNonconvex
import LongTails.Algorithms.DistributedBatchedSgd

namespace LongTails.Algorithms.GraceBatch

open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.DistributedBatchedSgd

abbrev statistical (p : Params) : LongTails.Setups.DistributedSmoothNonconvex.Params :=
  { p.base with L := 2 * p.L }

noncomputable def B (p : Params) := targetBatch (statistical p)

noncomputable def batchTime (p : Params) (S : Finset (Fin p.n)) : DistributedTemplate.Time :=
  (B p + (S.card : DistributedTemplate.Time)) / ∑ i ∈ S, (p.h i)⁻¹

noncomputable def batches (p : Params) (S : Finset (Fin p.n)) : Fin p.n → ℕ := by
  classical
  let c := fun i => ⌊(batchTime p S : ℝ) / (p.h i : ℝ)⌋₊
  exact if h : ∃ a : Fin p.n → ℕ, (∀ i, a i ≤ c i) ∧
      (∀ i ∉ S, a i = 0) ∧ ∑ i ∈ S, a i = B p then h.choose else fun _ => 0

noncomputable def tuning (p : Params) (S : Finset (Fin p.n)) : Config (statistical p) :=
  { config (statistical p) with batch := batches p S }

end LongTails.Algorithms.GraceBatch
