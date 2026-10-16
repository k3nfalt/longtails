import LongTails.Setups.AdaptivePairedZerothOrder
import LongTails.Algorithms.AdaptivePairedZerothOrder
import LongTails.Proofs.AdaptivePairedZerothOrderWork

namespace LongTails.Theorems.AdaptivePairedZerothOrderConfidence

open OracleTemplate LongTails.Setups.AdaptivePairedZerothOrder

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 6 * p.T + 4 * p.N

theorem result : Convergence LongTails.Setups.AdaptivePairedZerothOrder.spec budget := by
  refine ⟨LongTails.Algorithms.AdaptivePairedZerothOrder.algorithm, ?_, ?_⟩
  · intro p hv I O hadm
    exact (LongTails.Proofs.AdaptivePairedZerothOrderWork.certified_success p hv I O hadm).2
  · intro p hv
    trivial

end LongTails.Theorems.AdaptivePairedZerothOrderConfidence
