import LongTails.Setups.ZerothOrderSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.ZerothOrderConvergence

namespace OracleTemplate.ZerothOrder.AcceleratedTwoPointZerothOrderConvex

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈64 * q.d * Real.sqrt (q.L * q.R ^ 2 / q.ε) + 512 * q.L * q.d ^ 2 * q.R ^ 2 * q.σ / q.ε ^ 2 + 256 * q.L * q.d ^ 2 * q.R ^ 2 * q.σ ^ 2 / q.ε ^ 3 + 1⌉₊ * 2

set_option maxHeartbeats 1500000 in
theorem result :
    Convergence LongTails.Setups.ZerothOrderSmoothAndConvex.spec budget := by
  have h (q : spec.Params) : Convergence (fixedSpaceSpec q.E q.Ω)
      (fun (d, L, R, σ, ε, _) _ => budget { q with d := d, L := L, R := R, σ := σ, ε := ε } 0) := by
    apply convergence_of_coordinates q.E q.Ω
      (fun d L R σ ε => budget { q with d := d, L := L, R := R, σ := σ, ε := ε } 0)
    intro d
    exact two_point_convergence_coordinates d q.Ω
  refine ⟨fun q => (h q).choose (q.d, q.L, q.R, q.σ, q.ε, q.x0),
    ?_,
    fun _ _ => trivial⟩
  intro q hp f O ho
  exact (h q).choose_spec.1 (q.d, q.L, q.R, q.σ, q.ε, q.x0) hp f O ho

end OracleTemplate.ZerothOrder.AcceleratedTwoPointZerothOrderConvex
