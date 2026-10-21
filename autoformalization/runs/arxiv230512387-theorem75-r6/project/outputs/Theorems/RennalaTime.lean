import outputs.Setups.RennalaTime
import outputs.Proofs.SingleOracleCounted
import outputs.Proofs.RennalaConvergence

namespace OracleTemplate.Rennala

noncomputable def budget : outputs.Setups.RennalaTime.spec.Params → Fin outputs.Setups.RennalaTime.spec.numOracles → ℕ := fun p _ => p.n + 2 * ⌈24 * p.L * p.Delta / p.eps⌉₊ * (max ⌈p.v / p.eps⌉₊ 1 + p.n)

theorem result : Convergence outputs.Setups.RennalaTime.spec budget := by
  classical
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp I O hO
    have hB : (publicInput p).horizon * (batchSize p.v p.eps + p.n) ≤ budget p 0 := by
      have hh : ⌊24 * p.L * p.Delta / p.eps⌋₊ ≤ ⌈24 * p.L * p.Delta / p.eps⌉₊ := Nat.floor_le_ceil _
      have hb : ⌊24 * p.L * p.Delta / p.eps⌋₊ * (batchSize p.v p.eps + p.n) ≤
          ⌈24 * p.L * p.Delta / p.eps⌉₊ * (batchSize p.v p.eps + p.n) := Nat.mul_le_mul_right _ hh
      change ⌊24 * p.L * p.Delta / p.eps⌋₊ * (batchSize p.v p.eps + p.n) ≤
        p.n + 2 * ⌈24 * p.L * p.Delta / p.eps⌉₊ * (batchSize p.v p.eps + p.n)
      calc
        _ ≤ ⌈24 * p.L * p.Delta / p.eps⌉₊ * (batchSize p.v p.eps + p.n) := hb
        _ ≤ p.n + 2 * (⌈24 * p.L * p.Delta / p.eps⌉₊ * (batchSize p.v p.eps + p.n)) := by omega
        _ = _ := by ring
    exact execution_success p hp I O hO (budget p 0) hB
  · intro p hp
    rfl


end OracleTemplate.Rennala
