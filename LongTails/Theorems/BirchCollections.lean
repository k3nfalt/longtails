import LongTails.Setups.BirchCollections
import LongTails.Proofs.BirchCollectionSuccess

namespace LongTails.Theorems.BirchCollections

open OracleTemplate
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Proofs.BirchCollectionEvaluation (compiled)
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionSuccess

noncomputable def budget : (let S := LongTails.Setups.BirchCollections.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.controls.initialization + p.controls.waste + ⌈(1 + (⌈32 * p.controls.massRatio * p.κ * p.σ ^ 2 / p.ε⌉₊ : ℝ)) * p.controls.amplification * ((1 + (⌈240 * p.L * p.Δ / (p.controls.lowerMass * p.ε)⌉₊ : ℝ)) * p.controls.upperMass)⌉₊

theorem result : Convergence LongTails.Setups.BirchCollections.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp I O hI
  have he : ValidFrom p.workers {} p.events := hp.2.2.2.2.2.2.2.2.1
  have hs : Structural (compiled p).trace p.ordering p.controls (horizon p) (batchSize p) := by
    simpa only [compiled, compile_trace] using hp.2.2.2.2.2.2.2.2.2
  have hQ : (program p).oracleCalls ≤ budget p 0 := by
    simpa only [budget, horizon, batchSize, Nat.cast_add, Nat.cast_one] using
      calls_bound p he (horizon p) (batchSize p) hs
  have hb : budget p = fun _ => budget p 0 := by
    rfl
  rw [hb]
  exact execute_success p hp (budget p 0) hQ I O hI

end LongTails.Theorems.BirchCollections
