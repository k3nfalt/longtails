import LongTails.Setups.LocalStrongAiming
import LongTails.Proofs.Execution
import LongTails.Proofs.NearestAimingConvergence

namespace OracleTemplate.NearestAiming

open LongTails.Setups.LocalStrongAiming

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 * Real.sqrt (p.L / p.μ) * Real.log (1 + 2 * p.Δ / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.LocalStrongAiming.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => (certifiedNesterov p).val, ?_, fun p _ => (certifiedNesterov p.toPublic).property⟩
  intro p hp K hK f oracle hadmissible
  obtain ⟨horacle, hg, xstar, hmin, hgap, hlocal⟩ := hadmissible
  have hrate := nesterov_rate p hp f hg xstar hmin hgap hlocal (K)
  have haccuracy := hrate.trans (accuracy_budget p hp K hK)
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨seed, oracleSeed⟩
    change f (execute oracle (certifiedNesterov p.toPublic).val (fun _ => (K)) seed oracleSeed) -
      f xstar ≤ p.ε
    rw [execute_nesterov p.toPublic f oracle hg horacle]
    exact haccuracy

end OracleTemplate.NearestAiming
