import LongTails.Setups.WeakMintySecondOrderExpected
import LongTails.Proofs.SecondOrderMintyUpper

namespace OracleTemplate.WeakMintyHybrid.SecondOrderWeakMintyUpperBound

open LongTails.Setups.WeakMintySecondOrderExpected

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 27 * (1 + min (q.L₂ * q.R ^ 2 / q.ε) (q.L₁ ^ 2 * q.R ^ 2 / q.ε ^ 2))⌉₊

theorem result : Convergence LongTails.Setups.WeakMintySecondOrderExpected.spec budget := by
  refine ⟨fun p => hybrid p.L₁ p.L₂ p.ρ p.ε p.x0, ?_, fun _ _ => trivial⟩
  intro q hq F oracle hadm
  exact upper_success q hq F oracle hadm

end OracleTemplate.WeakMintyHybrid.SecondOrderWeakMintyUpperBound
