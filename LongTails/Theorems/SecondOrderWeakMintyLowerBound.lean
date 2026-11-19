import LongTails.TemplateLowerBound
import LongTails.Setups.HighDimensionalWeakMintySecondOrder
import LongTails.Proofs.SecondOrderMintyLowerBound

namespace LongTails.Theorems.SecondOrderWeakMintyLowerBound

open OracleTemplate LongTails.Proofs.SecondOrderMintyLowerBound
open LongTails.Proofs.SecondOrderMintyLowerBudget

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalWeakMintySecondOrder.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊min (q.L₂ * q.R ^ 2 / q.ε) (q.L₁ ^ 2 * q.R ^ 2 / q.ε ^ 2) / 2 ^ 15⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalWeakMintySecondOrder.spec budget := by
  intro q hq A _ b hb
  obtain ⟨hL₁, hL₂, hρ, -, hR, hε, hM, hd⟩ := hq
  obtain ⟨hk, hn1, hn2, hn3⟩ := lower_parameters rfl hε hM (b 0) (hb 0)
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact exists_failure q hL₁ hL₂ hρ hR hε _ (b 0) hk hn1 hn2 (hn3.trans hd) A

end LongTails.Theorems.SecondOrderWeakMintyLowerBound
