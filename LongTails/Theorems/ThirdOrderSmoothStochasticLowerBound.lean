import LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex
import LongTails.Proofs.ThirdOrderLowerBound
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.ThirdOrderSmoothStochasticLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊q.Δ * min (q.L₁ / q.ε) (min (Real.sqrt (q.L₂ / q.ε)) ((q.L₃ / q.ε) ^ (1 / 3 : ℝ))) * (1 + q.σ ^ 2 / q.ε ^ 2) / (2 ^ 174 * q.ε)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex.spec budget := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain ⟨π, hπ⟩ := LongTails.Proofs.ThirdOrderLowerBound.exists_failure q hv A (b 0) (hb 0)
  exact ⟨_, _, LongTails.Proofs.ThirdOrderLowerAssembly.hard_admissible q hv π, hπ⟩

end LongTails.Theorems.ThirdOrderSmoothStochasticLowerBound
