import LongTails.Setups.HighDimensionalVarianceOnlySecondOrder
import LongTails.Proofs.EscapeChainLowerBound
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.VarianceOnlySospLowerBound

open OracleTemplate

noncomputable def budget :
    (let S := LongTails.Setups.HighDimensionalVarianceOnlySecondOrder.spec;
      S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let D := Real.sqrt q.ρ * q.Δ / (q.ε * Real.sqrt q.ε)
  ⌊q.d * (q.σ / q.ε) ^ 2 * D / 2 ^ 703⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalVarianceOnlySecondOrder.spec budget := by
  intro q hv A hA b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain ⟨θ, hθ⟩ := LongTails.Proofs.EscapeChainLowerBound.exists_failure q hv A hA (b 0) (hb 0)
  exact ⟨_, _, LongTails.Proofs.EscapeChainLowerBound.hard_admissible q hv (LongTails.Proofs.EscapeChainLowerBound.ctx q hv (b 0) (hb 0)) rfl rfl rfl rfl θ, hθ⟩

end LongTails.Theorems.VarianceOnlySospLowerBound
