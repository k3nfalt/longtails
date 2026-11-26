import LongTails.Setups.HighDimensionalBiasedNoiseNonconvex
import LongTails.Proofs.BiasedLowerBound
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.BiasedNoiseLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalBiasedNoiseNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let r := (1 - q.m) * q.ε ^ 2
  ⌊q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) / (2 ^ 60 * r)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalBiasedNoiseNonconvex.spec budget := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain ⟨π, sg, hsg, hπ⟩ := LongTails.Proofs.BiasedLowerBound.exists_failure_biased q hv A (b 0)
    (LongTails.Proofs.BiasedLowerBound.budget_le q hv (b 0) (hb 0))
  exact ⟨_, _, LongTails.Proofs.BiasedLowerAdmissible.admissibleB q hv π sg hsg, hπ⟩

end LongTails.Theorems.BiasedNoiseLowerBound
