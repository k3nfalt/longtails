import LongTails.Setups.RadiusCompositeGeneralizedSmooth
import LongTails.Proofs.CompositeAdaptiveCompletion

namespace OracleTemplate.RadiusCompositeAccelerated

open LongTails.Setups.RadiusCompositeGeneralizedSmooth
open LongTails.Algorithms.RadiusCompositeAccelerated
open OracleTemplate.CompositeAdaptive

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈32768 * ((1 + q.L1 * q.R) ^ (4 / 3 : ℝ) + Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε)) * Real.log (128 * (1 + q.L1 * q.R + (q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε)) ^ 2⌉₊

theorem result : Convergence LongTails.Setups.RadiusCompositeGeneralizedSmooth.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro q hq I oracle hI
  obtain ⟨xs, h⟩ := conditions_of_admissible q I oracle hq hI
  have hB : 32768 * rateFactor q * logFactor q ^ 2 ≤ (budget q 0 : ℝ) := Nat.le_ceil _
  have ha := padded_execution_accuracy h (budget q 0) hB
  refine ⟨xs, h.solution_mem, h.minimizer, Filter.Eventually.of_forall fun seed => ?_⟩
  change execute oracle (algorithm q.toPublic) (budget q) seed.1 seed.2 ∈ I.Q ∧
    objective I (execute oracle (algorithm q.toPublic) (budget q) seed.1 seed.2) - objective I xs ≤ q.ε
  have hb : budget q = fun _ => budget q 0 := rfl
  rw [hb, execute_canonical q.toPublic I oracle (admissible_answers q I oracle hI)]
  exact ha

end OracleTemplate.RadiusCompositeAccelerated
