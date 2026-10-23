import LongTails.Setups.FiniteSumWeakMintyInclusion
import LongTails.Proofs.VarianceReducedWeakMintyConvergence
import LongTails.Proofs.VarianceReducedWeakMintyBudget

open MeasureTheory

namespace OracleTemplate.VarianceReducedWeakMintyInclusion

open LongTails.Setups.FiniteSumWeakMintyInclusion
open VarianceReducedWeakMinty

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈4398046511104 * Real.log (2 / (1 - p.ρ * p.L)) / (1 - p.ρ * p.L) * min (p.n * (1 + p.L ^ 2 * p.R ^ 2 / ((1 - p.ρ * p.L) ^ 2 * p.ε ^ 2))) ((p.n + p.Λ ^ 2 / p.L ^ 2 + (Real.sqrt p.n * p.Λ * p.L + p.Λ ^ 2) * p.R ^ 2 / ((1 - p.ρ * p.L) ^ 2 * p.ε ^ 2)) / (1 - p.ρ * p.L) ^ 3)⌉₊

theorem result : Convergence LongTails.Setups.FiniteSumWeakMintyInclusion.spec budget := by
  refine ⟨tunedAlgorithm, ?_, fun _ _ => trivial⟩
  intro p hp I oracle hadm
  let : NeZero p.n := ⟨Nat.ne_of_gt hp.1⟩
  have hK : (stepCost (useExact p) p.n (batchSize p) (innerLength p) * epochLength p + p.n) *
      epochCount p ≤ budget p 0 := by
    simpa only [budget, margin, exactWork, batchWork, mul_div_assoc] using total_cost p hp
  have ha : tunedAlgorithm p = algorithm (useExact p) ((2 - margin p) / (2 * p.L))
      (margin p / (2 - margin p)) (epochLength p : ℝ)⁻¹ p.x0
      (batchSize p) (innerLength p) (epochLength p) (epochCount p) := by
    unfold tunedAlgorithm
    rw [dite_eq_left hp.1]
  let P := fun a : Algorithm (spec.Query p) (spec.Reply p) (spec.Output p) =>
    spec.successful p I
      (fun seed : a.Seed × ((k : ℕ) → oracle.Seed k) =>
        execute oracle a (budget p) seed.1 seed.2)
      ⟨(a.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩
  exact (congrArg P ha).mpr (algorithm_success p hp I oracle hadm hK)

end OracleTemplate.VarianceReducedWeakMintyInclusion
