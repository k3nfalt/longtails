import LongTails.Setups.FiniteScaleConvolutionalSgd
import LongTails.Proofs.FiniteScaleConvolutionalSgdRestarts

open MeasureTheory OracleTemplate

namespace LongTails.Theorems.FiniteScaleConvolutionalSgd

open LongTails.Setups.FiniteScaleConvolutionalSgd
open LongTails.Algorithms.FiniteScaleConvolutionalSgd
open LongTails.Proofs.FiniteScaleConvolutionalSgdGeometry
open LongTails.Proofs.FiniteScaleConvolutionalSgdTuning
open LongTails.Proofs.FiniteScaleConvolutionalSgdRestarts

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈100000000000000 * (p.input.count : ℝ) ^ 3 * (p.input.upper / p.input.lower) ^ 2 / p.input.derivativeMargin ^ 3 * Real.log (24000000 * p.input.upper ^ 2 / (p.input.derivativeMargin ^ 2 * p.input.contrast ^ 2)) * (1 + Real.log (1 / p.failure))⌉₊

theorem result : Convergence LongTails.Setups.FiniteScaleConvolutionalSgd.spec budget := by
  refine ⟨tunedAlgorithm, ?_, ?_⟩
  · intro p hp data O hO
    obtain ⟨⟨G⟩, hanswer⟩ := hO
    let M := ⌈Real.log (1 / p.failure)⌉₊ + 1
    have hprob := execution_failure_probability p hp data G O hanswer M (budget p ⟨0, by change 0 < 1; decide⟩)
      (total_budget_bound p hp)
    rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, hfailure, hfailure₁, _⟩
    have hconfidence : ENNReal.ofReal (1 / 4) ^ M ≤ ENNReal.ofReal p.failure := by
      rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      exact ENNReal.ofReal_le_ofReal (confidence_repetitions p.failure hfailure hfailure₁).1
    exact hprob.trans hconfidence
  · intro p hp
    exact algorithm_family p.input (stepSize p.input) (scale p.input) (period p.input)
      (parameter_bounds p hp).1 (initial_conditions p hp).1

end LongTails.Theorems.FiniteScaleConvolutionalSgd
