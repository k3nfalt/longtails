import LongTails.Setups.TwoSidedConvolutionalPerceptron
import LongTails.Algorithms.TwoSidedConvolutionalPerceptron
import LongTails.Proofs.TwoSidedPerceptronParameters

namespace OracleTemplate.TwoSidedConvolutionalPerceptron

open LongTails.Setups.TwoSidedConvolutionalPerceptron
open LongTails.Algorithms.TwoSidedConvolutionalPerceptron
open LongTails.Proofs.TwoSidedPerceptronParameters

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (p.samples + 1) * ⌈2 ^ 24 * (p.upper / p.lower) ^ 2 * (1 + Real.log (1 + p.lower / p.contrast)) / p.margin ^ 3⌉₊

theorem result : Convergence LongTails.Setups.TwoSidedConvolutionalPerceptron.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp D O hadm
    obtain ⟨⟨G⟩, hlaw⟩ := hadm
    change ∀ ω : (algorithm p).Seed × ((k : ℕ) → O.Seed k),
      Separates D (output p O (budget p ⟨0, by change 0 < 1; omega⟩) ω.1 ω.2)
    intro ω
    rw [LongTails.Proofs.TwoSidedPerceptronExecution.output_eq_iterate p D O hlaw]
    exact iterate_budget_separates p hp G
  · intro p _
    exact ⟨ScanState.point, ScanState.cursor, stepSize p, stepSize_pos_of_valid p ‹_›,
      fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end OracleTemplate.TwoSidedConvolutionalPerceptron
