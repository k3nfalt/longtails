import LongTails.Setups.ClusteredConvolutionalPerceptron
import LongTails.Algorithms.ClusteredConvolutionalPerceptron
import LongTails.Proofs.ClusteredConvolutionalPerceptronConvergence

namespace OracleTemplate.ClusteredConvolutionalPerceptron

open LongTails.Setups.ClusteredConvolutionalPerceptron
open LongTails.Algorithms.ClusteredConvolutionalPerceptron
open LongTails.Proofs.ClusteredConvolutionalPerceptronConvergence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (p.samples + 1) * (⌈128 * p.upper ^ 2 / p.lower ^ 2 * Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)⌉₊ + 3)

theorem result : Convergence LongTails.Setups.ClusteredConvolutionalPerceptron.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp D O hadm
    obtain ⟨⟨G⟩, hlaw⟩ := hadm
    change ∀ ω : (algorithm p).Seed × ((k : ℕ) → O.Seed k),
      Separates D (output p O (budget p ⟨0, by change 0 < 1; omega⟩) ω.1 ω.2)
    intro ω
    rw [output_eq_iterate p D O hlaw]
    exact tuned_iterate p hp G ω.1
  · intro p hp
    trivial

end OracleTemplate.ClusteredConvolutionalPerceptron
