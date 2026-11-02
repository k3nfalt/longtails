import LongTails.Setups.KernelConvolutionalPerceptron
import LongTails.Algorithms.KernelConvolutionalPerceptron
import LongTails.Proofs.KernelPerceptronParameters

namespace OracleTemplate.KernelConvolutionalPerceptronAcceleration

open LongTails.Setups.KernelConvolutionalPerceptron
open LongTails.Algorithms.KernelConvolutionalPerceptron
open LongTails.Proofs.KernelPerceptronParameters

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (p.samples + 1) * ⌈200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 * Real.log (128 * p.kernel * p.upper ^ 2 / (p.derivativeMargin * p.contrast) ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.KernelConvolutionalPerceptron.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp D O hadm
    obtain ⟨⟨G⟩, hlaw⟩ := hadm
    change ∀ ω : (algorithm p).Seed × ((k : ℕ) → O.Seed k),
      Separates D (output p O (budget p ⟨0, by change 0 < 1; omega⟩) ω.1 ω.2)
    intro ω
    rw [LongTails.Proofs.KernelPerceptronExecution.output_eq_iterate p D O hlaw]
    exact budget_separates p hp G
  · intro p hp
    obtain ⟨_, hk, hg, hgR, _, _, hκ, _, _⟩ := hp
    exact family_algorithm p hκ (by omega) (lt_of_lt_of_le hg hgR)

end OracleTemplate.KernelConvolutionalPerceptronAcceleration
