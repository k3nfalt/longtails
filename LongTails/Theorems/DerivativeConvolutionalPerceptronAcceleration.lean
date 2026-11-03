import LongTails.Setups.DerivativeConvolutionalPerceptron
import LongTails.Algorithms.DerivativeConvolutionalPerceptron
import LongTails.Proofs.DerivativeConvolutionalPerceptronConvergence

namespace OracleTemplate.DerivativeConvolutionalPerceptron

open LongTails.Setups.DerivativeConvolutionalPerceptron
open LongTails.Algorithms.DerivativeConvolutionalPerceptron
open LongTails.Proofs.DerivativeConvolutionalPerceptronConvergence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (p.samples + 1) * (⌈2 ^ 140 * p.upper ^ 10 / (p.derivativeMargin ^ 8 * p.lower ^ 10) * (1 + Real.log (p.upper / p.contrast))⌉₊ + 1)

theorem result : Convergence LongTails.Setups.DerivativeConvolutionalPerceptron.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp D O hadm
    obtain ⟨⟨G⟩, hlaw⟩ := hadm
    change ∀ ω : (algorithm p).Seed × ((k : ℕ) → O.Seed k),
      Separates D (output p O (budget p ⟨0, by change 0 < 1; omega⟩) ω.1 ω.2)
    intro ω
    exact output_separates p hp G O hlaw ω.1 ω.2
  · intro p hp
    trivial

end OracleTemplate.DerivativeConvolutionalPerceptron
