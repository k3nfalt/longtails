import LongTails.Setups.ManySampleConvolutionalPerceptron
import LongTails.Algorithms.ManySampleConvolutionalPerceptron
import LongTails.Proofs.ManySampleConvolutionalPerceptronConvergence

namespace OracleTemplate.ManySampleConvolutionalPerceptron

open LongTails.Setups.ManySampleConvolutionalPerceptron
open LongTails.Algorithms.ManySampleConvolutionalPerceptron
open LongTails.Proofs.ManySampleConvolutionalPerceptronConvergence
open LongTails.Proofs.ManySampleConvolutionalPerceptronExecution

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈34359738368 * (p.upper / p.lower) ^ 4 * (Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)) ^ 2 * (p.samples + 1 + (p.upper / p.lower) * Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)) / p.derivativeMargin ^ 2⌉₊

theorem result : Convergence LongTails.Setups.ManySampleConvolutionalPerceptron.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp D O hadm
    obtain ⟨⟨G⟩, hlaw⟩ := hadm
    change ∀ ω : (algorithm p).Seed × ((k : ℕ) → O.Seed k),
      Separates D (output p O (budget p ⟨0, by change 0 < 1; omega⟩) ω.1 ω.2)
    intro ω
    rw [output_eq_iterate p D O hlaw]
    exact tuned_iterate p hp G (public_budget_suffices p hp)
  · intro p hp
    trivial

end OracleTemplate.ManySampleConvolutionalPerceptron
