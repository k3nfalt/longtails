import LongTails.Setups.CyclicFullWidthPerceptron
import LongTails.Algorithms.CyclicFullWidthPerceptron
import LongTails.Proofs.CyclicPerceptronScanner

namespace OracleTemplate.CyclicFullWidthPerceptronAcceleration

open LongTails.Setups.CyclicFullWidthPerceptron
open LongTails.Algorithms.CyclicFullWidthPerceptron
open LongTails.Proofs.CyclicPerceptronExecution LongTails.Proofs.CyclicPerceptronScanner

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (p.count + 1) * ⌈256 / p.κ ^ 4⌉₊

theorem result : Convergence LongTails.Setups.CyclicFullWidthPerceptron.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp D oracle ho
    change ∀ ω : Unit × ((k : ℕ) → oracle.Seed k),
      Separates p D (execute oracle (algorithm p) (budget p) ω.1 ω.2)
    rintro ⟨seed, ξ⟩
    cases seed
    change Separates p D (output p oracle ((p.count + 1) * ⌈256 / p.κ ^ 4⌉₊) ξ)
    rw [output_eq_iterate p D oracle ho.2]
    exact iterate_separates p D hp ho.1
  · intro p hp
    exact family_algorithm p hp.2.1

end OracleTemplate.CyclicFullWidthPerceptronAcceleration
