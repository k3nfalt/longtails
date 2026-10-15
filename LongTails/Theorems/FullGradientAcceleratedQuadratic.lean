import LongTails.Setups.QuadraticFiniteSum
import LongTails.Proofs.FullGradientQuadraticExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace OracleTemplate.FullGradientAccelerated

open LongTails.Setups.QuadraticFiniteSum

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * ⌈8 * Real.sqrt (p.L / p.μ) * Real.log (1 + 2 * p.L * p.R ^ 2 / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.QuadraticFiniteSum.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p hp f O ⟨hs, hA, hc, hanswer, u, hu, hR, hG⟩
  let K := ⌈8 * Real.sqrt (p.L / p.μ) * Real.log (1 + 2 * p.L * p.R ^ 2 / p.ε)⌉₊
  have hexec (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
      execute O (algorithm p) (fun _ => budget p 0) seed ξ = output p (averageGradient f) K :=
    execute_algorithm p f O hanswer K seed ξ
  change Measurable _ ∧ ∃ xstar, IsMinOn (objective f) Set.univ xstar ∧ _ ∧ _
  simp only [hexec]
  refine ⟨measurable_const, u,
    QuadraticFiniteSum.stationary_minimizer f hp.2.1.le hs hc hu, integrable_const _, ?_⟩
  simpa using output_accuracy p hp f hs hA hc u hu hR K le_rfl

end OracleTemplate.FullGradientAccelerated
