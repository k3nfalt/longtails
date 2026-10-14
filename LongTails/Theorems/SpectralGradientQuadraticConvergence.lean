import LongTails.Setups.MinimizerRegularHessian
import LongTails.Proofs.Execution
import LongTails.Proofs.SpectralGradientConvergence

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 * p.L / p.μ) * Real.log (2 + 8 * ((Module.finrank ℝ p.E : ℝ) + 1) ^ 2 * (4 * p.L ^ 2 / p.μ ^ 2) ^ Module.finrank ℝ p.E * p.M * p.L * p.R / p.μ ^ 2)⌉₊ + 2 * Module.finrank ℝ p.E * ⌈Real.log (1 + Real.log (1 + p.L ^ 2 * p.R ^ 2 / (p.μ * p.ε))) / Real.log 2⌉₊

theorem result : Convergence LongTails.Setups.MinimizerRegularHessian.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => spectralGradient p (warmupCount p), ?_, fun _ _ => trivial⟩
  intro p hp f O h
  rcases hp with ⟨hμ, hμL, hM, hR, hε⟩
  rcases h with ⟨hf, hg, hs, hlip, hO, u, hmin, hinit, hH⟩
  have hcost : budget p 0 = warmupCount p + windowCount p * (2 * Module.finrank ℝ p.E) :=
    (expanded_cost p).symm
  have hacc := spectral_accuracy p hμ hμL hM hR hε hf hg hs hlip u hmin hinit hH
  refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨⟨⟩, ξ⟩
    change f (execute O (spectralGradient p (warmupCount p)) (fun _ => (budget p 0)) () ξ) - f u ≤ p.ε
    erw [hcost, complete_execution p (gradient f) (warmupCount p) (windowCount p) O hO]
    exact hacc

end OracleTemplate.SpectralGradient
