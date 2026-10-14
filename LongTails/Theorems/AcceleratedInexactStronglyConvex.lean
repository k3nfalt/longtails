import LongTails.Setups.InexactGradientStronglyConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.InexactAcceleratedConvergence

namespace OracleTemplate.InexactGradient

open LongTails.Setups.InexactGradientStronglyConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(8 * Real.sqrt (p.L / (p.μ * (1 - p.α))) + 32 * p.α ^ 2 * p.L / (p.μ * (1 - p.α))) * Real.log (1 + 2 * p.L * p.R ^ 2 / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.InexactGradientStronglyConvex.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => inexactAccelerated p.L p.μ p.α p.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨hμ, hμL, hα0, hα1, -, -, hε, hδ⟩
  intro K hK
  rintro f O ⟨hg, hup, hsc, herr, xstar, hmin, hdist⟩
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨seed, ξ⟩
    exact execute_accuracy hμ hμL hα0 hα1 hε hδ hg hup hsc hmin hdist O herr seed ξ K hK

end OracleTemplate.InexactGradient
