import LongTails.Setups.HiddenPotentialStronglyMonotone
import LongTails.Proofs.HiddenPotentialExecution
import LongTails.Proofs.HiddenDecompositionLowerBound

namespace OracleTemplate.HiddenPotential

open LongTails.Setups.HiddenPotentialStronglyMonotone

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2097152 * Real.sqrt ((p.μ + p.s) * (p.L + p.μ + p.s)) / p.μ * Real.log (2 + p.s / p.μ) * Real.log (2 + p.R / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.HiddenPotentialStronglyMonotone.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => hiddenPotentialOutput p.μ p.L p.s p.R p.ε p.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨hμ, hL, hs, hR, hε⟩ F O ⟨hO, hstrong, ⟨φ, hg, hlip, hresidual⟩, xstar, hroot, hdist⟩
  refine ⟨xstar, hroot, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, ω⟩
  change ‖execute O (hiddenPotentialOutput p.μ p.L p.s p.R p.ε p.x0)
    (fun _ => budget p 0) () ω - xstar‖ ≤ p.ε
  exact execute_hidden_accuracy F φ O (fun k x seed => hO k seed x)
    hμ hL hs hR hε hg hlip hstrong hresidual p.x0 xstar hroot hdist (budget p 0) ω
    (total_calls_bound hμ hL hs hR hε)

end OracleTemplate.HiddenPotential
