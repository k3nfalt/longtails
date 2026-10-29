import LongTails.Setups.CovarianceBoundedConvex
import LongTails.Proofs.CovarianceSoftCutGuarantee

namespace LongTails.Theorems.CovarianceSoftCutConvex

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCutMethod
open LongTails.Proofs.CovarianceSoftCutGuarantee
open LongTails.Proofs.CovarianceSoftCutBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2^32*((q.d : ℝ)+q.σ^2*q.R^2/q.ε^2)*(1+Real.log (16*(q.d : ℝ)*(1+q.L*q.R/q.ε)))^5⌉₊

theorem result : OracleTemplate.Convergence LongTails.Setups.CovarianceBoundedConvex.spec budget := by
  refine ⟨tunedMethod, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  obtain ⟨hd, hL, hR, hσ, hε⟩ := hq
  exact successful_tuned q ⟨hd, hL, hR, hσ, hε⟩ (budget q 0)
    (fun hsmall => tuned_work_le_public_budget q hd hL hR hε hsmall) f O hadm

end LongTails.Theorems.CovarianceSoftCutConvex
