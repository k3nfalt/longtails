import LongTails.Setups.SpikedSubGaussianConvex
import LongTails.Proofs.SpikedSoftCutGuarantee
import LongTails.Proofs.SpikedSoftCutBudget

namespace LongTails.Theorems.SpikedSubGaussianSoftCutConvex

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCutMethod
open LongTails.Proofs.SpikedSoftCutGuarantee
open LongTails.Proofs.SpikedSoftCutBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2^51*((q.m+1 : ℝ)+(q.vTop+q.m*q.vRest)*q.R^2/q.ε^2)*(1+Real.log (16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε)))^5⌉₊

theorem result : OracleTemplate.Convergence LongTails.Setups.SpikedSubGaussianConvex.spec budget := by
  refine ⟨algorithm,?_,fun _ _ => trivial⟩
  intro q hq f O hadm
  obtain ⟨hG,hR,hrest,horder,hε⟩ := hq
  exact successful_tuned q ⟨hG,hR,hrest,horder,hε⟩ (budget q 0)
    (tuned_budget_suffices q hG hR hε hrest horder) f O hadm

end LongTails.Theorems.SpikedSubGaussianSoftCutConvex
