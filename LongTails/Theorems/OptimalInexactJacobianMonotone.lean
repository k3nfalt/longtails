import LongTails.Setups.InexactJacobianMonotone
import LongTails.Proofs.InexactJacobianExecution
import LongTails.Proofs.InexactJacobianBudget

namespace LongTails.Theorems.OptimalInexactJacobianMonotone

open OracleTemplate MeasureTheory
open LongTails.Setups.InexactJacobianMonotone
open LongTails.Algorithms.NestedAnchoredInexactJacobian
open LongTails.Proofs.InexactJacobianInner
open LongTails.Proofs.InexactJacobianOuter
open LongTails.Proofs.InexactJacobianExecution
open LongTails.Proofs.InexactJacobianBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈4194304 * (1 + (p.M * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ) + p.δ * p.R / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.InexactJacobianMonotone.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨hM, hδ, hR, hε⟩ F O ⟨hd, hm, hL, ⟨xs, hzero, hx⟩, hO⟩
  have hreg : Regular F := ⟨fun x => (hd x).hasFDerivAt, hm, hL⟩
  apply Filter.Eventually.of_forall
  rintro ⟨seed, ξ⟩
  cases seed
  change ‖F (output O (budget p 0) ξ)‖ ≤ p.ε
  let J := historyJacobian O ξ
  have hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ := historyJacobian_error F O ξ hO
  have hB := public_budget_sufficient F hreg J hJ hM hδ hR hε xs hzero hx
  erw [execute_eq_outer F O ξ (fun history x seed => (hO history x seed).1)
    (succeeds F hreg J hJ hM hδ hR hε) hB]
  exact final_accuracy F hreg J hJ hM hδ hR hε xs hzero hx

end LongTails.Theorems.OptimalInexactJacobianMonotone
