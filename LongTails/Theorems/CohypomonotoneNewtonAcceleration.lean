import LongTails.Setups.CohypomonotoneNewton
import LongTails.Proofs.CohypomonotoneNewtonCost

namespace LongTails.Theorems.CohypomonotoneNewtonAcceleration

open OracleTemplate
open LongTails.Setups.CohypomonotoneNewton
open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonRun
open LongTails.Proofs.CohypomonotoneNewtonCost
open OracleTemplate.ComponentEnvelope (Program)

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈100000000000000 * ((1 + p.ρ * p.H * p.R) ^ 2 + (1 + p.H * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ)) * (1 + Real.log (2 + p.ρ * p.H * p.R + p.H * p.R ^ 2 / p.ε)) ^ 2⌉₊

theorem result : Convergence LongTails.Setups.CohypomonotoneNewton.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨hH, hρ, hR, hε⟩ F oracle ⟨J, hanswer, hF, hJ, hco, root, hzero, hroot⟩
  have hwork := (plan_work p F J root hH hρ hR hε hF hJ hco hzero hroot).trans
    (public_work_bound p hH hρ hR hε)
  have hcostReal : (Program.cost (fun x => (F x, J x)) (plan p) : ℝ) ≤ (budget p 0 : ℝ) :=
    hwork.trans (Nat.le_ceil _)
  have hcost : Program.cost (fun x => (F x, J x)) (plan p) ≤ budget p 0 := by exact_mod_cast hcostReal
  have haccuracy := plan_accuracy p F J root hH hρ hR hε hF hJ hco hzero hroot
  apply Filter.Eventually.of_forall
  rintro ⟨⟨⟩, ξ⟩
  change ‖F (output p oracle (budget p 0) ξ)‖ ≤ p.ε
  rw [LongTails.Proofs.CohypomonotoneNewtonExecution.execute_of_cost_le p (fun x => (F x, J x)) oracle
    (fun history x seed => hanswer history seed x) (budget p 0) ξ hcost]
  exact haccuracy

end LongTails.Theorems.CohypomonotoneNewtonAcceleration
