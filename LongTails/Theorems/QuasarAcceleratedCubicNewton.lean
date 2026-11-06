import LongTails.Setups.QuasarConvexHessianLipschitz
import LongTails.Proofs.QuasarCubicConvergence

namespace LongTails.Theorems.QuasarAcceleratedCubicNewton

open OracleTemplate
open LongTails.Setups.QuasarConvexHessianLipschitz
open LongTails.Algorithms.QuasarCubicNewton
open LongTails.Proofs.QuasarCubicConvergence
open LongTails.Proofs.QuasarCubicExecution
open OracleTemplate.ComponentEnvelope (Program)

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(8388608 * p.H * p.R ^ 3 / (p.γ ^ 4 * p.ε)) ^ (3 / 8 : ℝ)⌉₊ * (Nat.log2 ⌈27 * (8388608 * p.H * p.R ^ 3 / (p.γ ^ 4 * p.ε) + 1) ^ 2 * (p.L₀ / (p.H * p.R) + 32768) / p.γ ^ 2⌉₊ + 3) + 1

theorem result : Convergence LongTails.Setups.QuasarConvexHessianLipschitz.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p hp f oracle ⟨hC2, hLip, hA0, ⟨xstar, hQ, hR⟩, hanswer⟩
  have hyp := hyp_of_admissible hp hC2 hLip hA0 hQ hR
  have hcost : Program.cost (reply f) (plan p) ≤ budget p 0 := by
    have h := plan_cost p (reply f)
    have e : iterations p * (depth p + 2) + 1 = budget p 0 := by
      simp only [budget, iterations, depth]
    omega
  refine ⟨xstar, hQ.1, ?_⟩
  apply Filter.Eventually.of_forall
  rintro ⟨⟨⟩, ξ⟩
  change f (execute oracle (algorithm p) (fun _ => budget p 0) () ξ) - f xstar ≤ p.ε
  rw [execute_of_cost_le p (reply f) oracle (fun history query seed => hanswer history query seed)
    (budget p 0) ξ hcost, plan_eval]
  exact final_accuracy hyp

end LongTails.Theorems.QuasarAcceleratedCubicNewton
