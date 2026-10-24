import LongTails.Setups.NoisyBatchQuadraticPerceptron
import LongTails.Algorithms.NoisyBatchQuadraticPerceptron
import LongTails.Proofs.NoisyBatchQuadraticPerceptronConvergence

namespace OracleTemplate.NoisyBatchQuadraticPerceptronGlobal
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Algorithms.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronConvergence
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈100000 * (p.input.count : ℝ) * (((p.input.count : ℝ) + 1) ^ 2 * (p.input.radius / p.input.margin) ^ 2 + ‖p.input.start‖ ^ 2 / (p.input.noiseScale ^ 2 * (p.input.dimension + 1))) * (2 / p.failure) ^ (5 * Real.exp (25000 * (p.input.dimension + 1 : ℝ) ^ 2 * (((p.input.count : ℝ) + 1) ^ 2 * (p.input.radius / p.input.margin) ^ 2) ^ 2)) / p.failure⌉₊
theorem result : Convergence LongTails.Setups.NoisyBatchQuadraticPerceptron.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p ⟨0, by change 0 < 1; omega⟩)
  refine ⟨(fun P => algorithm P (P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))), ?_, ?_⟩
  · rintro p ⟨hδ, hδR, hσ, hρ, hρ1, h⟩ L hL data O ⟨⟨u, hu, hdata⟩, hO⟩
    dsimp only [spec] at *
    exact execution_failure_bound p.input data
      (p.input.margin / (8 * ((p.input.count : ℝ) + 1) * p.input.radius ^ 2)) p.failure O
      (fun history q ξ => hO history (0, q) ξ) h u L hσ hδ hδR hρ hρ1
      (fun i => (hdata i).1) hu (fun i => (hdata i).2.trans_eq (real_inner_comm u (data i)).symm) rfl hL
  · intro p hp
    apply algorithm_family
    have hδ := hp.1
    have hR : 0 < p.input.radius := lt_of_lt_of_le hδ hp.2.1
    positivity
end OracleTemplate.NoisyBatchQuadraticPerceptronGlobal
