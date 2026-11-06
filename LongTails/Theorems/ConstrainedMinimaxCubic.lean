import LongTails.Setups.ConstrainedMinimaxSecondOrder
import LongTails.Proofs.ConstrainedSaddleBudget

namespace LongTails.Theorems.ConstrainedMinimaxCubic

open LongTails.Setups.ConstrainedMinimaxSecondOrder
open LongTails.Algorithms.ConstrainedSaddleCubic
open LongTails.Proofs.ConstrainedMinimaxValue
open LongTails.Proofs.ConstrainedSaddleInner
open LongTails.Proofs.ConstrainedSaddleExecution
open LongTails.Proofs.ConstrainedSaddleBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 4 * (1 + ⌈16 * p.L / p.μ * Real.log (1 + 32 * p.ρ * p.B / p.μ ^ 2)⌉₊ + (2 + ⌈384 * p.Δ * Real.sqrt p.ρ * (p.L / p.μ) ^ (3 / 4 : ℝ) / (p.ε * Real.sqrt p.ε)⌉₊ + ⌈2048 * p.ρ * Real.sqrt (p.L / p.μ) * p.Δ / (p.μ * p.ε) + 8 * Real.sqrt (p.ρ * p.ε) / p.μ⌉₊) * (2 + ⌈2 * Real.log (33 + 512 * p.L * p.μ / (p.ρ * p.ε))⌉₊))

theorem result : OracleTemplate.Convergence LongTails.Setups.ConstrainedMinimaxSecondOrder.spec budget := by
  refine ⟨method, ?_, ?_⟩
  · intro p hv f O hO
    refine ⟨value_differentiable hO.1.toRegularity hv, Filter.Eventually.of_forall ?_⟩
    rintro ⟨seed, ω⟩
    cases seed
    change ‖gradient (value f) (output p O (budget p 0) ω)‖ ≤ p.ε
    have hK := explicit_plan_cost hO.1 hv
    rw [execute_method (p := p) O (jet f) hO.2 (budget p 0) hK ω]
    exact full_plan_accuracy hO.1 hv
  · intro p hv
    trivial

end LongTails.Theorems.ConstrainedMinimaxCubic
