import LongTails.Setups.SimilarFiniteSumQuasar
import LongTails.Proofs.Execution
import LongTails.Proofs.CachedQuasarConvergence

namespace OracleTemplate.SimilarQuasar

open LongTails.Setups.SimilarFiniteSumQuasar

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (p.n + ⌈2 * Real.sqrt (p.L / p.μ) / p.γ * Real.log (1 + 1 / (48 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2) + p.γ * p.ε / (16 * (p.γ * p.ε + 2 * p.Δ))))⌉₊) * ⌈Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) / Real.log (1 / (2 * (48 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2) + p.γ * p.ε / (16 * (p.γ * p.ε + 2 * p.Δ)))))⌉₊

theorem result : Convergence LongTails.Setups.SimilarFiniteSumQuasar.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  let makeAlgorithm (p : Params) :=
    let θ := Real.sqrt (p.μ / p.L)
    let B := 2 * p.Δ / p.γ
    let ν := 48 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2)
    let r := ν + p.ε / (16 * (p.ε + B))
    let m := ⌈(2 / (p.γ * θ)) * Real.log (1 + 1 / r)⌉₊
    let S := ⌈Real.log (1 + B / p.ε) / Real.log (1 / (2 * r))⌉₊
    cachedQuasar p θ m S
  refine ⟨makeAlgorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O ho
  obtain ⟨u, hmin, hacc⟩ := execution_accuracy p f O hp ho
  refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  simpa only [execute, budget, ← budget_formula p hp.2.2.1.ne', makeAlgorithm, one_mul] using hacc seed ξ

end OracleTemplate.SimilarQuasar
