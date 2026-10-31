import LongTails.Setups.LinearPredictorBFGS
import LongTails.Algorithms.LinearPredictorBFGS
import LongTails.Proofs.BFGSExecution

namespace LongTails.Theorems.LinearPredictorBFGS

open OracleTemplate LongTails.Setups.LinearPredictorBFGS LongTails.Algorithms.LinearPredictorBFGS
open LongTails.Proofs.BFGSExecution

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈35 * (q.Lh / (q.μ * q.c1 * (1 - q.c2))) * Real.sqrt (q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε))⌉₊ + 1

theorem result : Convergence LongTails.Setups.LinearPredictorBFGS.spec budget := by
  refine ⟨method, ?_, fun p hp => ⟨p.L, hp.2.2.2.2.2.1, rfl⟩⟩
  intro q hq I O hO
  obtain ⟨hμ, hμL, hc1, hc12, hc2, hL, -, hε⟩ := hq
  obtain ⟨hconv, ⟨gradH, hgH, hlip⟩, hAL, ⟨xs, hmin, hdist, hqg⟩, hgrad, hls⟩ := hO
  refine ⟨xs, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  cases seed
  set K := ⌈35 * (q.Lh / (q.μ * q.c1 * (1 - q.c2))) *
    Real.sqrt (q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε))⌉₊
  change objective I (execute O (bfgs q.L q.x0) (fun _ => K + 1) () ξ) - objective I xs ≤ q.ε
  rw [execute_eq_run]
  exact accuracy q I O ξ hμ hμL hc1 hc12 hc2 hL hε hconv hgH hlip hAL hmin hdist hqg hgrad hls
    K (Nat.le_ceil _)

end LongTails.Theorems.LinearPredictorBFGS
