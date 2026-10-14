import LongTails.Setups.RelativeErrorSmoothConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.DampedAccelerated

namespace OracleTemplate.RelativeErrorConvex

open LongTails.Setups.RelativeErrorSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈7 * Real.sqrt (p.L * p.R ^ 2 / ((1 - p.α) * p.ε)) + 11 * p.α ^ 2 * p.L * p.R ^ 2 / ((1 - p.α) * p.ε)⌉₊

theorem result : Convergence LongTails.Setups.RelativeErrorSmoothConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => dampedAccelerated p.L (damping p.α (budget p 0)) p.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨hL, hα0, hα1, -, hε⟩

  rintro f O ⟨-, hcv, hup, herr, xstar, hmin, hdist⟩
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨seed, ξ⟩
    exact execute_accuracy hL hα0 hα1 hε hcv hup hmin hdist O herr (budget p 0)
      (Nat.le_ceil _) seed ξ

end OracleTemplate.RelativeErrorConvex
