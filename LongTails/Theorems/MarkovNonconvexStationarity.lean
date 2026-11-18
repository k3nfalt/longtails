import LongTails.Setups.MarkovSmoothNonconvex
import LongTails.Proofs.MarkovClippedConvergence

namespace LongTails.Theorems.MarkovNonconvexStationarity

open OracleTemplate LongTails.Setups.MarkovSmoothNonconvex LongTails.Algorithms.MarkovClippedSgd

noncomputable def budget : (let S := LongTails.Setups.MarkovSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (⌈32768 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4⌉₊ + 1) * ⌈p.τ * Real.log (8192 * p.σ ^ 2 / p.ε ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.MarkovSmoothNonconvex.spec budget :=
  ⟨algorithm, fun p hv f O ha => LongTails.Proofs.MarkovClippedConvergence.accuracy p hv f O ha,
   fun _ _ => trivial⟩

end LongTails.Theorems.MarkovNonconvexStationarity
