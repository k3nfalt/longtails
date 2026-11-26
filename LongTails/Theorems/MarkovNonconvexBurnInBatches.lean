import LongTails.Setups.MarkovSmoothNonconvex
import LongTails.Proofs.MarkovNonconvexBurnInBatchesRate

namespace LongTails.Theorems.MarkovNonconvexBurnInBatches

open OracleTemplate LongTails.Proofs.MarkovNonconvexBurnInBatches

noncomputable def budget : (let S := LongTails.Setups.MarkovSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let T := p.L * p.Δ / p.ε ^ 2
  let V := p.σ ^ 2 / p.ε ^ 2
  ⌈8 * T⌉₊ * (⌈p.τ * Real.log 16⌉₊ + ⌈1024 * p.τ * V⌉₊)

theorem result : Convergence LongTails.Setups.MarkovSmoothNonconvex.spec budget :=
  ⟨algorithm, accuracy, fun _ _ => trivial⟩

end LongTails.Theorems.MarkovNonconvexBurnInBatches
