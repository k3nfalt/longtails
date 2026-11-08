import LongTails.Setups.BirchNonEuclideanComposition
import LongTails.Proofs.BirchNonEuclideanComposition

namespace LongTails.Theorems.BirchNonEuclideanComposition

open OracleTemplate
open LongTails.Algorithms.BirchNonEuclideanComposition

noncomputable def budget : (let S := LongTails.Setups.BirchNonEuclideanComposition.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(5 + 528 * p.L * p.Δ / p.ε) * p.slots * p.credits + (32 + 1920 * p.L * p.Δ / p.ε) * p.κ * p.σ ^ 2 / p.ε⌉₊

theorem result : Convergence LongTails.Setups.BirchNonEuclideanComposition.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp I O hI
  exact LongTails.Proofs.BirchNonEuclideanComposition.execute_success p hp I O hI

end LongTails.Theorems.BirchNonEuclideanComposition
