import LongTails.Setups.StronglyConvexDueling
import LongTails.Proofs.DuelingReferenceUpperBound

open OracleTemplate
open LongTails.Algorithms.DuelingReferenceDescent (algorithm output)
open LongTails.Proofs.DuelingReferenceTuning (sufficient_calls)
open LongTails.Proofs.DuelingReferenceUpperBound (successful)

namespace LongTails.Theorems.LocalReferenceDueling

noncomputable def budget : (let S := LongTails.Setups.StronglyConvexDueling.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈72 * (p.d : ℝ)^2 * (4/p.μ)^(2*p.k) * (max 1 (8*p.G/p.r))^(4*p.k+2) / (p.c^2*p.μ*p.ε) + 10368 * ((p.d : ℝ)*p.M*p.L)^2 * (4/p.μ)^(4*p.k) * (max 1 (8*p.G/p.r))^(8*p.k) / (p.c^2*p.μ*p.ε)^2⌉₊

theorem result : Convergence LongTails.Setups.StronglyConvexDueling.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hO
  exact successful hp (budget p 0) (sufficient_calls hp (Nat.le_ceil _)) f O hO

end LongTails.Theorems.LocalReferenceDueling
