import LongTails.Setups.CompositeLipschitzHessian
import LongTails.Proofs.CompositeLazyCubicConvergence

namespace LongTails.Theorems.CompositeLazyCubicAcceleration

open OracleTemplate MeasureTheory
open LongTails.Setups.CompositeLipschitzHessian
open LongTails.Algorithms.CompositeLazyCubic
open LongTails.Proofs.CompositeLazyCubicConvergence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i = 1 then 4160 * (3 + Nat.log2 (p.m ^ 3 + 4)) * (3 + Nat.log2 (2 + ⌈(p.H * p.R ^ 3 / ((p.m : ℝ) ^ 3 * p.ε)) ^ (4 / 7 : ℝ)⌉₊)) * (1 + ⌈(p.H * p.R ^ 3 / ((p.m : ℝ) ^ 3 * p.ε)) ^ (2 / 7 : ℝ)⌉₊) else 2 ^ 39 * p.m * (3 + Nat.log2 (p.m ^ 3 + 4)) ^ 4 * (3 + Nat.log2 (2 + ⌈(p.H * p.R ^ 3 / ((p.m : ℝ) ^ 3 * p.ε)) ^ (4 / 7 : ℝ)⌉₊)) * (1 + ⌈(p.H * p.R ^ 3 / ((p.m : ℝ) ^ 3 * p.ε)) ^ (2 / 7 : ℝ)⌉₊)

theorem result : Convergence LongTails.Setups.CompositeLipschitzHessian.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp F O hF
    apply Filter.Eventually.of_forall
    rintro ⟨seed, ξ⟩
    apply execution_accuracy p hp F O hF (budget p) ?_ ?_ seed ξ
    · simpa only [budget, ite_true, scaledGap] using LongTails.Proofs.CompositeCurvatureParameters.total_hessians_bound p
    · intro i hi
      simpa only [budget, ite_eq_right hi, scaledGap] using LongTails.Proofs.CompositeCurvatureParameters.total_calls_bound p hp.2.2.2
  · intro p hp
    trivial

end LongTails.Theorems.CompositeLazyCubicAcceleration
