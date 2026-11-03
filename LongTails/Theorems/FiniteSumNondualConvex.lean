import LongTails.Setups.FiniteSumNondualSmoothConvex
import LongTails.Proofs.FiniteSumNondualGuarantee
import LongTails.Proofs.FiniteSumNondualLowerBound
import LongTails.Proofs.FiniteSumNondualLowerAffine

namespace LongTails.Theorems.FiniteSumNondualConvex

open OracleTemplate
open LongTails.Setups.FiniteSumNondualSmoothConvex
open LongTails.Algorithms.FiniteSumNondual
open LongTails.Proofs.FiniteSumNondualGuarantee

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 1099511627776 * p.n * (1 + ⌈(p.L * p.R ^ 2 / (p.n * p.ε)) ^ (1 / 3 : ℝ)⌉₊) * (1 + Nat.log 2 (2 + p.d + p.n + ⌈p.L * p.R ^ 2 / p.ε⌉₊)) ^ 4

theorem result : Convergence LongTails.Setups.FiniteSumNondualSmoothConvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f oracle ha
  change spec.successful p f (fun seed : Seeds p × ((k : ℕ) → oracle.Seed k) => runOutput p oracle (budget p 0) seed.1 seed.2) _
  apply successful_execution p hp f oracle ha
  simp only [budget, rootSize_explicit, logSize, scale, le_refl]

end LongTails.Theorems.FiniteSumNondualConvex
