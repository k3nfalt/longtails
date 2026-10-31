import LongTails.Setups.RecursiveRelativeErrorSmoothConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.RecursiveEnvelopeGuarantee

namespace LongTails.Theorems.RecursiveRelativeErrorConvex

open OracleTemplate LongTails.Setups.RecursiveRelativeErrorSmoothConvex
open LongTails.Algorithms.RecursiveEnvelope LongTails.Proofs.RecursiveEnvelopeBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈4 * Real.sqrt (2 + p.L * p.R ^ 2 / p.ε) * Real.exp (32 * (1 + Real.sqrt (Real.log (2 + p.L * p.R ^ 2 / p.ε))) * Real.log (32 + Real.log (2 + p.L * p.R ^ 2 / p.ε)))⌉₊

theorem result : Convergence LongTails.Setups.RecursiveRelativeErrorSmoothConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p =>
    let d := ⌈Real.sqrt (Real.log (2 + p.L * p.R ^ 2 / p.ε) / Real.log 4)⌉₊
    let m := 2048 * d * 2 ^ d
    recursiveEnvelopeOutput p.L d m p.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨⟨hL, -, -, -, hε⟩, hα⟩
  rintro f O ⟨-, hcv, hup, herr, xstar, hmin, hdist⟩
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  exact LongTails.Proofs.RecursiveEnvelopeGuarantee.execute_accuracy ⟨hL, hcv, hup⟩ hε hα
    (fun x => hmin (Set.mem_univ x)) hdist O herr (budget p 0) le_rfl seed ξ

end LongTails.Theorems.RecursiveRelativeErrorConvex
