import LongTails.Setups.SharpRelativeErrorSmoothConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.SharpEnvelopeGuarantee

namespace LongTails.Theorems.PolylogPrecisionRelativeErrorConvex

open OracleTemplate LongTails.Setups.SharpRelativeErrorSmoothConvex
open LongTails.Algorithms.SharpEnvelope

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈8 * (33 * (1 + Real.log (2 + p.L * p.R ^ 2 / p.ε))) ^ 20 * (2 + p.L * p.R ^ 2 / p.ε) ^ (5 / 8 : ℝ)⌉₊

theorem result : Convergence LongTails.Setups.SharpRelativeErrorSmoothConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p =>
    let T := p.L * p.R ^ 2 / p.ε
    let b := ⌈32 * (1 + Real.log (2 + T))⌉₊
    let d := ⌈Real.log (2 + T) / Real.log (4 * (b : ℝ) ^ 32 - 1)⌉₊
    let n := b ^ 20
    sharpEnvelopeOutput p.L b d n p.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨⟨hL, -, -, -, hε⟩, hα⟩
  rintro f O ⟨-, hcv, hup, herr, xstar, hmin, hdist⟩
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  exact LongTails.Proofs.SharpEnvelopeGuarantee.execute_accuracy ⟨hL, hcv, hup⟩ hε hα
    (fun x => hmin (Set.mem_univ x)) hdist O herr (budget p 0) le_rfl seed ξ

end LongTails.Theorems.PolylogPrecisionRelativeErrorConvex
