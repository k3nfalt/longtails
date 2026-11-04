import LongTails.Setups.SharpRelativeErrorSmoothConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.SharpDistanceGuarantee

namespace LongTails.Theorems.NearAcceleratedPolylogPrecisionRelativeErrorConvex

open OracleTemplate LongTails.Setups.SharpRelativeErrorSmoothConvex
open LongTails.Algorithms.SharpDistanceEnvelope

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈32768 * (33 * (1 + Real.log (2 + p.L * p.R ^ 2 / p.ε))) ^ 16 * (1 + Real.log (33 * (1 + Real.log (2 + p.L * p.R ^ 2 / p.ε)))) * (2 + p.L * p.R ^ 2 / p.ε) ^ (1 / 2 + Real.log (16384 * (1 + Real.log (33 * (1 + Real.log (2 + p.L * p.R ^ 2 / p.ε))))) / (32 * Real.log (32 * (1 + Real.log (2 + p.L * p.R ^ 2 / p.ε)))))⌉₊

theorem result : Convergence LongTails.Setups.SharpRelativeErrorSmoothConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p =>
    let T := p.L * p.R ^ 2 / p.ε
    let b := ⌈32 * (1 + Real.log (2 + T))⌉₊
    let d := ⌈Real.log (2 + T) / Real.log (4 * (b : ℝ) ^ 32 - 1)⌉₊
    let n := ⌈4096 * (b : ℝ) ^ 16 * (1 + Real.log b)⌉₊
    distanceEnvelopeOutput p.L b d n p.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨⟨hL, -, -, -, hε⟩, hα⟩
  rintro f O ⟨-, hcv, hup, herr, xstar, hmin, hdist⟩
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  exact LongTails.Proofs.SharpDistanceGuarantee.execute_accuracy ⟨hL, hcv, hup⟩ hε hα
    (fun x => hmin (Set.mem_univ x)) hdist O herr (budget p 0) le_rfl seed ξ

end LongTails.Theorems.NearAcceleratedPolylogPrecisionRelativeErrorConvex
