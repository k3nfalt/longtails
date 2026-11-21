import LongTails.TemplateLowerBound
import LongTails.Setups.HighDimensionalGeneralizedMinty
import LongTails.Proofs.GeneralizedMintyLowerBound

namespace LongTails.Theorems.GeneralizedMintyLowerBound

open OracleTemplate LongTails.Proofs.GeneralizedMintyScales LongTails.Proofs.GeneralizedMintyLowerBound

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalGeneralizedMinty.spec;
    S.Params → Fin S.numOracles → ℕ) :=
  fun p _ => ⌊(p.R * (p.L0 / p.ε + p.L1) / 1024) ^ 2⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalGeneralizedMinty.spec budget := by
  intro p hp A _ b hb
  obtain ⟨s, hs⟩ := scales p hp
  have hN : b 0 ≤ s.m := by rw [hs]; exact hb 0
  obtain ⟨π, hf⟩ := insufficient s hp.1 A (b 0) hN
  refine ⟨instanceField s π, oracle s π, admissible s π hp.1, ?_⟩
  have he : b = fun _ => b 0 := funext (fun i => congrArg b (Subsingleton.elim i 0))
  rw [he]
  exact hf

end LongTails.Theorems.GeneralizedMintyLowerBound
