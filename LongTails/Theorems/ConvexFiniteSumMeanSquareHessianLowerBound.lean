import LongTails.TemplateLowerBound
import LongTails.Setups.ConvexFiniteSumMeanSquareHessian
import LongTails.Proofs.ComponentHessianExecution
import LongTails.Proofs.ComponentHessianInitialization
import LongTails.Proofs.ComponentHessianTuning

namespace LongTails.Theorems.ConvexFiniteSumMeanSquareHessianLowerBound

open OracleTemplate LongTails.Proofs

noncomputable def budget : (let S := LongTails.Setups.ConvexFiniteSumMeanSquareHessian.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  ⌊p.n * (1 + (p.H * p.R ^ 3 / (Real.sqrt p.n * p.ε)) ^ (2 / 7 : ℝ)) / 2 ^ 16⌋₊

theorem result : NonConvergence LongTails.Setups.ConvexFiniteSumMeanSquareHessian.spec budget := by
  intro p hp A _ b hb
  obtain ⟨hn, hH, hR, hε, hd⟩ := hp
  have hvalid : LongTails.Setups.ConvexFiniteSumMeanSquareHessian.spec.valid p := ⟨hn, hH, hR, hε, hd⟩
  by_cases hsmall : 4 * b 0 ≤ p.n
  · apply ComponentHessianInitialization.failure hn _ hR hε A b hsmall
    exact lt_of_lt_of_le (by positivity) hd
  have hs : 0 ≤ ComponentHessianTuning.scale p := by unfold ComponentHessianTuning.scale; positivity
  have hb' : (b 0 : ℝ) ≤ p.n * (1 + ComponentHessianTuning.scale p) / 2 ^ 16 :=
    (Nat.cast_le.mpr (hb 0)).trans (Nat.floor_le (by positivity))
  obtain ⟨k, hk, hT, hlen, hceil⟩ := ComponentHessianTuning.choose_length hn hs hb' (by omega)
  obtain ⟨D, hD, hdD, hsize, hkd⟩ := ComponentHessianTuning.dimension hvalid hceil hT
  obtain ⟨c, β, hc, hβ, hr, hh, he⟩ := ComponentHessianTuning.parameters hvalid hlen
  exact ComponentHessianExecution.failure hn hc hβ hr hh he hD hdD hk hkd A b hT hsize

end LongTails.Theorems.ConvexFiniteSumMeanSquareHessianLowerBound
