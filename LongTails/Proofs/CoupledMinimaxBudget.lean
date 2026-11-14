import LongTails.Proofs.CoupledMinimaxTuning

namespace LongTails.Proofs.CoupledMinimaxBudget

open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax
open LongTails.Proofs.CoupledMinimaxGeometry
open LongTails.Proofs.CoupledMinimaxTuning

lemma conversion_factor (p : Params) :
    1 + Real.sqrt p.constraints + cap p =
      2 + Real.sqrt p.constraints + 2 * p.Z * (p.Gy + 1) / p.δ := by
  unfold cap
  ring

lemma gap_nonneg {p : Params} (hv : Valid p) : 0 ≤ gapBound p := by
  unfold gapBound
  exact add_nonneg (add_nonneg (mul_nonneg hv.Gx_nonneg hv.DX_nonneg)
    (mul_nonneg hv.Gy_nonneg hv.DY_nonneg)) (mul_nonneg (cap_pos hv).le hv.C_nonneg)

lemma value_smoothness_bound {p : Params} (hv : Valid p) :
    valueSmoothness p ≤ 2 * smoothness p ^ 2 / p.μ := by
  have hμ := hv.μ_pos
  have hL := smoothness_pos hv
  have hm := mul_le_mul_of_nonneg_left (μ_le_smoothness hv) hL.le
  have he : valueSmoothness p * p.μ = smoothness p * p.μ + smoothness p ^ 2 := by
    unfold valueSmoothness
    field_simp
  apply (le_div_iff₀ hμ).mpr
  nlinarith

lemma restart_argument {p : Params} (_hv : Valid p) :
    12 * smoothness p * p.DY / tolerance p =
      24 * smoothness p * p.DY * (1 + p.ε) *
        (1 + Real.sqrt p.constraints + cap p) / p.ε := by
  unfold tolerance
  field_simp
  ring

lemma outer_argument_bound {p : Params} (hv : Valid p) :
    72 * valueSmoothness p * gapBound p / tolerance p ^ 2 ≤
      576 * smoothness p ^ 2 * gapBound p * (1 + p.ε) ^ 2 *
        (1 + Real.sqrt p.constraints + cap p) ^ 2 / (p.μ * p.ε ^ 2) := by
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (value_smoothness_bound hv) (by norm_num : (0 : ℝ) ≤ 72)) (gap_nonneg hv))
    (sq_nonneg (tolerance p))
  apply hh.trans_eq
  unfold tolerance
  field_simp
  ring

lemma calls_bound {p : Params} (hv : Valid p) :
    calls p ≤ (2 + ⌈4 * Real.sqrt (smoothness p / p.μ)⌉₊ *
      ⌈Real.log (2 + 24 * smoothness p * p.DY * (1 + p.ε) *
        (1 + Real.sqrt p.constraints + cap p) / p.ε) / Real.log 2⌉₊) *
      (1 + ⌈576 * smoothness p ^ 2 * gapBound p * (1 + p.ε) ^ 2 *
        (1 + Real.sqrt p.constraints + cap p) ^ 2 / (p.μ * p.ε ^ 2)⌉₊) := by
  have ho := Nat.ceil_mono (outer_argument_bound hv)
  unfold calls stepCalls innerIterations innerRestarts outerIterations
  rw [restart_argument hv]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left ho 1)

end LongTails.Proofs.CoupledMinimaxBudget
