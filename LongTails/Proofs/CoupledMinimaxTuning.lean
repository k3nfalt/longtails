import LongTails.Proofs.CoupledMinimaxGeometry
import LongTails.Proofs.CoupledMinimaxAcceleration
import LongTails.Proofs.PLMinimaxTuning

namespace LongTails.Proofs.CoupledMinimaxTuning

open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax
open LongTails.Algorithms.CoupledMinimaxInner
open LongTails.Proofs.CoupledMinimaxGeometry

lemma smoothness_pos {p : Params} (hv : Valid p) : 0 < smoothness p := by
  unfold smoothness
  have hμ := hv.μ_pos
  have hf := hv.Lf_nonneg
  have hJ := hv.J_nonneg
  have hLJ := hv.LJ_nonneg
  have hcap := cap_pos hv
  positivity

lemma μ_le_smoothness {p : Params} (hv : Valid p) : p.μ ≤ smoothness p := by
  unfold smoothness
  have hh := mul_nonneg (cap_pos hv).le hv.LJ_nonneg
  linarith [hv.Lf_nonneg, hv.J_nonneg]

lemma tolerance_pos {p : Params} (hv : Valid p) : 0 < tolerance p := by
  unfold tolerance
  have he := hv.ε_pos
  have hc := cap_pos hv
  positivity

lemma tolerance_le_one {p : Params} (hv : Valid p) : tolerance p ≤ 1 := by
  have he := hv.ε_pos
  have hc := cap_pos hv
  have hs := Real.sqrt_nonneg (p.constraints : ℝ)
  unfold tolerance
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma inner_weight {p : Params} (hv : Valid p) :
    4 ≤ p.μ * accumulated (smoothness p) (innerIterations p) := by
  have hL := smoothness_pos hv
  have hμ := hv.μ_pos
  have hr : 0 ≤ smoothness p / p.μ := div_nonneg hL.le hμ.le
  have hs := Real.sq_sqrt hr
  have hn : 4 * Real.sqrt (smoothness p / p.μ) ≤ (innerIterations p : ℝ) :=
    Nat.le_ceil _
  have hn0 : (0 : ℝ) ≤ innerIterations p := Nat.cast_nonneg _
  have hs0 := Real.sqrt_nonneg (smoothness p / p.μ)
  have hsq : 16 * (smoothness p / p.μ) ≤ (innerIterations p : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hμ.le
  have he : p.μ * (smoothness p / p.μ) = smoothness p := by field_simp
  unfold accumulated
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 4 * smoothness p)).mpr
  nlinarith

lemma restart_accuracy {p : Params} (hv : Valid p) :
    (1 / 2 : ℝ) ^ innerRestarts p * p.DY ≤ tolerance p / (12 * smoothness p) := by
  have hL := smoothness_pos hv
  have ht := tolerance_pos hv
  have hD := hv.DY_nonneg
  let A := 2 + 12 * smoothness p * p.DY / tolerance p
  have hA : 0 < A := by dsimp [A]; positivity
  have hn : Real.log A / Real.log 2 ≤ (innerRestarts p : ℝ) := Nat.le_ceil _
  have hh := OracleTemplate.PLMinimax.halving_log_bound hA (innerRestarts p) hn
  have hbound := mul_le_mul_of_nonneg_right hh hD
  apply hbound.trans
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hA).mpr
  dsimp [A]
  have he : tolerance p / (12 * smoothness p) *
      (2 + 12 * smoothness p * p.DY / tolerance p) =
      p.DY + tolerance p / (6 * smoothness p) := by field_simp; ring
  rw [he]
  exact le_add_of_nonneg_right (by positivity)

end LongTails.Proofs.CoupledMinimaxTuning
