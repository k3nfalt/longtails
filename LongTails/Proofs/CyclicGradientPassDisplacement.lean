import LongTails.Proofs.CyclicGradientRun
import LongTails.Proofs.GdConvex

open Finset

namespace OracleTemplate.CyclicInterpolation.Hyp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} [NeZero m] {f : Fin m → E → ℝ} {g : Fin m × E → E} {L : ℝ} {xstar : E}
variable (h : Hyp m f g L xstar) (x0 : E)
include h

lemma dist_pass_le (K : ℕ) : ‖iter m g L x0 (K * m) - xstar‖ ≤ ‖x0 - xstar‖ := by
  induction K with
  | zero => simp [iter]
  | succ K ih =>
    rw [Nat.succ_mul]
    apply le_trans _ ih
    have := h.online_le_distance x0 (K * m)
    have := h.online_nonneg x0 (K * m)
    nlinarith [norm_nonneg (iter m g L x0 (K * m) - xstar),
      norm_nonneg (iter m g L x0 (K * m + m) - xstar)]

lemma online_le_displacement (K : ℕ) :
    online f g L x0 xstar (K * m) ≤
      2 * ‖x0 - xstar‖ * ‖iter m g L x0 (K * m) - iter m g L x0 (K * m + m)‖ := by
  let x := iter m g L x0 (K * m)
  let y := iter m g L x0 (K * m + m)
  have hx : ‖x - xstar‖ ≤ ‖x0 - xstar‖ := h.dist_pass_le x0 K
  have hy : ‖y - xstar‖ ≤ ‖x0 - xstar‖ := by
    simpa [y, Nat.succ_mul] using h.dist_pass_le x0 (K + 1)
  have hd := norm_sub_norm_le (x - xstar) (y - xstar)
  rw [sub_sub_sub_cancel_right] at hd
  calc
    _ ≤ ‖x - xstar‖ ^ 2 - ‖y - xstar‖ ^ 2 := h.online_le_distance x0 _
    _ = (‖x - xstar‖ - ‖y - xstar‖) * (‖x - xstar‖ + ‖y - xstar‖) := by ring
    _ ≤ ‖x - y‖ * (2 * ‖x0 - xstar‖) :=
      mul_le_mul hd (by linarith) (by positivity) (norm_nonneg _)
    _ = _ := mul_comm _ _

lemma displacement_bound (K : ℕ) :
    (K : ℝ) * (K - 1) * shift g L x0 (K * m) ≤
      (1 + (m : ℝ) * (m - 1)) * ‖x0 - xstar‖ ^ 2 := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hfirst : ‖iter m g L x0 m - xstar‖ ≤ ‖x0 - xstar‖ := by
    simpa using h.dist_pass_le x0 1
  have hp := h.potential x0 K
  have ha := mul_nonneg (Nat.cast_nonneg (α := ℝ) K) (h.online_nonneg x0 (K * m))
  have hb := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr hm))
    (sq_nonneg ‖iter m g L x0 (K * m) - xstar‖)
  linarith [sq_nonneg ‖iter m g L x0 ((K + 1) * m) - xstar‖,
    pow_le_pow_left₀ (norm_nonneg _) hfirst 2]

lemma pass_accuracy (K : ℕ) (hK : 2 ≤ K) :
    let B := 1 + (m : ℝ) * (m - 1)
    (m : ℝ)⁻¹ * ∑ i, (f i (iter m g L x0 (m * K)) - f i xstar) ≤
      2 * B * Real.sqrt B * L * ‖x0 - xstar‖ ^ 2 / (m * Real.sqrt ((K : ℝ) * (K - 1))) := by
  let B := 1 + (m : ℝ) * (m - 1)
  let D := (K : ℝ) * (K - 1)
  let d := ‖iter m g L x0 (K * m) - iter m g L x0 (K * m + m)‖
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hB : 0 ≤ B := by dsimp [B]; nlinarith
  have hD : 0 < D := mul_pos (by linarith) (by linarith)
  have hd : D * d ^ 2 ≤ B * ‖x0 - xstar‖ ^ 2 := h.displacement_bound x0 K
  have hs : Real.sqrt D * d ≤ Real.sqrt B * ‖x0 - xstar‖ := by
    simpa [Real.sqrt_mul hD.le, Real.sqrt_mul hB, Real.sqrt_sq (norm_nonneg _), d]
      using Real.sqrt_le_sqrt hd
  have hL := h.pos
  rw [Nat.mul_comm m K]
  change _ ≤ 2 * B * Real.sqrt B * L * ‖x0 - xstar‖ ^ 2 / (m * Real.sqrt D)
  rw [le_div_iff₀ (by positivity : 0 < (m : ℝ) * Real.sqrt D)]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  calc
    _ = (∑ i, (f i (iter m g L x0 (K * m)) - f i xstar)) * Real.sqrt D := by field_simp
    _ ≤ (L * B * (2 * ‖x0 - xstar‖ * d)) * Real.sqrt D := by
      gcongr
      exact (h.average_le_online x0 K).trans
        (mul_le_mul_of_nonneg_left (h.online_le_displacement x0 K) (by positivity))
    _ = (2 * L * B * ‖x0 - xstar‖) * (Real.sqrt D * d) := by ring
    _ ≤ (2 * L * B * ‖x0 - xstar‖) * (Real.sqrt B * ‖x0 - xstar‖) := by gcongr
    _ = _ := by ring

lemma pass_accuracy_relaxed {R : ℝ} (hdist : ‖x0 - xstar‖ ≤ R) (K : ℕ) (hK : 2 ≤ K) :
    let B := 1 + (m : ℝ) * (m - 1)
    (m : ℝ)⁻¹ * ∑ i, (f i (iter m g L x0 (m * K)) - f i xstar) ≤
      2 * B * Real.sqrt B * L * R ^ 2 / (m * ((K : ℝ) - 1)) := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hkm : 0 < (K : ℝ) - 1 := by linarith
  have hB : 0 ≤ 1 + (m : ℝ) * (m - 1) := by nlinarith
  have hL := h.pos
  have ht : (K : ℝ) - 1 ≤ Real.sqrt ((K : ℝ) * (K - 1)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  apply (h.pass_accuracy x0 K hK).trans
  gcongr

lemma pass_accuracy_simple {R : ℝ} (hdist : ‖x0 - xstar‖ ≤ R) (K : ℕ) (hK : 2 ≤ K) :
    (m : ℝ)⁻¹ * ∑ i, (f i (iter m g L x0 (m * K)) - f i xstar) ≤
      2 * (m : ℝ) ^ 2 * L * R ^ 2 / ((K : ℝ) - 1) := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hkm : 0 < (K : ℝ) - 1 := by linarith
  have hL := h.pos
  let B := 1 + (m : ℝ) * (m - 1)
  have hb : B ≤ (m : ℝ) ^ 2 := by dsimp [B]; linarith
  have hs : Real.sqrt B ≤ m := by simpa using Real.sqrt_le_sqrt hb
  apply (h.pass_accuracy_relaxed x0 hdist K hK).trans
  change 2 * B * Real.sqrt B * L * R ^ 2 / _ ≤ _
  calc
    _ ≤ 2 * (m : ℝ) ^ 2 * m * L * R ^ 2 / (m * ((K : ℝ) - 1)) := by
      gcongr
    _ = _ := by field_simp

lemma initial_accuracy {R ε : ℝ} (hdist : ‖x0 - xstar‖ ≤ R) (hsmall : L * R ^ 2 ≤ 2 * ε) :
    (m : ℝ)⁻¹ * ∑ i, (f i x0 - f i xstar) ≤ ε := by
  have hL := h.pos
  have hterm (i : Fin m) : f i x0 - f i xstar ≤ ε := by
    have hg := fun x => h.grad i x
    have hl := fun x y => h.lip i x y
    have hu := Gradient.smooth_upper_bound hg hl xstar x0
    rw [gradient_min_zero hL hg hl (h.min i), inner_zero_left, add_zero] at hu
    linarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist 2) hL.le]
  rw [inv_mul_le_iff₀ (by exact_mod_cast NeZero.pos m : 0 < (m : ℝ))]
  simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)

end OracleTemplate.CyclicInterpolation.Hyp
