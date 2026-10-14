import LongTails.Proofs.MarkovProductEnergy
import LongTails.Proofs.MarkovOperatorRenewal
import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped BigOperators

namespace OracleTemplate.MarkovProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_projection_sum_sq (φ : ℂ → ℝ) (hφ : ∀ z, |φ z| ≤ ‖z‖)
    (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (x y : ℕ → E) (n : ℕ) :
    (∑ k ∈ Finset.range n, w k * φ (inner ℂ (x k) (y k))) ^ 2 ≤
      (∑ k ∈ Finset.range n, w k * ‖x k‖ ^ 2) *
      (∑ k ∈ Finset.range n, w k * ‖y k‖ ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro k hk; exact mul_nonneg (hw k) (sq_nonneg _)
  · intro k hk; exact mul_nonneg (hw k) (sq_nonneg _)
  · intro k hk
    have hb : |φ (inner ℂ (x k) (y k))| ≤ ‖x k‖ * ‖y k‖ :=
      (hφ _).trans (norm_inner_le_norm _ _)
    have hs : φ (inner ℂ (x k) (y k)) ^ 2 ≤ ‖x k‖ ^ 2 * ‖y k‖ ^ 2 := by
      have ht := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hb
      simpa only [sq_abs, mul_pow] using ht
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (w k))
    nlinarith

lemma geometric_projection_area_bound (φ : ℂ → ℝ) (hφ : ∀ z, |φ z| ≤ ‖z‖)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (x : ℕ → E) (n : ℕ) :
    (1 - r ^ 2) * |∑ k ∈ Finset.range n,
      r ^ (2 * k) * φ (inner ℂ (x 0 - x k) (x k - x (k + 1)))| ≤
      2 * ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by
  let A := ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x k - x 0‖ ^ 2
  let B := ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2
  let I := ∑ k ∈ Finset.range n,
    r ^ (2 * k) * φ (inner ℂ (x 0 - x k) (x k - x (k + 1)))
  have hcs : I ^ 2 ≤ A * B := by
    have h := inner_projection_sum_sq φ hφ (fun k => r ^ (2 * k))
      (fun k => pow_nonneg hr _) (fun k => x 0 - x k) (fun k => x k - x (k + 1)) n
    have hA : (∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x 0 - x k‖ ^ 2) = A := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_sub_rev (x 0) (x k)]
    have hB : (∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x k - x (k + 1)‖ ^ 2) = B := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_sub_rev (x k) (x (k + 1))]
    rw [hA, hB] at h
    exact h
  have hd : (1 - r ^ 2) ^ 2 * A ≤ 4 * B := geometric_displacement_rescaled r hr hr1 x n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm := mul_le_mul_of_nonneg_left hcs (sq_nonneg (1 - r ^ 2))
  have hn := mul_le_mul_of_nonneg_right hd hB
  have hα : 0 ≤ 1 - r ^ 2 := by nlinarith
  change (1 - r ^ 2) * |I| ≤ 2 * B
  nlinarith [sq_abs I, abs_nonneg I]

lemma imaginary_area_telescope (x : ℕ → E)
    (hreal : ∀ k, (inner ℂ (x k) (x k - x (k + 1))).im = 0) (n : ℕ) :
    (inner ℂ (x 0) (x 0 - x n)).im =
      ∑ k ∈ Finset.range n, (inner ℂ (x 0 - x k) (x k - x (k + 1))).im := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : inner ℂ (x 0) (x 0 - x (n + 1)) =
        inner ℂ (x 0) (x 0 - x n) + inner ℂ (x 0) (x n - x (n + 1)) := by
      rw [← inner_add_right]
      congr 1
      abel
    rw [he, Complex.add_im, ih, Finset.sum_range_succ, inner_sub_left, Complex.sub_im,
      hreal n, sub_zero]

lemma geometric_displacement_variation (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (x : ℕ → E) (n : ℕ) :
    (1 - r ^ 2) * (∑ k ∈ Finset.range n,
      r ^ (2 * k) * (‖x 0 - x (k + 1)‖ ^ 2 - ‖x 0 - x k‖ ^ 2)) ≤
      5 * ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by
  let S := ∑ k ∈ Finset.range n,
    r ^ (2 * k) * (inner ℂ (x 0 - x k) (x k - x (k + 1))).re
  let B := ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2
  have hS : (1 - r ^ 2) * |S| ≤ 2 * B :=
    geometric_projection_area_bound Complex.re Complex.abs_re_le_norm r hr hr1 x n
  have hα : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlinear : (1 - r ^ 2) * S ≤ 2 * B :=
    (mul_le_mul_of_nonneg_left (le_abs_self S) hα).trans hS
  have hterm (k : ℕ) : ‖x 0 - x (k + 1)‖ ^ 2 - ‖x 0 - x k‖ ^ 2 =
      2 * (inner ℂ (x 0 - x k) (x k - x (k + 1))).re + ‖x (k + 1) - x k‖ ^ 2 := by
    rw [show x 0 - x (k + 1) = (x 0 - x k) + (x k - x (k + 1)) by abel]
    rw [norm_add_sq (𝕜 := ℂ), norm_sub_rev (x k) (x (k + 1))]
    change ‖x 0 - x k‖ ^ 2 + 2 * (inner ℂ (x 0 - x k) (x k - x (k + 1))).re +
      ‖x (k + 1) - x k‖ ^ 2 - ‖x 0 - x k‖ ^ 2 = _
    ring
  have he : (∑ k ∈ Finset.range n,
      r ^ (2 * k) * (‖x 0 - x (k + 1)‖ ^ 2 - ‖x 0 - x k‖ ^ 2)) = 2 * S + B := by
    dsimp [S, B]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hterm k]
    ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_right (show 1 - r ^ 2 ≤ 1 by nlinarith [sq_nonneg r]) hB
  change (1 - r ^ 2) * (2 * S + B) ≤ 5 * B
  nlinarith

lemma disk_scalar_bound {D J : ℝ} (hJ : 0 ≤ J) (hJD : J ≤ D)
    (c z : ℂ) (hc_re : c.re = (D - J) / 2) (hc_im : |c.im| ≤ D / 4)
    (hz : ‖z‖ ≤ 1 / 2) : -D + 2 * (z * c).re + ‖z‖ ^ 2 * J ≤ 0 := by
  have hD : 0 ≤ D := hJ.trans hJD
  have hre : 0 ≤ c.re := by linarith
  have hc : ‖c‖ ≤ 3 * D / 4 := by
    have hn := Complex.norm_le_abs_re_add_abs_im c
    rw [abs_of_nonneg hre] at hn
    linarith
  have hprod := mul_le_mul hz hc (norm_nonneg c) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcross := Complex.re_le_norm (z * c)
  rw [norm_mul] at hcross
  have hz2 : ‖z‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg z]
  have hlast := mul_le_mul_of_nonneg_right hz2 hJ
  nlinarith

end OracleTemplate.MarkovProduct
