import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace LongTails.Proofs.QuarticCoefficientBounds

lemma quartic_at_quadratic_root (δ g a b c u v t : ℝ)
    (ht : t ^ 2 + u * t - v = 0) :
    δ + g * t + a * t ^ 2 + b * t ^ 3 + c * t ^ 4 =
      δ + v * (a - b * u + c * (u ^ 2 + v)) +
        (g - u * (a - b * u + c * (u ^ 2 + v)) + v * (b - c * u)) * t := by
  have h : δ + g * t + a * t ^ 2 + b * t ^ 3 + c * t ^ 4 =
      (c * t ^ 2 + (b - c * u) * t + a - b * u + c * (u ^ 2 + v)) *
        (t ^ 2 + u * t - v) +
      (δ + v * (a - b * u + c * (u ^ 2 + v)) +
        (g - u * (a - b * u + c * (u ^ 2 + v)) + v * (b - c * u)) * t) := by ring
  simpa only [ht, mul_zero, zero_add] using h

lemma quartic_moment_nonneg {δ g a b c : ℝ}
    (h : ∀ t : ℝ, 0 ≤ δ + g * t + a * t ^ 2 + b * t ^ 3 + c * t ^ 4)
    (u : ℝ) {v : ℝ} (hv : 0 < v) :
    0 ≤ δ + v * (a - b * u + c * (u ^ 2 + v)) := by
  let d := Real.sqrt (u ^ 2 + 4 * v)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d ^ 2 = u ^ 2 + 4 * v := Real.sq_sqrt (by nlinarith [sq_nonneg u])
  have hdu : |u| < d := by
    nlinarith [sq_abs u, abs_nonneg u]
  let p := (d - u) / 2
  let n := (-d - u) / 2
  have hp : 0 < p := by dsimp [p]; linarith [le_abs_self u]
  have hn : n < 0 := by dsimp [n]; linarith [neg_abs_le u]
  have hpr : p ^ 2 + u * p - v = 0 := by dsimp [p]; nlinarith [hd2]
  have hnr : n ^ 2 + u * n - v = 0 := by dsimp [n]; nlinarith [hd2]
  have hpp := h p
  have hnn := h n
  rw [quartic_at_quadratic_root δ g a b c u v p hpr] at hpp
  rw [quartic_at_quadratic_root δ g a b c u v n hnr] at hnn
  have h1 := mul_nonneg (neg_nonneg.mpr hn.le) hpp
  have h2 := mul_nonneg hp.le hnn
  by_contra hh
  have hh' : δ + v * (a - b * u + c * (u ^ 2 + v)) < 0 := lt_of_not_ge hh
  have h3 := mul_neg_of_pos_of_neg (sub_pos.mpr (lt_trans hn hp)) hh'
  nlinarith

lemma quartic_coefficient_bound {δ g a b c v : ℝ}
    (h : ∀ t : ℝ, 0 ≤ δ + g * t + a * t ^ 2 + b * t ^ 3 + c * t ^ 4)
    (hc : 0 < c) (hv : 0 < v) (hδ : δ = c * v ^ 2) :
    b ^ 2 ≤ 4 * c * a + 8 * c ^ 2 * v := by
  have hm := quartic_moment_nonneg h (b / (2 * c)) hv
  have hi : δ + v * (a - b * (b / (2 * c)) + c * ((b / (2 * c)) ^ 2 + v)) =
      v / (4 * c) * (4 * c * a + 8 * c ^ 2 * v - b ^ 2) := by
    rw [hδ]
    field_simp
    ring
  rw [hi] at hm
  have hp : 0 < v / (4 * c) := div_pos hv (by positivity)
  have := nonneg_of_mul_nonneg_right hm hp
  linarith

lemma third_coefficient_bound {δ g H T M v : ℝ}
    (h : ∀ t : ℝ, 0 ≤ δ + g * t + H * t ^ 2 / 2 + T * t ^ 3 / 6 + M * t ^ 4)
    (hM : 0 < M) (hv : 0 < v) (hδ : δ = M * v ^ 2) :
    T ^ 2 ≤ 72 * M * (H + 4 * M * v) := by
  have hp : ∀ t : ℝ, 0 ≤ δ + g * t + (H / 2) * t ^ 2 + (T / 6) * t ^ 3 + M * t ^ 4 := by
    intro t
    convert h t using 1
    ring
  have hh := quartic_coefficient_bound hp hM hv hδ
  nlinarith

lemma second_coefficient_lower {δ g H T M v : ℝ}
    (h : ∀ t : ℝ, 0 ≤ δ + g * t + H * t ^ 2 / 2 + T * t ^ 3 / 6 + M * t ^ 4)
    (hM : 0 < M) (hv : 0 < v) (hδ : δ = M * v ^ 2) :
    -(4 * M * v) ≤ H := by
  have ht := third_coefficient_bound h hM hv hδ
  have hm : 0 < 72 * M := by positivity
  have hb : 0 ≤ 72 * M * (H + 4 * M * v) := (sq_nonneg T).trans ht
  have := nonneg_of_mul_nonneg_right hb hm
  linarith

end LongTails.Proofs.QuarticCoefficientBounds
