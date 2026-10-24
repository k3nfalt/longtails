import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.QuadraticPerceptronBatchPotential

lemma gap_square_bound (b y k : ℝ) (hb : 0 ≤ b) (hy : 0 ≤ y)
    (hk : 4 * k ≤ y) :
    b * y + 2 * ((max (b - y + k) 0) ^ 2 - b ^ 2) ≤ y ^ 2 / 8 := by
  by_cases h : b - y + k ≤ 0
  · rw [max_eq_right h]
    nlinarith [sq_nonneg (4 * b - y)]
  · rw [max_eq_left (le_of_not_ge h)]
    have hd : 0 ≤ y - k := by linarith
    have hm := mul_nonneg (show 0 ≤ b - (y - k) by linarith)
      (show 0 ≤ 3 * y - 4 * k by linarith)
    have hs := mul_nonneg (show 0 ≤ y - k - y / 4 by linarith) hd
    nlinarith [sq_nonneg y]

lemma nonflip_drift (x y k : ℝ) (hk : 0 ≤ k)
    (hy : 4 * k ≤ y) (hy₁ : y ≤ 1) :
    k * (2 - y) - x * y +
        2 * ((max (1 - x - y + k) 0) ^ 2 - (max (1 - x) 0) ^ 2) ≤
      -(x * y + k) / 4 := by
  have hy₀ : 0 ≤ y := by linarith
  by_cases h : 1 ≤ x
  · rw [max_eq_right (show 1 - x - y + k ≤ 0 by linarith),
      max_eq_right (show 1 - x ≤ 0 by linarith)]
    have hxy := mul_le_mul_of_nonneg_right h hy₀
    nlinarith [mul_nonneg hk hy₀]
  · have hb : 0 ≤ 1 - x := by linarith
    have hg := gap_square_bound (1 - x) y k hb hy₀ hy
    rw [max_eq_left hb]
    have hxy := mul_nonneg hb hy₀
    have hyy := mul_nonneg hy₀ (show 0 ≤ 1 - y by linarith)
    nlinarith [mul_nonneg hk hy₀]

lemma flip_drift (x y k : ℝ) (hx : 0 ≤ x) (hk : 0 ≤ k)
    (hk₁ : k ≤ 1 / 256) (hy : 1 ≤ y)
    (hnext : 4 * k * (y - 1) ≤ x + k) :
    y * (k - x) - 2 * (max (1 - x) 0) ^ 2 ≤ -(x * y + k) / 4 := by
  by_cases h : 2 * k ≤ x
  · have hxy := mul_nonneg (show 0 ≤ x - 2 * k by linarith)
      (show 0 ≤ y by linarith)
    have hky := mul_nonneg hk (show 0 ≤ y - 1 by linarith)
    nlinarith [sq_nonneg (max (1 - x) 0)]
  · have hx₁ : x ≤ 1 := by linarith
    rw [max_eq_left (show 0 ≤ 1 - x by linarith)]
    have hkpos : 0 < k := by linarith
    have hy₁ : y ≤ 7 / 4 := by nlinarith
    have hxy := mul_nonneg hx (show 0 ≤ y by linarith)
    have hky := mul_nonneg hk (show 0 ≤ 7 / 4 - y by linarith)
    nlinarith [sq_nonneg x]

lemma potential_bounds (s v a b : ℝ) (hs : 0 ≤ s) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ s / 16) :
    (s ^ 2 + v ^ 2) / 2 ≤
        s ^ 2 - v ^ 2 + v * (a - b) + 2 * (max (v - a) 0) ^ 2 ∧
      s ^ 2 - v ^ 2 + v * (a - b) + 2 * (max (v - a) 0) ^ 2 ≤
        2 * (s ^ 2 + v ^ 2) := by
  have ha₁ : a ≤ s / 16 := by linarith
  have hb₁ : b ≤ s / 16 := by linarith
  have hva := mul_nonneg hv ha
  have hvb := mul_nonneg hv hb
  have hva₁ := mul_nonneg hv (show 0 ≤ s / 16 - a by linarith)
  have hvb₁ := mul_nonneg hv (show 0 ≤ s / 16 - b by linarith)
  by_cases h : v ≤ a
  · rw [max_eq_right (show v - a ≤ 0 by linarith)]
    have hvs : v ≤ s / 16 := by linarith
    have hsq := mul_nonneg (show 0 ≤ s / 16 - v by linarith)
      (show 0 ≤ s / 16 + v by positivity)
    have hprod := mul_nonneg hs (show 0 ≤ s / 16 - v by linarith)
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg v]
  · rw [max_eq_left (show 0 ≤ v - a by linarith)]
    have hasq := mul_nonneg (show 0 ≤ s / 16 - a by linarith)
      (show 0 ≤ s / 16 + a by positivity)
    constructor <;> nlinarith [sq_nonneg (s - v), sq_nonneg a, sq_nonneg v]

lemma positive_square_add_le (x y : ℝ) :
    (max (x + y) 0) ^ 2 ≤ (max x 0) ^ 2 + 2 * max x 0 * y + y ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    by_cases hxy : 0 ≤ x + y
    · rw [max_eq_left hxy]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hxy)]
      nlinarith [sq_nonneg (x + y)]
  · rw [max_eq_right (le_of_not_ge hx)]
    by_cases hxy : 0 ≤ x + y
    · rw [max_eq_left hxy]
      have h := mul_nonneg (show 0 ≤ -x by linarith)
        (show 0 ≤ x + 2 * y by linarith)
      nlinarith
    · rw [max_eq_right (le_of_not_ge hxy)]
      nlinarith [sq_nonneg y]

lemma positive_part_support (x y : ℝ) :
    max x 0 + (if 0 < x then y else 0) ≤ max (x + y) 0 := by
  split_ifs with hx
  · rw [max_eq_left hx.le]
    exact le_max_left _ _
  · rw [max_eq_right (le_of_not_gt hx)]
    simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma batch_potential_identity (c g m : E) (v η : ℝ) :
    ‖c + (η * v) • g‖ ^ 2 - (v + η * ⟪g, c⟫) ^ 2 +
        η * (v + η * ⟪g, c⟫) * ⟪m, c + (η * v) • g⟫ -
        (‖c‖ ^ 2 - v ^ 2 + η * v * ⟪m, c⟫) =
      η ^ 2 * ⟪g, c⟫ * (⟪m, c⟫ - ⟪g, c⟫) +
        η ^ 2 * ((v * (v + η * ⟪g, c⟫)) * ⟪m, g⟫ + v ^ 2 * ‖g‖ ^ 2) := by
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right, real_inner_comm c g,
    mul_pow, Real.norm_eq_abs, sq_abs, inner_add_right, real_inner_smul_right]
  ring

lemma nonflip_drift_scaled (p q v η R : ℝ) (hv : 0 < v) (hη : 0 < η)
    (hescape : 4 * η * R ^ 2 * v ≤ q) (hflip : η * q ≤ v) :
    η ^ 2 * (R ^ 2 * v * (2 * v - η * q) - p * q) +
      2 * ((max (v - η * p - η * q + η ^ 2 * v * R ^ 2) 0) ^ 2 -
        (max (v - η * p) 0) ^ 2) ≤ -(η ^ 2 * (p * q + R ^ 2 * v ^ 2)) / 4 := by
  have hk : 0 ≤ η ^ 2 * R ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hy : 4 * (η ^ 2 * R ^ 2) ≤ η * q / v := by
    rw [le_div_iff₀ hv]
    nlinarith [mul_le_mul_of_nonneg_left hescape hη.le]
  have hy₁ : η * q / v ≤ 1 := (div_le_one hv).mpr hflip
  have h := nonflip_drift (η * p / v) (η * q / v) (η ^ 2 * R ^ 2) hk hy hy₁
  have he₁ : 1 - η * p / v = (v - η * p) / v := by field_simp
  rw [he₁] at h
  have he₂' : (v - η * p) / v - η * q / v + η ^ 2 * R ^ 2 =
      (v - η * p - η * q + η ^ 2 * v * R ^ 2) / v := by field_simp
  rw [he₂'] at h
  have hm (a : ℝ) : max (a / v) 0 = max a 0 / v := by
    simpa using max_div_div_right hv.le a 0
  rw [hm, hm] at h
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg v)
  field_simp at hmul
  ring_nf at hmul ⊢
  linarith only [hmul]
lemma flip_drift_scaled (p q v η R : ℝ) (hp : 0 ≤ p) (hv : 0 < v) (hη : 0 < η)
    (hk : η ^ 2 * R ^ 2 ≤ 1 / 256) (hflip : v ≤ η * q)
    (hnext : 4 * η * R ^ 2 * (η * q - v) ≤ p + η * v * R ^ 2) :
    η ^ 2 * q * (η * v * R ^ 2 - p) - 2 * (max (v - η * p) 0) ^ 2 ≤
      -(η ^ 2 * (p * q + R ^ 2 * v ^ 2)) / 4 := by
  have hx : 0 ≤ η * p / v := div_nonneg (mul_nonneg hη.le hp) hv.le
  have hy : 1 ≤ η * q / v := (one_le_div hv).mpr hflip
  have hn : 4 * (η ^ 2 * R ^ 2) * (η * q / v - 1) ≤ η * p / v + η ^ 2 * R ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hnext hη.le
    apply (mul_le_mul_iff_left₀ hv).mp
    field_simp
    nlinarith [hh]
  have h := flip_drift (η * p / v) (η * q / v) (η ^ 2 * R ^ 2) hx
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hk hy hn
  have he : 1 - η * p / v = (v - η * p) / v := by field_simp
  have hm (a : ℝ) : max (a / v) 0 = max a 0 / v := by
    simpa using max_div_div_right hv.le a 0
  rw [he, hm] at h
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg v)
  field_simp at hmul
  ring_nf at hmul ⊢
  linarith only [hmul]
end LongTails.Proofs.QuadraticPerceptronBatchPotential
