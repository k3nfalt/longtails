import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OracleTemplate.BallProximal

open scoped BigOperators

lemma weighted_cauchy {ι : Type*} (s : Finset ι) (t a : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (ha : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, t i) ^ 2 ≤ (∑ i ∈ s, t i * a i) * ∑ i ∈ s, t i / a i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => mul_nonneg (ht i hi) (ha i hi).le)
    (fun i hi => div_nonneg (ht i hi) (ha i hi).le)
  intro i hi
  have hn := ne_of_gt (ha i hi)
  field_simp
  exact le_rfl

lemma kernel_deficit {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    1 - (a - m) / m - (b - m) / m ≤ min a b / max a b := by
  have ha0 : 0 < a := lt_of_lt_of_le hm ha
  have hb0 : 0 < b := lt_of_lt_of_le hm hb
  have hbase (a b : ℝ) (ha : m ≤ a) (hb : m ≤ b) :
      (3 * m - a - b) * b ≤ a * m := by
    have h1 := sq_nonneg (b - m)
    have h2 := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ b + m by linarith)
    nlinarith
  have he : 1 - (a - m) / m - (b - m) / m = (3 * m - a - b) / m := by field_simp; ring
  rw [he]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    exact (div_le_div_iff₀ hm hb0).mpr (hbase a b ha hb)
  · rw [min_eq_right hba, max_eq_left hba]
    apply (div_le_div_iff₀ hm ha0).mpr
    have hh := hbase b a hb ha
    nlinarith


lemma cauchy_combine {x y a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hx : x ^ 2 ≤ a * b) (hy : y ^ 2 ≤ c * d) :
    (x + y) ^ 2 ≤ (a + c) * (b + d) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin 2))
    (r := ![x, y]) (f := ![a, c]) (g := ![b, d])
    (by intro i hi; fin_cases i <;> simp_all)
    (by intro i hi; fin_cases i <;> simp_all)
    (by intro i hi; fin_cases i <;> simp_all)
  simpa [Fin.sum_univ_two] using h


lemma high_gap_algebra {H A r z B P : ℝ} (hH : 0 ≤ H) (hA : 0 < A)
    (hr : A ≤ r) (hz : H ≤ z) (hB : H ^ 2 ≤ A * B)
    (hP : H ^ 2 - 2 * H * (z - H) ≤ P) :
    H ^ 2 * (A + r) ^ 2 ≤ A ^ 2 * (P + 2 * r * B) + r ^ 2 * z ^ 2 := by
  have hr0 : 0 ≤ r := le_trans (le_of_lt hA) hr
  have hrA : A ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (le_of_lt hA) hr 2
  have h1 := mul_le_mul_of_nonneg_left hP (sq_nonneg A)
  have h2 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * A * r by positivity)
  have h3 : 0 ≤ r ^ 2 * (z + H) - 2 * A ^ 2 * H := by
    have h31 := mul_le_mul_of_nonneg_right hrA (show 0 ≤ 2 * H by positivity)
    have h32 := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hz)
    nlinarith
  have h4 := mul_nonneg h3 (sub_nonneg.mpr hz)
  nlinarith

lemma logarithmic_mean_lower {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    2 * (v - u) ≤ (v + u) * (Real.log v - Real.log u) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h := Real.le_log_one_add_of_nonneg (div_nonneg (sub_nonneg.mpr huv) hu.le)
  have he : 1 + (v - u) / u = v / u := by field_simp; ring
  rw [he, Real.log_div (ne_of_gt hv) (ne_of_gt hu)] at h
  have he' : 2 * ((v - u) / u) / ((v - u) / u + 2) = 2 * (v - u) / (v + u) := by
    have hd : (v - u) / u + 2 = (v + u) / u := by field_simp; ring
    rw [hd, ← mul_div_assoc, div_div_div_cancel_right₀ (ne_of_gt hu)]
  rw [he'] at h
  have hh := (div_le_iff₀ (show 0 < v + u by positivity)).mp h
  nlinarith

lemma one_piece_logarithmic {t a r : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hr : 0 < r) :
    2 * t ^ 2 ≤ (Real.log (r + t * a) - Real.log r) * (t ^ 2 + 2 * t * r / a) := by
  have h := logarithmic_mean_lower hr (show r ≤ r + t * a by nlinarith [mul_nonneg ht ha.le])
  have hh := mul_le_mul_of_nonneg_left h (div_nonneg ht ha.le)
  have he : t / a * (2 * (r + t * a - r)) = 2 * t ^ 2 := by field_simp; ring
  have he' : t / a * ((r + t * a + r) * (Real.log (r + t * a) - Real.log r)) =
      (Real.log (r + t * a) - Real.log r) * (t ^ 2 + 2 * t * r / a) := by field_simp; ring
  rwa [he, he'] at hh


lemma split_energy_algebra {s q h D : ℝ} (hh : 0 < h)
    (hD : 2 * s ^ 2 / h + 4 * q ^ 2 ≤ D) :
    4 * (s + q) ^ 2 ≤ (1 + 2 * h) * D := by
  have h1 := mul_le_mul_of_nonneg_left hD (show 0 ≤ 1 + 2 * h by positivity)
  have h2 : 0 ≤ 2 / h * (s - 2 * h * q) ^ 2 := by positivity
  field_simp at h1 h2 ⊢
  nlinarith

end OracleTemplate.BallProximal
