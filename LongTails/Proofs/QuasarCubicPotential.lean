import LongTails.Proofs.CubicRegularization
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.QuasarCubicPotential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def psi (N : ℝ) (x0 : E) (c : ℝ) (s u : E) : ℝ := c + ⟪s, u⟫ + N / 6 * ‖u - x0‖ ^ 3

def center (N : ℝ) (x0 s : E) : E := x0 - (Real.sqrt (2 / N) / Real.sqrt ‖s‖) • s

lemma center_stationary {N : ℝ} (hN : 0 < N) (x0 s : E) :
    s + (N / 2 * ‖center N x0 s - x0‖) • (center N x0 s - x0) = 0 := by
  by_cases hs : s = 0
  · simp [center, hs]
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  set t := Real.sqrt (2 / N) / Real.sqrt ‖s‖
  have ht : 0 ≤ t := by positivity
  have hv : center N x0 s - x0 = -(t • s) := by simp [center, t]
  have hnorm : ‖center N x0 s - x0‖ = t * ‖s‖ := by
    rw [hv, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have ht2 : t ^ 2 * ‖s‖ = 2 / N := by
    simp only [t, div_pow, Real.sq_sqrt (div_pos two_pos hN).le, Real.sq_sqrt hsn.le]
    field_simp
  rw [hnorm, hv, smul_neg, smul_smul]
  have hc : N / 2 * (t * ‖s‖) * t = 1 := by
    have : N / 2 * (t * ‖s‖) * t = N / 2 * (t ^ 2 * ‖s‖) := by ring
    rw [this, ht2]
    field_simp
  rw [hc, one_smul, add_neg_cancel]

lemma psi_lower {N : ℝ} (hN : 0 < N) (x0 : E) (c : ℝ) (s u : E) :
    psi N x0 c s (center N x0 s) + N / 12 * ‖u - center N x0 s‖ ^ 3 ≤ psi N x0 c s u := by
  set v := center N x0 s
  have hb := CubicRegularization.cubic_bregman_lower (u - x0) (v - x0)
  have hst := center_stationary hN x0 s
  change s + (N / 2 * ‖v - x0‖) • (v - x0) = 0 at hst
  simp only [CubicRegularization.cubic, CubicRegularization.cubicGradient] at hb
  have huv : u - x0 - (v - x0) = u - v := by abel
  rw [huv] at hb
  have hs : s = -((N / 2 * ‖v - x0‖) • (v - x0)) := by
    rw [eq_neg_iff_add_eq_zero, hst]
  have hinner : ⟪s, u⟫ - ⟪s, v⟫ = -(N / 2) * ⟪‖v - x0‖ • (v - x0), u - v⟫ := by
    rw [← inner_sub_right, hs, inner_neg_left, real_inner_smul_left, real_inner_smul_left]
    ring
  simp only [psi]
  nlinarith

lemma cubic_min {N t β Λ : ℝ} (hN : 0 < N) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hΛ : 0 ≤ Λ)
    (hcond : 16 / 9 * β ^ 3 ≤ Λ ^ 2 * N) : -Λ ≤ N / 12 * t ^ 3 - β * t := by
  set u := Real.sqrt (β / N)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = β / N := Real.sq_sqrt (div_nonneg hβ hN.le)
  have hβu : β = N * u ^ 2 := by rw [hu2]; field_simp
  have hpoly : N / 12 * t ^ 3 - β * t + 4 / 3 * N * u ^ 3 =
      N / 12 * ((t - 2 * u) ^ 2 * (t + 4 * u)) := by rw [hβu]; ring
  have hsq : 0 ≤ N / 12 * ((t - 2 * u) ^ 2 * (t + 4 * u)) := by positivity
  have hΛu : 4 / 3 * N * u ^ 3 ≤ Λ := by
    have h1 : (4 / 3 * N * u ^ 3) ^ 2 ≤ Λ ^ 2 := by
      have : (4 / 3 * N * u ^ 3) ^ 2 * N = 16 / 9 * β ^ 3 := by rw [hβu]; ring
      have h2 : (4 / 3 * N * u ^ 3) ^ 2 * N ≤ Λ ^ 2 * N := by rw [this]; exact hcond
      exact le_of_mul_le_mul_right h2 hN
    have h0 : 0 ≤ 4 / 3 * N * u ^ 3 := by positivity
    nlinarith [sq_nonneg (4 / 3 * N * u ^ 3 - Λ), sq_nonneg (4 / 3 * N * u ^ 3 + Λ)]
  linarith

lemma young_cube {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) : t ≤ c ^ 2 * t ^ 3 / 3 + 2 / (3 * c) := by
  have key : 0 ≤ (c * t - 1) ^ 2 * (c * t + 2) := by positivity
  have h3 : 0 < 3 * c := by positivity
  rw [div_add_div _ _ (by norm_num : (3 : ℝ) ≠ 0) h3.ne', le_div_iff₀ (by positivity)]
  nlinarith

lemma amgm_square {c r θ : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) (hθ : 0 < θ) :
    c * r ^ 2 ≤ θ * r ^ 3 + 4 / 27 * c ^ 3 / θ ^ 2 := by
  have key : 0 ≤ (3 * θ * r - 2 * c) ^ 2 * (3 * θ * r + c) := by positivity
  have hθ2 : 0 < θ ^ 2 := by positivity
  have : c * r ^ 2 * (27 * θ ^ 2) ≤ θ * r ^ 3 * (27 * θ ^ 2) + 4 * c ^ 3 := by nlinarith
  have h' : 4 / 27 * c ^ 3 / θ ^ 2 = 4 * c ^ 3 / (27 * θ ^ 2) := by field_simp
  rw [h', ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  nlinarith

def weight (k : ℕ) : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2

def total (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2) / 6

lemma total_succ (k : ℕ) : total (k + 1) = total k + weight k := by
  simp only [total, weight]; push_cast; ring

lemma total_nonneg (k : ℕ) : 0 ≤ total k := by unfold total; positivity

lemma weight_pos (k : ℕ) : 0 < weight k := by unfold weight; positivity

lemma weight_le_total (k : ℕ) : weight k ≤ total (k + 1) := by
  rw [total_succ]; linarith [total_nonneg k]

lemma weight_cube_le (k : ℕ) : weight k ^ 3 ≤ 9 / 2 * total (k + 1) ^ 2 := by
  simp only [weight, total]
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp : 0 ≤ ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2 := by positivity
  nlinarith [mul_nonneg hp (show (0 : ℝ) ≤ 2 * k + 5 by linarith)]

lemma total_lower (k : ℕ) : (k : ℝ) ^ 3 / 6 ≤ total k := by
  simp only [total]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [sq_nonneg (k : ℝ)]

lemma total_upper (k : ℕ) : total k ≤ ((k : ℝ) + 1) ^ 3 := by
  simp only [total]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [sq_nonneg (k : ℝ)]

lemma inv_sqrt_step {n : ℝ} (hn : 1 ≤ n) :
    1 / (Real.sqrt (n + 1) ^ 3) ≤ 2 / Real.sqrt n - 2 / Real.sqrt (n + 1) := by
  set a := Real.sqrt n
  set b := Real.sqrt (n + 1)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = n := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
  have hab : a < b := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : a ≤ 2 * b ^ 2 * (b - a) := by
    have h1 : (b - a) * (b + a) = 1 := by nlinarith
    nlinarith [sq_nonneg (a - b), mul_pos ha hb]
  nlinarith [mul_pos ha hb, pow_pos hb 3, pow_pos hb 2]

lemma inv_power_sum_succ (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), 1 / Real.sqrt ((i : ℝ) + 1) ^ 3 ≤
      3 - 2 / Real.sqrt ((k : ℝ) + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hstep := inv_sqrt_step (n := (k : ℝ) + 1)
        (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      push_cast
      linarith

lemma inv_power_sum (k : ℕ) :
    ∑ i ∈ Finset.range k, 1 / Real.sqrt ((i : ℝ) + 1) ^ 3 ≤ 3 := by
  cases k with
  | zero => norm_num
  | succ k =>
      have := inv_power_sum_succ k
      have : 0 ≤ 2 / Real.sqrt ((k : ℝ) + 1) := by positivity
      linarith

lemma inv_total_le (i : ℕ) :
    1 / Real.sqrt (total (i + 1)) ≤ Real.sqrt 6 * (1 / Real.sqrt ((i : ℝ) + 1) ^ 3) := by
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hlow : ((i : ℝ) + 1) ^ 3 / 6 ≤ total (i + 1) := by
    have := total_lower (i + 1); push_cast at this; exact this
  have hs : Real.sqrt (((i : ℝ) + 1) ^ 3 / 6) ≤ Real.sqrt (total (i + 1)) := Real.sqrt_le_sqrt hlow
  have hpos : 0 < Real.sqrt (((i : ℝ) + 1) ^ 3 / 6) := Real.sqrt_pos.mpr (by positivity)
  have heq : Real.sqrt (((i : ℝ) + 1) ^ 3 / 6) = Real.sqrt ((i : ℝ) + 1) ^ 3 / Real.sqrt 6 := by
    have hx : ((i : ℝ) + 1) ^ 3 = (Real.sqrt ((i : ℝ) + 1) ^ 3) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hi.le]
    rw [Real.sqrt_div (by positivity), hx, Real.sqrt_sq (by positivity)]
  have h6 : 0 < Real.sqrt 6 := by positivity
  calc 1 / Real.sqrt (total (i + 1)) ≤ 1 / Real.sqrt (((i : ℝ) + 1) ^ 3 / 6) :=
        one_div_le_one_div_of_le hpos hs
    _ = Real.sqrt 6 * (1 / Real.sqrt ((i : ℝ) + 1) ^ 3) := by
        rw [heq]; field_simp

lemma inv_total_sum (k : ℕ) :
    ∑ i ∈ Finset.range k, 1 / Real.sqrt (total (i + 1)) ≤ 3 * Real.sqrt 6 := by
  calc ∑ i ∈ Finset.range k, 1 / Real.sqrt (total (i + 1))
      ≤ ∑ i ∈ Finset.range k, Real.sqrt 6 * (1 / Real.sqrt ((i : ℝ) + 1) ^ 3) :=
        Finset.sum_le_sum fun i _ => inv_total_le i
    _ = Real.sqrt 6 * ∑ i ∈ Finset.range k, 1 / Real.sqrt ((i : ℝ) + 1) ^ 3 := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt 6 * 3 := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact inv_power_sum k
    _ = 3 * Real.sqrt 6 := by ring

end LongTails.Proofs.QuasarCubicPotential
