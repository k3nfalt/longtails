import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

open Finset

namespace OracleTemplate.ReshuffledHarmonic

noncomputable def H (n : ℕ) : ℝ := harmonic n

lemma H_eq_sum (n : ℕ) : H n = ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ)⁻¹ := by
  simp [H, harmonic]

lemma H_zero : H 0 = 0 := by simp [H]

lemma H_succ (n : ℕ) : H (n + 1) = H n + ((n + 1 : ℕ) : ℝ)⁻¹ := by
  simp [H, harmonic_succ]

lemma H_nonneg (n : ℕ) : 0 ≤ H n := by
  rw [H_eq_sum]
  exact sum_nonneg fun j _ => by positivity

lemma H_mono : Monotone H := by
  intro m n hmn
  rw [H_eq_sum, H_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) (fun j _ _ => by positivity)

lemma one_le_H {n : ℕ} (hn : 0 < n) : 1 ≤ H n := by
  have h := H_mono (show 1 ≤ n by omega)
  simpa [H, harmonic] using h

lemma H_pos {n : ℕ} (hn : 0 < n) : 0 < H n := lt_of_lt_of_le zero_lt_one (one_le_H hn)

lemma H_log (n : ℕ) : H n ≤ 1 + Real.log n := harmonic_le_one_add_log n

noncomputable def W (r : ℕ) : ℝ := H r / r

lemma W_nonneg (r : ℕ) : 0 ≤ W r := div_nonneg (H_nonneg r) (Nat.cast_nonneg r)

lemma W_pos {r : ℕ} (hr : 0 < r) : 0 < W r :=
  div_pos (H_pos hr) (Nat.cast_pos.mpr hr)

lemma mul_W {r : ℕ} (hr : 0 < r) : (r : ℝ) * W r = H r := by
  rw [W, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr))]

lemma W_one : W 1 = 1 := by simp [W, H, harmonic]

lemma W_slack {r : ℕ} (hr : 0 < r) :
    W (r + 1) - r * (W r - W (r + 1)) = ((r + 1 : ℕ) : ℝ)⁻¹ := by
  have h1 := mul_W hr
  have h2 := mul_W (Nat.zero_lt_succ r)
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h2
  rw [H_succ] at h2
  linarith

lemma W_succ_le {r : ℕ} (hr : 0 < r) : W (r + 1) ≤ W r := by
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hH := one_le_H hr
  have hsl := W_slack hr
  have hmul := mul_W hr
  have hrec := H_succ r
  have hmul1 := mul_W (Nat.zero_lt_succ r)
  have hinv : ((r + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))
  have hprod : (r : ℝ) * ((r + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one (by positivity)).2 (by norm_num)
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hmul1
  have hiw : ((r + 1 : ℕ) : ℝ)⁻¹ ≤ W r := by
    have hh : (r : ℝ) * ((r + 1 : ℕ) : ℝ)⁻¹ ≤ r * W r := by
      rw [hmul]
      exact hprod.trans hH
    exact le_of_mul_le_mul_left hh hr'
  nlinarith

lemma W_antitone_on : AntitoneOn W (Set.Ici 1) := by
  intro a ha b hb hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (W_succ_le (by have := ha; simp only [Set.mem_Ici] at this; omega)).trans (ih (by have := ha; simp only [Set.mem_Ici] at this ⊢; omega))

lemma W_le_two_succ {r : ℕ} (hr : 0 < r) : W r ≤ 2 * W (r + 1) := by
  have hm := H_mono (Nat.le_succ r)
  have hmul := mul_W hr
  have hmul1 := mul_W (Nat.zero_lt_succ r)
  have hnon := W_nonneg (r + 1)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hmul1
  nlinarith

lemma W_slack_lower {r T : ℕ} (hr : 0 < r) (hrT : r + 1 ≤ T) :
    W (r + 1) / H T ≤ W (r + 1) - r * (W r - W (r + 1)) := by
  rw [W_slack hr]
  have hT : 0 < H T := H_pos (by omega)
  have hmono := H_mono hrT
  rw [div_le_iff₀ hT, W]
  simpa [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right hmono (by positivity : 0 ≤ ((r + 1 : ℕ) : ℝ)⁻¹)

lemma sum_W_le (T : ℕ) : ∑ j ∈ range T, W (j + 1) ≤ H T ^ 2 := by
  calc
    ∑ j ∈ range T, W (j + 1) ≤ ∑ j ∈ range T, H T * ((j + 1 : ℕ) : ℝ)⁻¹ := by
      apply sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_right (H_mono (by have := mem_range.mp hj; omega))
        (by positivity)
    _ = H T * H T := by rw [← mul_sum, ← H_eq_sum]
    _ = H T ^ 2 := by ring

noncomputable def V (c : ℝ) (r : ℕ) : ℝ := (c + H r) / r

lemma V_eq (c : ℝ) (r : ℕ) : V c r = c / r + W r := by
  simp [V, W, add_div]

lemma mul_V (c : ℝ) {r : ℕ} (hr : 0 < r) : (r : ℝ) * V c r = c + H r := by
  rw [V, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr))]

lemma V_nonneg {c : ℝ} (hc : 0 ≤ c) (r : ℕ) : 0 ≤ V c r :=
  div_nonneg (add_nonneg hc (H_nonneg r)) (Nat.cast_nonneg r)

lemma V_pos {c : ℝ} (hc : 0 ≤ c) {r : ℕ} (hr : 0 < r) : 0 < V c r :=
  div_pos (add_pos_of_nonneg_of_pos hc (H_pos hr)) (Nat.cast_pos.mpr hr)

lemma V_slack (c : ℝ) {r : ℕ} (hr : 0 < r) :
    V c (r + 1) - r * (V c r - V c (r + 1)) = ((r + 1 : ℕ) : ℝ)⁻¹ := by
  have h1 := mul_V c hr
  have h2 := mul_V c (Nat.zero_lt_succ r)
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h2
  rw [H_succ] at h2
  linarith

lemma V_succ_le {c : ℝ} (hc : 0 ≤ c) {r : ℕ} (hr : 0 < r) : V c (r + 1) ≤ V c r := by
  rw [V_eq, V_eq]
  apply add_le_add _ (W_succ_le hr)
  exact div_le_div_of_nonneg_left hc (Nat.cast_pos.mpr hr) (by exact_mod_cast Nat.le_succ r)

lemma V_antitone_on {c : ℝ} (hc : 0 ≤ c) : AntitoneOn (V c) (Set.Ici 1) := by
  intro a ha b hb hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (V_succ_le hc (by have := ha; simp only [Set.mem_Ici] at this; omega)).trans
      (ih (by have := ha; simp only [Set.mem_Ici] at this ⊢; omega))

lemma V_le_two_succ {c : ℝ} (hc : 0 ≤ c) {r : ℕ} (hr : 0 < r) :
    V c r ≤ 2 * V c (r + 1) := by
  have hm := H_mono (Nat.le_succ r)
  have hmul := mul_V c hr
  have hmul1 := mul_V c (Nat.zero_lt_succ r)
  have hnon := V_nonneg hc (r + 1)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hmul1
  nlinarith

lemma V_slack_lower {r T : ℕ} (hr : 0 < r) (hrT : r + 1 ≤ T) :
    V (H T) (r + 1) / (2 * H T) ≤
      V (H T) (r + 1) - r * (V (H T) r - V (H T) (r + 1)) := by
  rw [V_slack _ hr]
  have hT : 0 < H T := H_pos (by omega)
  have hmono := H_mono hrT
  rw [div_le_iff₀ (by positivity : 0 < 2 * H T), V]
  have hm := mul_le_mul_of_nonneg_right (show H T + H (r + 1) ≤ 2 * H T by linarith)
    (by positivity : 0 ≤ ((r + 1 : ℕ) : ℝ)⁻¹)
  simpa [div_eq_mul_inv, mul_comm] using hm

lemma V_initial (T : ℕ) : V (H T) T = 2 * H T / T := by
  unfold V
  congr 1
  ring

lemma V_terminal (T : ℕ) : V (H T) 1 = H T + 1 := by simp [V, H, harmonic]

lemma sum_V_le (T : ℕ) :
    ∑ j ∈ range T, V (H T) (j + 1) ≤ 2 * H T ^ 2 := by
  simp_rw [V_eq, div_eq_mul_inv]
  rw [sum_add_distrib, ← mul_sum, ← H_eq_sum]
  have h := sum_W_le T
  nlinarith

lemma V_shift_le {c : ℝ} (hc : 0 ≤ c) {q m j : ℕ} (hq : 0 < q) (hj : j ≤ m) :
    V c (q + j) ≤ ((m + 1 : ℕ) : ℝ) / (j + 1) * V c (q + m) := by
  have hqj : (0 : ℝ) < q + j := by exact_mod_cast (by omega : 0 < q + j)
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj
  have hnon := V_nonneg hc (q + m)
  have hm := H_mono (show q + j ≤ q + m by omega)
  have hmul0 := mul_V c (show 0 < q + j by omega)
  have hmul1 := mul_V c (show 0 < q + m by omega)
  simp only [Nat.cast_add, Nat.cast_one] at hmul0 hmul1 ⊢
  have hm' : (q + j : ℝ) * V c (q + j) ≤ (q + m) * V c (q + m) := by linarith
  have hpoly : (j + 1 : ℝ) * (q + m) ≤ (q + j) * (m + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hjm)]
  have hh := mul_le_mul_of_nonneg_right hpoly hnon
  have hh' := mul_le_mul_of_nonneg_left hm' hj1.le
  have hf : (q + j : ℝ) * ((j + 1) * V c (q + j)) ≤
      (q + j) * ((m + 1) * V c (q + m)) := by nlinarith
  have hres := le_of_mul_le_mul_left hf hqj
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hj1).2
  simpa [mul_comm] using hres

lemma sum_V_shift_le {c : ℝ} (hc : 0 ≤ c) {q m : ℕ} (hq : 0 < q) :
    ∑ j ∈ range m, V c (q + j) ≤ (m + 1) * H m * V c (q + m) := by
  calc
    ∑ j ∈ range m, V c (q + j) ≤
        ∑ j ∈ range m, (((m + 1 : ℕ) : ℝ) / (j + 1) * V c (q + m)) := by
      apply sum_le_sum
      intro j hj
      exact V_shift_le hc hq (Nat.le_of_lt (mem_range.mp hj))
    _ = (m + 1) * H m * V c (q + m) := by
      simp only [div_eq_mul_inv, ← sum_mul, ← mul_sum]
      rw [show (∑ j ∈ range m, ((j : ℝ) + 1)⁻¹) = H m by
        rw [H_eq_sum]; simp only [Nat.cast_add, Nat.cast_one]]
      push_cast
      ring

lemma sum_V_epoch_le {c : ℝ} (hc : 0 ≤ c) {q m n : ℕ} (hq : 0 < q) (hm : m < n) :
    ∑ j ∈ range m, V c (q + j) ≤ n * H n * V c (q + m) := by
  have hmn : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm
  have hH := H_mono (Nat.le_of_lt hm)
  have hp := mul_le_mul hmn hH (H_nonneg m) (Nat.cast_nonneg n)
  exact (sum_V_shift_le hc hq).trans
    (mul_le_mul_of_nonneg_right hp (V_nonneg hc _))

noncomputable def weight (T t : ℕ) : ℝ := V (H T) (T - t)

lemma weight_pos {T t : ℕ} (ht : t < T) : 0 < weight T t :=
  V_pos (H_nonneg T) (by omega)

lemma weight_mono {T t : ℕ} (ht : t + 1 < T) : weight T t ≤ weight T (t + 1) := by
  have h := V_succ_le (H_nonneg T) (r := T - (t + 1)) (by omega)
  simpa only [weight, show T - (t + 1) + 1 = T - t by omega] using h

lemma weight_adjacent {T t : ℕ} (ht : t + 1 < T) : weight T (t + 1) ≤ 2 * weight T t := by
  have h := V_le_two_succ (H_nonneg T) (r := T - (t + 1)) (by omega)
  simpa only [weight, show T - (t + 1) + 1 = T - t by omega] using h

lemma weight_initial (T : ℕ) : weight T 0 = 2 * H T / T := by
  simpa [weight] using V_initial T

lemma weight_terminal {T : ℕ} (hT : 0 < T) : weight T (T - 1) = H T + 1 := by
  rw [weight, show T - (T - 1) = 1 by omega, V_terminal]

lemma weight_sum_le (T : ℕ) : ∑ t ∈ range T, weight T t ≤ 2 * H T ^ 2 := by
  have he : (∑ t ∈ range T, weight T t) = ∑ t ∈ range T, V (H T) (t + 1) := by
    rw [← sum_range_reflect (fun t => V (H T) (t + 1)) T]
    apply sum_congr rfl
    intro t ht
    unfold weight
    congr 1
    have := mem_range.mp ht
    omega
  rw [he]
  exact sum_V_le T

lemma weight_kernel {T t : ℕ} (ht : t < T) :
    (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) ≤ weight T t := by
  by_cases hlt : t + 1 < T
  · have hs := V_slack (H T) (r := T - (t + 1)) (by omega)
    have hi : 0 ≤ (((T - (t + 1) + 1 : ℕ) : ℝ)⁻¹) := by positivity
    rw [show T - (t + 1) + 1 = T - t by omega] at hs hi
    change weight T t - (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) = _ at hs
    linarith
  · have he : T - (t + 1) = 0 := by omega
    rw [he, Nat.cast_zero, zero_mul]
    exact (weight_pos ht).le

lemma weight_slack {T t : ℕ} (ht : t + 1 < T) :
    weight T t / (2 * H T) ≤
      weight T t - (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) := by
  have hs := V_slack_lower (r := T - (t + 1)) (T := T) (by omega) (by omega)
  simpa only [weight, show T - (t + 1) + 1 = T - t by omega] using hs

lemma weight_kernel_nonneg {T t : ℕ} (ht : t < T) :
    0 ≤ (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) := by
  by_cases hlt : t + 1 < T
  · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (weight_mono hlt))
  · have he : T - (t + 1) = 0 := by omega
    simp [he]

end OracleTemplate.ReshuffledHarmonic
