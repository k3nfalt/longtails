import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

open Finset

namespace LongTails.Proofs.TailEntropyCurvature

def tail (z : ℕ → ℝ) (n k : ℕ) : ℝ := ∑ i ∈ Ico k n, z i

lemma tail_succ (z : ℕ → ℝ) {n k : ℕ} (hk : k < n) : tail z n k = z k + tail z n (k + 1) := by
  unfold tail
  rw [Finset.sum_eq_sum_Ico_succ_bot hk]

lemma tail_self (z : ℕ → ℝ) (n : ℕ) : tail z n n = 0 := by
  simp [tail]

lemma tail_nonneg (z : ℕ → ℝ) (n k : ℕ) (hz : ∀ i < n, 0 ≤ z i) : 0 ≤ tail z n k :=
  Finset.sum_nonneg (fun i hi => hz i (Finset.mem_Ico.mp hi).2)

lemma tail_eq_zero_of_tail_zero (z u : ℕ → ℝ) (n k : ℕ) (hz : ∀ i < n, 0 ≤ z i)
    (hu : ∀ i < n, z i = 0 → u i = 0) (h : tail z n k = 0) : tail u n k = 0 := by
  unfold tail at h ⊢
  have h' := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => hz i (Finset.mem_Ico.mp hi).2)).mp h
  exact Finset.sum_eq_zero (fun i hi => hu i (Finset.mem_Ico.mp hi).2 (h' i hi))

lemma tail_le (z : ℕ → ℝ) {n k : ℕ} (hk : k < n) (hz : ∀ i < n, 0 ≤ z i) :
    z k ≤ tail z n k := by
  rw [tail_succ z hk]
  linarith [tail_nonneg z n (k + 1) hz]

section

variable (n : ℕ) (z u : ℕ → ℝ) (M : ℝ)

noncomputable def ratio (k : ℕ) : ℝ := tail u n k / tail z n k

noncomputable def residual (k : ℕ) : ℝ := u k - z k * ratio n z u k

noncomputable def drift (k : ℕ) : ℝ := ratio n z u 0 - ratio n z u k

noncomputable def potential (k : ℕ) : ℝ :=
  2 * tail z n k * min (tail z n k) M * drift n z u k ^ 2

variable (hz : ∀ k < n, 0 ≤ z k) (hu : ∀ k < n, z k = 0 → u k = 0)

include hz hu

lemma drift_step {k : ℕ} (hk : k < n) :
    tail z n (k + 1) * (drift n z u (k + 1) - drift n z u k) = residual n z u k := by
  have hT := tail_succ z hk
  have hU := tail_succ u hk
  have hT' := tail_nonneg z n (k + 1) hz
  have hd : drift n z u (k + 1) - drift n z u k = ratio n z u k - ratio n z u (k + 1) := by
    unfold drift; ring
  rw [hd]
  unfold residual ratio
  rcases hT'.eq_or_lt with h0 | hpos
  · have hU0 := tail_eq_zero_of_tail_zero z u n (k + 1) hz hu h0.symm
    rw [← h0, zero_mul]
    rw [hT, hU, ← h0, hU0, add_zero, add_zero]
    by_cases hzk : z k = 0
    · rw [hu k hk hzk, hzk]; ring
    · field_simp; ring
  · have hTpos : 0 < tail z n k := by linarith [hz k hk]
    rw [hU]
    field_simp
    rw [hT]
    ring

lemma potential_step {k : ℕ} (hk : k < n) (hM : ∀ k < n, z k ≤ M) :
    z k ^ 2 * drift n z u k ^ 2 + (potential n z u M (k + 1) - potential n z u M k) ≤
      6 * M * (residual n z u k ^ 2 / z k) := by
  have hT := tail_succ z hk
  have hU := tail_succ u hk
  have hT' := tail_nonneg z n (k + 1) hz
  have hstep := drift_step n z u hz hu hk
  set a := z k with ha
  set T := tail z n k
  set T' := tail z n (k + 1)
  set c := drift n z u k
  set c' := drift n z u (k + 1)
  set e := residual n z u k
  by_cases hzk : a = 0
  · have huk := hu k hk hzk
    have hTT : T = T' := by rw [hT, hzk, zero_add]
    have hUU : tail u n k = tail u n (k + 1) := by rw [hU, huk, zero_add]
    have hTT' : tail z n k = tail z n (k + 1) := hTT
    have hcc : c' = c := by
      simp only [c, c', drift, ratio, hUU, hTT']
    unfold potential
    rw [hzk]
    simp only [c, c'] at hcc
    rw [hcc]
    change (0 : ℝ) ^ 2 * c ^ 2 + (2 * T' * min T' M * c ^ 2 - 2 * T * min T M * c ^ 2) ≤ 6 * M * (e ^ 2 / 0)
    rw [hTT]
    simp
  · have hapos : 0 < a := lt_of_le_of_ne (hz k hk) (Ne.symm hzk)
    have haM : a ≤ M := hM k hk
    have haT : T = a + T' := hT
    set μ := min T M with hμ
    set μ' := min T' M with hμ'
    have hμa : a ≤ μ := le_min (by linarith) haM
    have hμ'0 : 0 ≤ μ' := le_min hT' (by linarith)
    have hμ'T : μ' ≤ T' := min_le_left _ _
    have hμ'M : μ' ≤ M := min_le_right _ _
    have hμ'μ : μ' ≤ μ := min_le_min (by linarith) le_rfl
    have hμpos : 0 < μ := lt_of_lt_of_le hapos hμa
    have hnext : potential n z u M (k + 1) ≤ 2 * μ' * T' * c ^ 2 + 4 * μ' * c * e + 2 * e ^ 2 := by
      unfold potential
      change 2 * T' * μ' * c' ^ 2 ≤ _
      have hδ : T' * (c' - c) = e := hstep
      have hsq : μ' * T' * (c' - c) ^ 2 ≤ e ^ 2 := by
        rw [← hδ]
        have h1 : 0 ≤ T' * (c' - c) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hμ'T h1]
      have hexp : 2 * T' * μ' * c' ^ 2 =
          2 * μ' * T' * c ^ 2 + 4 * μ' * c * (T' * (c' - c)) + 2 * (μ' * T' * (c' - c) ^ 2) := by
        ring
      rw [hexp, hδ]
      linarith
    have hcur : potential n z u M k = 2 * T * μ * c ^ 2 := rfl
    rw [hcur]
    have hgoal : a * (a ^ 2 * c ^ 2 + (2 * μ' * T' * c ^ 2 + 4 * μ' * c * e + 2 * e ^ 2 -
        2 * T * μ * c ^ 2)) ≤ 6 * M * e ^ 2 := by
      have h1 : 2 * μ' * T' * c ^ 2 ≤ 2 * μ * T' * c ^ 2 := by
        have : 0 ≤ T' * c ^ 2 := by positivity
        nlinarith
      have h2 : a ^ 2 * c ^ 2 ≤ μ * a * c ^ 2 := by
        have : 0 ≤ a * c ^ 2 := by positivity
        nlinarith
      have h3 : μ * a * (4 * μ' * c * e) ≤ μ ^ 2 * a ^ 2 * c ^ 2 + 4 * μ' ^ 2 * e ^ 2 := by
        nlinarith [sq_nonneg (μ * a * c - 2 * μ' * e)]
      have h4 : 4 * μ' ^ 2 * e ^ 2 ≤ 4 * μ * M * e ^ 2 := by
        have : 0 ≤ e ^ 2 := sq_nonneg e
        have h5 : μ' ^ 2 ≤ μ * M := by nlinarith
        nlinarith
      have h6 : a * (4 * μ' * c * e) ≤ μ * a ^ 2 * c ^ 2 + 4 * M * e ^ 2 := by
        have h7 : μ * (a * (4 * μ' * c * e)) ≤ μ * (μ * a ^ 2 * c ^ 2 + 4 * M * e ^ 2) := by
          nlinarith
        exact le_of_mul_le_mul_left h7 hμpos
      have h8 : a * (2 * e ^ 2) ≤ M * (2 * e ^ 2) := by
        have : 0 ≤ 2 * e ^ 2 := by positivity
        nlinarith
      have h9 : a * (a ^ 2 * c ^ 2 + (2 * μ' * T' * c ^ 2 - 2 * T * μ * c ^ 2)) ≤
          a * (- μ * a * c ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hapos.le
        rw [haT]
        nlinarith
      nlinarith
    have hkey : a ^ 2 * c ^ 2 + (2 * μ' * T' * c ^ 2 + 4 * μ' * c * e + 2 * e ^ 2 -
        2 * T * μ * c ^ 2) ≤ 6 * M * e ^ 2 / a := by
      rw [le_div_iff₀ hapos]
      linarith
    have hrhs : 6 * M * (e ^ 2 / a) = 6 * M * e ^ 2 / a := by ring
    rw [hrhs]
    linarith

theorem curvature_bound (hM : ∀ k < n, z k ≤ M) :
    ∑ k ∈ range n, (u k - ratio n z u 0 * z k) ^ 2 ≤
      14 * M * ∑ k ∈ range n, residual n z u k ^ 2 / z k := by
  have hdecomp (k : ℕ) : u k - ratio n z u 0 * z k = residual n z u k - z k * drift n z u k := by
    unfold residual drift; ring
  have htel : ∑ k ∈ range n, (potential n z u M (k + 1) - potential n z u M k) =
      potential n z u M n - potential n z u M 0 := Finset.sum_range_sub _ n
  have hp0 : potential n z u M 0 = 0 := by simp [potential, drift]
  have hpn : potential n z u M n = 0 := by simp [potential, tail_self]
  have hsteps := Finset.sum_le_sum (fun k hk => potential_step n z u M hz hu
    (Finset.mem_range.mp hk) hM)
  rw [Finset.sum_add_distrib, htel, hp0, hpn, sub_zero, add_zero, ← Finset.mul_sum] at hsteps
  have hres (k : ℕ) (hk : k < n) : residual n z u k ^ 2 ≤ M * (residual n z u k ^ 2 / z k) := by
    by_cases hzk : z k = 0
    · have : residual n z u k = 0 := by
        unfold residual; rw [hu k hk hzk, hzk]; ring
      rw [this]; simp
    · have hpos : 0 < z k := lt_of_le_of_ne (hz k hk) (Ne.symm hzk)
      have he : residual n z u k ^ 2 = z k * (residual n z u k ^ 2 / z k) := by
        field_simp
      have hq : 0 ≤ residual n z u k ^ 2 / z k := by positivity
      calc residual n z u k ^ 2 = z k * (residual n z u k ^ 2 / z k) := he
        _ ≤ M * (residual n z u k ^ 2 / z k) := mul_le_mul_of_nonneg_right (hM k hk) hq
  have hres_sum := Finset.sum_le_sum (fun k hk => hres k (Finset.mem_range.mp hk))
  rw [← Finset.mul_sum] at hres_sum
  have hpoint (k : ℕ) : (u k - ratio n z u 0 * z k) ^ 2 ≤
      2 * residual n z u k ^ 2 + 2 * (z k ^ 2 * drift n z u k ^ 2) := by
    rw [hdecomp]
    nlinarith [sq_nonneg (residual n z u k + z k * drift n z u k)]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ range n) => hpoint k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  linarith

end

end LongTails.Proofs.TailEntropyCurvature
