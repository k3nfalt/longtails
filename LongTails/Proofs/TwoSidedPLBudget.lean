import LongTails.Proofs.TwoSidedPLSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset

namespace OracleTemplate.TwoSidedPL

lemma pow_le_exp_window {C : ℝ} (hC : 1 ≤ C) (n : ℕ) :
    (1 - 1 / C) ^ n ≤ Real.exp (-(n / C)) := by
  have hC0 : 0 < C := by linarith
  have h0 : 0 ≤ 1 - 1 / C := by rw [sub_nonneg, div_le_one hC0]; exact hC
  have h1 : 1 - 1 / C ≤ Real.exp (-(1 / C)) := by
    have := Real.add_one_le_exp (-(1 / C)); linarith
  calc (1 - 1 / C) ^ n ≤ Real.exp (-(1 / C)) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp (-(n / C)) := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma exp_neg_two_le : Real.exp (-2) ≤ 1 / 4 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h2 : 4 ≤ Real.exp 2 := by
    rw [e]
    have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
    have := mul_le_mul h1 h1 (by norm_num) (by linarith)
    linarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 2) (by norm_num)]
  linarith

lemma window_decay {C Δ ε : ℝ} {n : ℕ} (hC : 1 ≤ C) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hn : C * (2 + Real.log (1 + Δ / ε)) ≤ n) : (1 - 1 / C) ^ n * Δ ≤ ε / 4 := by
  have hC0 : 0 < C := by linarith
  have hΔε : 0 ≤ Δ / ε := by positivity
  have hpos : 0 < 1 + Δ / ε := by linarith
  have h1 := pow_le_exp_window hC n
  have h2 : Real.exp (-((n : ℝ) / C)) ≤ Real.exp (-2) / (1 + Δ / ε) := by
    rw [le_div_iff₀ hpos, ← Real.exp_log hpos, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : 2 + Real.log (1 + Δ / ε) ≤ n / C := by rw [le_div_iff₀ hC0]; linarith
    linarith
  have h3 : Real.exp (-2) / (1 + Δ / ε) * Δ ≤ ε / 4 := by
    have he := exp_neg_two_le
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have e : (1 + Δ / ε) * ε = ε + Δ := by field_simp
    have h4 : Real.exp (-2) * Δ ≤ 1 / 4 * Δ := mul_le_mul_of_nonneg_right he hΔ
    have h5 : ε / 4 * (1 + Δ / ε) = (ε + Δ) / 4 := by rw [← e]; ring
    rw [h5]
    linarith
  calc (1 - 1 / C) ^ n * Δ ≤ Real.exp (-2) / (1 + Δ / ε) * Δ :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hΔ
    _ ≤ ε / 4 := h3

lemma final_bound {L μx μy σ Δ ε Δ0 K τ C : ℝ} {n : ℕ} (hμx : 0 < μx) (hμxL : μx ≤ L)
    (hμy : 0 < μy) (hμyL : μy ≤ L) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hΔ0Δ : Δ0 ≤ Δ) (hK : K = 3 + 2 ^ 24 * L * σ ^ 2 / (μx * μy * ε)) (hτ : τ = 1 / (L * K))
    (hC : C = 2 ^ 18 * L / (μx * μy * τ))
    (hn : n = ⌈2 ^ 18 * L ^ 2 / (μx * μy) * K * (2 + Real.log (1 + Δ / ε))⌉₊) :
    (2 * C * ((1 - 1 / C) ^ n * Δ0 + ∑ t ∈ range n, (1 - 1 / C) ^ (n - 1 - t) *
        (9 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx / C + 2 * L * τ ^ 2 * (σ ^ 2 + σ ^ 2)) +
        (n + 1) * (2 * L * τ ^ 2 * (σ ^ 2 + σ ^ 2))) +
      (n + 1) * (12 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx)) / (n + 1) ≤ ε := by
  have hL : 0 < L := lt_of_lt_of_le hμx hμxL
  have hm : 0 < μx * μy * ε := by positivity
  have hq : 0 ≤ 2 ^ 24 * L * σ ^ 2 / (μx * μy * ε) := by positivity
  have hK3 : 3 ≤ K := by rw [hK]; linarith
  have hK0 : 0 < K := by linarith
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hLτK : L * τ = 1 / K := by rw [hτ]; field_simp
  have hCe : C = 2 ^ 18 * L ^ 2 * K / (μx * μy) := by rw [hC, hτ]; field_simp
  have hC1 : 1 ≤ C := by
    rw [hCe, le_div_iff₀ (by positivity)]
    have h1 : μx * μy ≤ L * L := mul_le_mul hμxL hμyL hμy.le hL.le
    have h2 : L * L * 1 ≤ L ^ 2 * K := by nlinarith
    have h3 : 0 ≤ L ^ 2 * K := by positivity
    linarith
  have hC0 : 0 < C := by linarith
  have hΔε : 0 ≤ Δ / ε := by positivity
  have hlog : 0 ≤ Real.log (1 + Δ / ε) := Real.log_nonneg (by linarith)
  have hnC : C * (2 + Real.log (1 + Δ / ε)) ≤ (n : ℝ) := by
    have h := Nat.le_ceil (2 ^ 18 * L ^ 2 / (μx * μy) * K * (2 + Real.log (1 + Δ / ε)))
    rw [← hn] at h
    have e : C * (2 + Real.log (1 + Δ / ε)) =
        2 ^ 18 * L ^ 2 / (μx * μy) * K * (2 + Real.log (1 + Δ / ε)) := by rw [hCe]; ring
    rw [e]; exact h
  have hCn : C ≤ (n : ℝ) + 1 := by
    have : C * 1 ≤ C * (2 + Real.log (1 + Δ / ε)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0.le
    linarith
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hρ0 : 0 ≤ 1 - 1 / C := by rw [sub_nonneg, div_le_one hC0]; exact hC1
  have hgeo := geometric_window_le hC1 rfl n
  have hexp := window_decay hC1 hΔ hε hnC
  have hKx : 2 ^ 24 * L * σ ^ 2 ≤ K * (μx * μy * ε) := by
    have h1 : 2 ^ 24 * L * σ ^ 2 / (μx * μy * ε) * (μx * μy * ε) = 2 ^ 24 * L * σ ^ 2 := by
      field_simp
    have h2 : 2 ^ 24 * L * σ ^ 2 / (μx * μy * ε) ≤ K := by rw [hK]; linarith
    have := mul_le_mul_of_nonneg_right h2 hm.le
    linarith
  set Q1 := 30 * σ ^ 2 / (μx * K ^ 2) with hQ1
  set Q2 := 2 ^ 22 * L * σ ^ 2 / (μx * μy * K) with hQ2
  have hQ1b : Q1 ≤ ε / 4 := by
    rw [hQ1, div_le_iff₀ (by positivity)]
    have h1 : μy * (2 ^ 24 * σ ^ 2) ≤ μy * (K * μx * ε) := by
      have := mul_le_mul_of_nonneg_right hμyL (by positivity : (0 : ℝ) ≤ 2 ^ 24 * σ ^ 2)
      linarith
    have h2 : 2 ^ 24 * σ ^ 2 ≤ K * μx * ε := le_of_mul_le_mul_left h1 hμy
    have h3 : K * (2 ^ 24 * σ ^ 2) ≤ K * (K * μx * ε) := mul_le_mul_of_nonneg_left h2 hK0.le
    have h4 : 3 * (2 ^ 24 * σ ^ 2) ≤ K * (2 ^ 24 * σ ^ 2) :=
      mul_le_mul_of_nonneg_right hK3 (by positivity)
    have h5 : 0 ≤ σ ^ 2 := sq_nonneg σ
    linarith
  have hQ2b : Q2 ≤ ε / 4 := by
    rw [hQ2, div_le_iff₀ (by positivity)]
    linarith
  have hbN : 9 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx = 9 / 30 * Q1 := by
    rw [hQ1]
    have : L ^ 2 * τ ^ 2 = 1 / K ^ 2 := by rw [show L ^ 2 * τ ^ 2 = (L * τ) ^ 2 by ring, hLτK]; ring
    rw [show 9 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx = 9 * (L ^ 2 * τ ^ 2) * σ ^ 2 / μx by ring, this]
    field_simp
    try ring
  have hNb : 12 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx = 12 / 30 * Q1 := by
    have : 12 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx = 4 / 3 * (9 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx) := by ring
    rw [this, hbN]; ring
  have hCns : C * (2 * L * τ ^ 2 * (σ ^ 2 + σ ^ 2)) = 1 / 4 * Q2 := by
    rw [hQ2, hCe]
    have : L * τ ^ 2 = τ / K := by
      rw [show L * τ ^ 2 = (L * τ) * τ by ring, hLτK]; ring
    rw [show 2 * L * τ ^ 2 * (σ ^ 2 + σ ^ 2) = 4 * (L * τ ^ 2) * σ ^ 2 by ring, this, hτ]
    field_simp
    try ring
  set bN := 9 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx with hbNdef
  set ns := 2 * L * τ ^ 2 * (σ ^ 2 + σ ^ 2) with hnsdef
  set Nb := 12 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx with hNbdef
  have hns0 : 0 ≤ ns := by rw [hnsdef]; positivity
  have hbN0 : 0 ≤ bN := by rw [hbNdef]; positivity
  have hS : ∑ t ∈ range n, (1 - 1 / C) ^ (n - 1 - t) * (bN / C + ns) ≤ bN + C * ns := by
    rw [← Finset.sum_mul]
    have h := mul_le_mul_of_nonneg_right hgeo (by positivity : (0 : ℝ) ≤ bN / C + ns)
    have e : C * (bN / C + ns) = bN + C * ns := by field_simp
    linarith
  rw [div_le_iff₀ hn1]
  have hA1 : 2 * C * ((1 - 1 / C) ^ n * Δ0) ≤ 2 * C * ((1 - 1 / C) ^ n * Δ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔ0Δ (pow_nonneg hρ0 n)) (by linarith)
  have hA2 : 2 * C * ((1 - 1 / C) ^ n * Δ) ≤ 2 * ((n : ℝ) + 1) * ((1 - 1 / C) ^ n * Δ) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (pow_nonneg hρ0 n) hΔ)
  have hA3 : 2 * ((n : ℝ) + 1) * ((1 - 1 / C) ^ n * Δ) ≤ 2 * ((n : ℝ) + 1) * (ε / 4) :=
    mul_le_mul_of_nonneg_left hexp (by linarith)
  have hB1 : 2 * C * (∑ t ∈ range n, (1 - 1 / C) ^ (n - 1 - t) * (bN / C + ns)) ≤
      2 * C * (bN + C * ns) := mul_le_mul_of_nonneg_left hS (by linarith)
  have hB2 : 2 * C * bN ≤ 2 * ((n : ℝ) + 1) * bN := mul_le_mul_of_nonneg_right (by linarith) hbN0
  have hB3 : 2 * C * (C * ns) ≤ 2 * ((n : ℝ) + 1) * (C * ns) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hC0.le hns0)
  have hB4 : ((n : ℝ) + 1) * (Q1 + Q2) ≤ ((n : ℝ) + 1) * (ε / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hn1.le
  have e1 : ((n : ℝ) + 1) * bN = ((n : ℝ) + 1) * (9 / 30 * Q1) := by rw [hbN]
  have e2 : ((n : ℝ) + 1) * Nb = ((n : ℝ) + 1) * (12 / 30 * Q1) := by rw [hNb]
  have e3 : ((n : ℝ) + 1) * (C * ns) = ((n : ℝ) + 1) * (1 / 4 * Q2) := by rw [hCns]
  have e4 : 2 * C * ((n + 1) * ns) = 2 * ((n : ℝ) + 1) * (C * ns) := by ring
  linarith

end OracleTemplate.TwoSidedPL
