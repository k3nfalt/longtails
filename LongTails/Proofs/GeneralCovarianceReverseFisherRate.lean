import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedSectionVars false

namespace LongTails.Proofs.GeneralCovarianceReverseFisherRate

variable {V : ℕ → ℝ} {a N : ℝ}

lemma min_nonneg_of (h : 0 ≤ V k) (hN : 0 < N) : 0 ≤ min (V k / 2) (V k ^ 2 / (4 * N)) :=
  le_min (by linarith) (by positivity)

lemma step_le (ha0 : 0 < a) (hN : 0 < N) (h0 : ∀ k, 0 ≤ V k)
    (hrec : ∀ k, V (k + 1) ≤ V k - a * min (V k / 2) (V k ^ 2 / (4 * N))) (k : ℕ) :
    V (k + 1) ≤ V k := by
  have := hrec k
  have := mul_nonneg ha0.le (min_nonneg_of (h0 k) hN)
  linarith

lemma antitone_of (ha0 : 0 < a) (hN : 0 < N) (h0 : ∀ k, 0 ≤ V k)
    (hrec : ∀ k, V (k + 1) ≤ V k - a * min (V k / 2) (V k ^ 2 / (4 * N))) : Antitone V :=
  antitone_nat_of_succ_le (step_le ha0 hN h0 hrec)

lemma phase_one (ha0 : 0 < a) (hN : 0 < N) (h0 : ∀ k, 0 ≤ V k)
    (hrec : ∀ k, V (k + 1) ≤ V k - a * min (V k / 2) (V k ^ 2 / (4 * N))) (k : ℕ) :
    V k ≤ max (2 * N) ((1 - a / 2) ^ k * V 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases le_or_gt (V k) (2 * N) with hk | hk
    · exact le_max_of_le_left ((step_le ha0 hN h0 hrec k).trans hk)
    · have hmin : min (V k / 2) (V k ^ 2 / (4 * N)) = V k / 2 := by
        apply min_eq_left
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      have h1 := hrec k
      rw [hmin] at h1
      have hk' : V k ≤ (1 - a / 2) ^ k * V 0 := by
        rcases le_max_iff.mp ih with h | h
        · linarith
        · exact h
      refine le_max_of_le_right ?_
      rw [pow_succ]
      have : V (k + 1) ≤ (1 - a / 2) * V k := by linarith
      by_cases hc : 0 ≤ 1 - a / 2
      · calc V (k + 1) ≤ (1 - a / 2) * V k := this
          _ ≤ (1 - a / 2) * ((1 - a / 2) ^ k * V 0) := mul_le_mul_of_nonneg_left hk' hc
          _ = _ := by ring
      · have : (1 - a / 2) * V k < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
        linarith [h0 (k + 1)]

lemma phase_two (ha0 : 0 < a) (ha1 : a ≤ 1) (hN : 0 < N) (h0 : ∀ k, 0 ≤ V k)
    (hrec : ∀ k, V (k + 1) ≤ V k - a * min (V k / 2) (V k ^ 2 / (4 * N))) {j : ℕ}
    (hj : V j ≤ 2 * N) (s : ℕ) :
    V (j + s) ≤ V j / (1 + a / (4 * N) * s * V j) := by
  set b := a / (4 * N) with hb
  have hb0 : 0 < b := by positivity
  have hVj := h0 j
  induction s with
  | zero => simp
  | succ s ih =>
    set w := V j / (1 + b * s * V j)
    have hden : 0 < 1 + b * s * V j := by positivity
    have hw0 : 0 ≤ w := div_nonneg hVj hden.le
    have hwj : w ≤ V j := div_le_self hVj
      (by nlinarith [mul_nonneg (mul_nonneg hb0.le (Nat.cast_nonneg s)) hVj])
    have hv := h0 (j + s)
    have hvle : V (j + s) ≤ 2 * N :=
      ((antitone_of ha0 hN h0 hrec) (Nat.le_add_right j s)).trans hj
    have hmin : min (V (j + s) / 2) (V (j + s) ^ 2 / (4 * N)) = V (j + s) ^ 2 / (4 * N) := by
      apply min_eq_right
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h1 := hrec (j + s)
    rw [hmin] at h1
    have h2 : V (j + s + 1) ≤ V (j + s) - b * V (j + s) ^ 2 := by
      rw [hb]; convert h1 using 2; ring
    have hmono : V (j + s) - b * V (j + s) ^ 2 ≤ w - b * w ^ 2 := by
      have hsum : b * (w + V (j + s)) ≤ 1 := by
        have : w + V (j + s) ≤ 4 * N := by linarith
        calc b * (w + V (j + s)) ≤ b * (4 * N) := mul_le_mul_of_nonneg_left this hb0.le
          _ = a := by rw [hb]; field_simp
          _ ≤ 1 := ha1
      nlinarith [mul_nonneg (sub_nonneg.mpr ih) (sub_nonneg.mpr hsum)]
    have hfin : w - b * w ^ 2 ≤ V j / (1 + b * ((s + 1 : ℕ) : ℝ) * V j) := by
      have e : V j / (1 + b * ((s + 1 : ℕ) : ℝ) * V j) = w / (1 + b * w) := by
        simp only [w]
        push_cast
        field_simp
        ring
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hb0.le hb0.le) (pow_nonneg hw0 3)]
    rw [show j + (s + 1) = j + s + 1 by ring]
    linarith

lemma one_sub_pow_le_exp {y : ℝ} (hy0 : 0 ≤ 1 - y) (k : ℕ) :
    (1 - y) ^ k ≤ Real.exp (-(y * k)) := by
  calc (1 - y) ^ k ≤ Real.exp (-y) ^ k :=
        pow_le_pow_left₀ hy0 (by linarith [Real.add_one_le_exp (-y)]) k
    _ = Real.exp (-(y * k)) := by rw [← Real.exp_nat_mul]; ring_nf

theorem rate (ha0 : 0 < a) (ha1 : a ≤ 1) (hN : 0 < N) (h0 : ∀ k, 0 ≤ V k)
    (hrec : ∀ k, V (k + 1) ≤ V k - a * min (V k / 2) (V k ^ 2 / (4 * N))) {B ε : ℝ}
    (hB : 1 ≤ B) (hV0 : V 0 ≤ 2 * N * B) (hε : 0 < ε) (K : ℕ)
    (hK : 2 / a * Real.log B + 4 * N / (a * ε) + 1 ≤ K) : V K ≤ ε := by
  set K1 := ⌈2 / a * Real.log B⌉₊
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hK1 : (K1 : ℝ) ≤ 2 / a * Real.log B + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hK1' : 2 / a * Real.log B ≤ K1 := Nat.le_ceil _
  have hK12 : K1 ≤ K := by
    have : (K1 : ℝ) ≤ K := by
      have : 0 < 4 * N / (a * ε) := by positivity
      linarith
    exact_mod_cast this
  set K2 := K - K1
  have hK2 : 4 * N / (a * ε) ≤ K2 := by
    have : (K2 : ℝ) = K - K1 := by simp [K2, Nat.cast_sub hK12]
    rw [this]; linarith
  have hV1 : V K1 ≤ 2 * N := by
    have hp := phase_one ha0 hN h0 hrec K1
    refine (max_le le_rfl ?_).trans' hp
    have hc : 0 ≤ 1 - a / 2 := by linarith
    · have he := one_sub_pow_le_exp hc K1
      have hexp : Real.exp (-(a / 2 * K1)) ≤ 1 / B := by
        rw [one_div, ← Real.exp_log (by linarith : (0 : ℝ) < B), ← Real.exp_neg]
        apply Real.exp_le_exp.mpr
        have : Real.log B ≤ a / 2 * K1 := by
          have := mul_le_mul_of_nonneg_left hK1' (by positivity : 0 ≤ a / 2)
          rw [← mul_assoc, show a / 2 * (2 / a) = 1 by field_simp, one_mul] at this
          exact this
        linarith
      calc (1 - a / 2) ^ K1 * V 0 ≤ (1 / B) * (2 * N * B) :=
            mul_le_mul (he.trans hexp) hV0 (h0 0) (by positivity)
        _ = 2 * N := by field_simp
  have hp2 := phase_two ha0 ha1 hN h0 hrec hV1 K2
  rw [show K1 + K2 = K by omega] at hp2
  refine hp2.trans ?_
  rcases (h0 K1).lt_or_eq with hpos | hzero
  · have hK2pos : (0 : ℝ) < K2 := lt_of_lt_of_le (by positivity) hK2
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ a / (4 * N) * K2 * ε := by
      rw [div_le_iff₀ (by positivity)] at hK2
      have e : a / (4 * N) * K2 * ε = K2 * (a * ε) / (4 * N) := by ring
      rw [e, le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  · rw [← hzero]; simp; exact hε.le

end LongTails.Proofs.GeneralCovarianceReverseFisherRate
