import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

namespace OracleTemplate.ScheduleBlock

lemma neg_q_eq (m R P γ δ : ℝ) (hRP : m * R = P - 1) :
    γ * (-(R * γ) - δ) - m * (-(R * γ) - δ) ^ 2 / 2 =
      -(γ ^ 2 * R * (P + 1) / 2) - P * γ * δ - m * δ ^ 2 / 2 := by
  have hP : P = m * R + 1 := by linarith
  subst hP; ring

lemma abs_u_le {R P γ δ σ : ℝ} (hR : 0 ≤ R) (hδ : |δ| ≤ P * σ) :
    |-(R * γ) - δ| ≤ R * |γ| + P * σ := by
  have h1 : |-(R * γ) - δ| ≤ |R * γ| + |δ| := by
    rw [show -(R * γ) - δ = -(R * γ) + -δ by ring]
    calc |-(R * γ) + -δ| ≤ |-(R * γ)| + |-δ| := abs_add_le _ _
      _ = |R * γ| + |δ| := by rw [abs_neg, abs_neg]
  rw [abs_mul, abs_of_nonneg hR] at h1
  linarith

lemma err_term_le {P γ δ σ : ℝ} (hP : 0 ≤ P) (hδ : |δ| ≤ P * σ) :
    -(P * γ * δ) ≤ P * |γ| * (P * σ) := by
  have h1 : |P * γ * δ| ≤ P * |γ| * (P * σ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hP]
    exact mul_le_mul_of_nonneg_left hδ (mul_nonneg hP (abs_nonneg γ))
  linarith [neg_abs_le (P * γ * δ)]

lemma mild_good {S R P a b σ q : ℝ} (hS : 0 < S) (hσ : 0 ≤ σ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hRS : S ≤ R) (hR3 : R ≤ 3 * S) (hP0 : 1 ≤ P) (hP3 : P ≤ 3)
    (hq : q ≤ -(a ^ 2 * R * (P + 1) / 2) + P * a * (P * σ))
    (hbb : b ≤ R * a + P * σ) (hgood : 18 * σ ≤ S * a) :
    q ≤ -(b ^ 2 / (21 * S)) := by
  have hRP2 : 2 * S ≤ R * (P + 1) := by nlinarith
  have hM : S * a ^ 2 ≤ a ^ 2 * R * (P + 1) / 2 := by
    have := mul_le_mul_of_nonneg_left hRP2 (sq_nonneg a)
    linarith
  have hPP : P * P ≤ 9 := by nlinarith
  have herr1 : P * a * (P * σ) ≤ 9 * (a * σ) := by
    have e : P * a * (P * σ) = (P * P) * (a * σ) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right hPP (mul_nonneg ha hσ)
  have herr2 : 9 * (a * σ) ≤ S * a ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hgood ha
    have e : a * (S * a) = S * a ^ 2 := by ring
    linarith
  have hPσ : P * σ ≤ S * a / 6 := by
    have := mul_le_mul_of_nonneg_right hP3 hσ
    linarith
  have hRa : R * a ≤ 3 * S * a := mul_le_mul_of_nonneg_right hR3 ha
  have hbb' : b ≤ 19 / 6 * (S * a) := by linarith
  have hb2 : b ^ 2 ≤ 361 / 36 * (S * a) ^ 2 := by
    have := mul_le_mul hbb' hbb' hb (by positivity)
    nlinarith
  have hfrac : b ^ 2 / (21 * S) ≤ S * a ^ 2 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have e : (S * a) ^ 2 = S * (S * a ^ 2) := by ring
    have : S * a ^ 2 / 2 * (21 * S) = 21 / 2 * (S * (S * a ^ 2)) := by ring
    rw [this]; rw [e] at hb2
    have hSa : 0 ≤ S * (S * a ^ 2) := by positivity
    linarith
  linarith

lemma mild_bad {S R P a b σ q : ℝ} (hS : 0 < S) (hσ : 0 ≤ σ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR3 : R ≤ 3 * S) (hP3 : P ≤ 3) (hq : q ≤ a * b)
    (hbb : b ≤ R * a + P * σ) (hbad : S * a < 18 * σ) :
    q ≤ -(b ^ 2 / (21 * S)) + 1181 * σ ^ 2 / S := by
  have hRa : R * a ≤ 3 * S * a := mul_le_mul_of_nonneg_right hR3 ha
  have hPσ : P * σ ≤ 3 * σ := mul_le_mul_of_nonneg_right hP3 hσ
  have hbb' : b ≤ 3 * (S * a) + 3 * σ := by linarith
  have hb57 : b ≤ 57 * σ := by linarith
  have hab : a * b * S ≤ 1026 * σ ^ 2 := by
    have h1 : a * b * S ≤ (S * a) * (57 * σ) := by
      have := mul_le_mul_of_nonneg_left hb57 (mul_nonneg hS.le ha)
      linarith
    have h2 : (S * a) * (57 * σ) ≤ (18 * σ) * (57 * σ) :=
      mul_le_mul_of_nonneg_right hbad.le (by positivity)
    nlinarith
  have hab' : a * b ≤ 1026 * σ ^ 2 / S := by rw [le_div_iff₀ hS]; exact hab
  have hb2 : b ^ 2 ≤ 3249 * σ ^ 2 := by
    have := mul_le_mul hb57 hb57 hb (by positivity)
    nlinarith
  have hfrac : b ^ 2 / (21 * S) ≤ 155 * σ ^ 2 / S := by
    rw [div_le_div_iff₀ (by positivity) hS]
    have : 0 ≤ σ ^ 2 * S := by positivity
    nlinarith
  have hpos : 0 ≤ b ^ 2 / (21 * S) := by positivity
  have e : 1026 * σ ^ 2 / S + 155 * σ ^ 2 / S = 1181 * σ ^ 2 / S := by ring
  linarith

lemma strong_good {m S R P a b σ q : ℝ} (hm : 0 < m) (hS : 0 < S) (_hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hRP : m * R = P - 1) (hP2 : 2 ≤ P) (hSm : 1 ≤ m * S)
    (hq : q ≤ -(a ^ 2 * R * (P + 1) / 2) + P * a * (P * σ))
    (hbb : b ≤ R * a + P * σ) (hgood : 16 * m * σ ≤ 3 * a) :
    q ≤ -(b ^ 2 / (21 * S)) := by
  have hmain : 16 * m * (a ^ 2 * R * (P + 1) / 2) = 8 * a ^ 2 * (P ^ 2 - 1) := by
    have e : 16 * m * (a ^ 2 * R * (P + 1) / 2) = 8 * a ^ 2 * (m * R) * (P + 1) := by ring
    rw [e, hRP]; ring
  have herr : 16 * m * (P * a * (P * σ)) ≤ 3 * P ^ 2 * a ^ 2 := by
    have e : 16 * m * (P * a * (P * σ)) = (P ^ 2 * a) * (16 * m * σ) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hgood (mul_nonneg (sq_nonneg P) ha)
    have e2 : P ^ 2 * a * (3 * a) = 3 * P ^ 2 * a ^ 2 := by ring
    linarith
  have hP4 : 4 ≤ P ^ 2 := by nlinarith
  have h16q : 16 * m * q ≤ -(3 * P ^ 2 * a ^ 2) := by
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ 16 * m)
    have e : 16 * m * (-(a ^ 2 * R * (P + 1) / 2) + P * a * (P * σ)) =
        -(16 * m * (a ^ 2 * R * (P + 1) / 2)) + 16 * m * (P * a * (P * σ)) := by ring
    rw [e, hmain] at this
    have : 8 * a ^ 2 ≤ 2 * (P ^ 2 * a ^ 2) := by nlinarith [sq_nonneg a]
    nlinarith
  have hmb : m * b ≤ 19 / 16 * (P * a) := by
    have h1 : m * (R * a) = (P - 1) * a := by rw [← mul_assoc, hRP]
    have h3 : m * σ ≤ 3 / 16 * a := by linarith
    have h2 : m * (P * σ) ≤ 3 / 16 * (P * a) := by
      have e : m * (P * σ) = P * (m * σ) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ P)
      linarith
    have := mul_le_mul_of_nonneg_left hbb hm.le
    nlinarith
  have hmb0 : 0 ≤ m * b := by positivity
  have hmb2 : (m * b) ^ 2 ≤ (19 / 16 * (P * a)) ^ 2 := by
    have := mul_le_mul hmb hmb hmb0 (by positivity)
    nlinarith
  have hfrac_le : b ^ 2 / (21 * S) ≤ m * b ^ 2 / 21 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hSm (sq_nonneg b)
    have e : m * b ^ 2 / 21 * (21 * S) = b ^ 2 * (m * S) := by ring
    linarith
  have h16f : 16 * m * (m * b ^ 2 / 21) ≤ 2 * P ^ 2 * a ^ 2 := by
    have e : 16 * m * (m * b ^ 2 / 21) = 16 / 21 * (m * b) ^ 2 := by ring
    rw [e]
    have e2 : (19 / 16 * (P * a)) ^ 2 = 361 / 256 * (P ^ 2 * a ^ 2) := by ring
    rw [e2] at hmb2
    have : 0 ≤ P ^ 2 * a ^ 2 := by positivity
    linarith
  have hfin : 16 * m * (q + b ^ 2 / (21 * S)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hfrac_le (by positivity : (0:ℝ) ≤ 16 * m)
    have e : 16 * m * (q + b ^ 2 / (21 * S)) = 16 * m * q + 16 * m * (b ^ 2 / (21 * S)) := by
      ring
    rw [e]
    have : 0 ≤ P ^ 2 * a ^ 2 := by positivity
    linarith
  have : q + b ^ 2 / (21 * S) ≤ 0 := by
    by_contra hc; push Not at hc
    have : 0 < 16 * m * (q + b ^ 2 / (21 * S)) := by positivity
    linarith
  linarith

lemma strong_bad {m S a b σ q : ℝ} (hm : 0 < m) (hS : 0 < S) (_hσ : 0 ≤ σ) (hb : 0 ≤ b)
    (hSm : 1 ≤ m * S) (hq : q ≤ a * b - m * b ^ 2 / 2) (hbad : 3 * a < 16 * m * σ) :
    q ≤ -(b ^ 2 / (21 * S)) + 16 * m * σ ^ 2 := by
  have hab : a * b ≤ 16 / 3 * (m * σ) * b := by
    have := mul_le_mul_of_nonneg_right hbad.le hb
    linarith
  have hquad : 16 / 3 * (m * σ) * b - 19 / 42 * (m * b ^ 2) ≤ 16 * m * σ ^ 2 := by
    have hsq := mul_nonneg hm.le (sq_nonneg (b - 112 / 19 * σ))
    have hσm : 0 ≤ m * σ ^ 2 := by positivity
    nlinarith
  have hfrac_le : b ^ 2 / (21 * S) ≤ m * b ^ 2 / 21 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hSm (sq_nonneg b)
    have e : m * b ^ 2 / 21 * (21 * S) = b ^ 2 * (m * S) := by ring
    linarith
  have e : a * b - m * b ^ 2 / 2 + m * b ^ 2 / 21 = a * b - 19 / 42 * (m * b ^ 2) := by ring
  linarith

theorem neg_coord_U1 {m S R P γ δ σ : ℝ} (hm : 0 < m) (hS : 0 < S) (hσ : 0 ≤ σ)
    (hRP : m * R = P - 1) (hRS : S ≤ R) (hRPS : R ≤ P * S) (hP1 : 1 + m * S ≤ P)
    (hPmild : m * S < 1 → P ≤ 3) (hδ : |δ| ≤ P * σ) :
    γ * (-(R * γ) - δ) - m * (-(R * γ) - δ) ^ 2 / 2 ≤
      -((-(R * γ) - δ) ^ 2 / (21 * S)) + 1181 * σ ^ 2 / S + 16 * m * σ ^ 2 := by
  have hR0 : 0 ≤ R := le_trans hS.le hRS
  have hmS0 : 0 ≤ m * S := by positivity
  have hP0 : 1 ≤ P := by linarith
  have hu_le := abs_u_le (γ := γ) hR0 hδ
  have hq := neg_q_eq m R P γ δ hRP
  have herr := err_term_le (γ := γ) (by linarith : (0:ℝ) ≤ P) hδ
  have hu2 : (-(R * γ) - δ) ^ 2 = |-(R * γ) - δ| ^ 2 := (sq_abs _).symm
  have hγ2 : γ ^ 2 = |γ| ^ 2 := (sq_abs γ).symm
  have hmδ : 0 ≤ m * δ ^ 2 / 2 := by positivity
  have hqm : γ * (-(R * γ) - δ) - m * (-(R * γ) - δ) ^ 2 / 2 ≤
      -(|γ| ^ 2 * R * (P + 1) / 2) + P * |γ| * (P * σ) := by
    rw [hq, hγ2]; linarith
  have hσS : 0 ≤ 1181 * σ ^ 2 / S := by positivity
  have hσm : 0 ≤ 16 * m * σ ^ 2 := by positivity
  have hk : (-(R * γ) - δ) ^ 2 / (21 * S) = |-(R * γ) - δ| ^ 2 / (21 * S) := by rw [hu2]
  by_cases hmild : m * S < 1
  · have hP3 := hPmild hmild
    have hR3 : R ≤ 3 * S := le_trans hRPS (by nlinarith)
    by_cases hgood : 18 * σ ≤ S * |γ|
    · have := mild_good hS hσ (abs_nonneg γ) (abs_nonneg _) hRS hR3 hP0 hP3 hqm hu_le hgood
      linarith
    · push Not at hgood
      have hγu : γ * (-(R * γ) - δ) ≤ |γ| * |-(R * γ) - δ| := by
        rw [← abs_mul]; exact le_abs_self _
      have hmu : 0 ≤ m * (-(R * γ) - δ) ^ 2 / 2 := by positivity
      have hq2 : γ * (-(R * γ) - δ) - m * (-(R * γ) - δ) ^ 2 / 2 ≤
          |γ| * |-(R * γ) - δ| := by linarith
      have := mild_bad hS hσ (abs_nonneg γ) (abs_nonneg _) hR3 hP3 hq2 hu_le hgood
      linarith
  · push Not at hmild
    by_cases hgood : 16 * m * σ ≤ 3 * |γ|
    · have := strong_good hm hS hσ (abs_nonneg γ) (abs_nonneg _) hRP (by linarith) hmild hqm
        hu_le hgood
      linarith
    · push Not at hgood
      have hγu : γ * (-(R * γ) - δ) ≤ |γ| * |-(R * γ) - δ| := by
        rw [← abs_mul]; exact le_abs_self _
      have hq2 : γ * (-(R * γ) - δ) - m * (-(R * γ) - δ) ^ 2 / 2 ≤
          |γ| * |-(R * γ) - δ| - m * |-(R * γ) - δ| ^ 2 / 2 := by rw [← hu2]; linarith
      have := strong_bad hm hS hσ (abs_nonneg _) hmild hq2 hgood
      linarith

end OracleTemplate.ScheduleBlock
