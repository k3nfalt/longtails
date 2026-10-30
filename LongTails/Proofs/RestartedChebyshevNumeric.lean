import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace OracleTemplate.RestartedScheduleGD

section Numeric

variable {S ε n K L ρ : ℝ}

structure NumHyp (S ε n K L ρ : ℝ) : Prop where
  hS : 0 < S
  hε : 0 < ε
  hn : 4 ≤ n
  hK : 1 ≤ K
  hL : 0 < L
  hρ : 0 < ρ
  hLS : L * S ≤ n ^ 2
  hSL : n ≤ 16 * L * S
  hq1 : K * (ρ * S ^ 2 * n * ε) * n ^ 2 ≤ 1 / 10 ^ 7
  hq2 : (ρ * S ^ 2 * n * ε) * n ^ 3 ≤ 1 / 10 ^ 7

lemma NumHyp.basic (h : NumHyp S ε n K L ρ) :
    let Θ := ρ * S ^ 2 * n * ε
    0 ≤ Θ ∧ Θ * n ^ 2 ≤ 1 / 10 ^ 7 ∧ K * Θ ≤ 1 / 10 ^ 7 ∧
      K ^ 2 * Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 ∧ Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 ∧
      L * S * K ^ 2 * Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 ∧ L * S * Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 ∧
      (L * S) ^ 2 * Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 ∧ K ^ 2 * Θ ^ 2 * n ^ 4 ≤ 1 / 10 ^ 14 := by
  intro Θ
  have hS := h.hS; have hε := h.hε; have hn := h.hn; have hK := h.hK
  have hL := h.hL; have hρ := h.hρ
  have hΘ : 0 ≤ Θ := by positivity
  have hn1 : (1:ℝ) ≤ n := by linarith
  have hn2 : (1:ℝ) ≤ n ^ 2 := by nlinarith
  have hLS0 : 0 ≤ L * S := by positivity
  have hq1 := h.hq1
  have hq2 := h.hq2
  have a1 : Θ * n ^ 2 ≤ 1 / 10 ^ 7 := by
    have : Θ * n ^ 2 ≤ K * Θ * n ^ 2 := by
      have : 0 ≤ Θ * n ^ 2 := by positivity
      nlinarith
    linarith
  have a0 : 0 ≤ K * Θ * n ^ 2 := by positivity
  have a2 : K * Θ ≤ 1 / 10 ^ 7 := by
    have : K * Θ ≤ K * Θ * n ^ 2 := by
      have : 0 ≤ K * Θ := by positivity
      nlinarith
    linarith
  have sq1 : (K * Θ * n ^ 2) ^ 2 ≤ (1 / 10 ^ 7) ^ 2 := pow_le_pow_left₀ a0 hq1 2
  have sq2 : (Θ * n ^ 3) ^ 2 ≤ (1 / 10 ^ 7) ^ 2 := pow_le_pow_left₀ (by positivity) hq2 2
  have e7 : ((1:ℝ) / 10 ^ 7) ^ 2 = 1 / 10 ^ 14 := by norm_num
  rw [e7] at sq1 sq2
  have b7 : K ^ 2 * Θ ^ 2 * n ^ 4 ≤ 1 / 10 ^ 14 := by nlinarith
  have hKΘn : 0 ≤ K ^ 2 * Θ ^ 2 * n ^ 2 := by positivity
  have b2 : K ^ 2 * Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 := by
    have : K ^ 2 * Θ ^ 2 * n ^ 2 ≤ K ^ 2 * Θ ^ 2 * n ^ 4 := by nlinarith
    linarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have b3 : Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 := by
    have : Θ ^ 2 * n ^ 2 ≤ K ^ 2 * Θ ^ 2 * n ^ 2 := by
      have : 0 ≤ Θ ^ 2 * n ^ 2 := by positivity
      nlinarith
    linarith
  have b5 : L * S * K ^ 2 * Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 := by
    have h0 : 0 ≤ K ^ 2 * Θ ^ 2 * n ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_right h.hLS h0
    have e1 : L * S * K ^ 2 * Θ ^ 2 * n ^ 2 = L * S * (K ^ 2 * Θ ^ 2 * n ^ 2) := by ring
    have e2 : n ^ 2 * (K ^ 2 * Θ ^ 2 * n ^ 2) = K ^ 2 * Θ ^ 2 * n ^ 4 := by ring
    rw [e1]; linarith
  have b4 : L * S * Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 := by
    have : L * S * Θ ^ 2 * n ^ 2 ≤ L * S * K ^ 2 * Θ ^ 2 * n ^ 2 := by
      have : 0 ≤ L * S * Θ ^ 2 * n ^ 2 := by positivity
      nlinarith
    linarith
  have b6 : (L * S) ^ 2 * Θ ^ 2 * n ^ 2 ≤ 1 / 10 ^ 14 := by
    have h1 : (L * S) ^ 2 ≤ (n ^ 2) ^ 2 := pow_le_pow_left₀ hLS0 h.hLS 2
    have : (L * S) ^ 2 * Θ ^ 2 * n ^ 2 ≤ (n ^ 2) ^ 2 * Θ ^ 2 * n ^ 2 := by
      have : 0 ≤ Θ ^ 2 * n ^ 2 := by positivity
      nlinarith
    nlinarith
  exact ⟨hΘ, a1, a2, b2, b3, b5, b4, b6, b7⟩

theorem num_completed (h : NumHyp S ε n K L ρ) :
    let R := 8 * S * (n * ε)
    (K ^ 2 / 2 + 1181) * S * (ρ * R ^ 2) ^ 2 + (L * K ^ 2 / 2 + 16 * L) * S ^ 2 * (ρ * R ^ 2) ^ 2 +
      2 * S * K ^ 2 * n ^ 2 * (ρ * R ^ 2) ^ 2 + ρ * R ^ 3 ≤ S * ε ^ 2 / 16 / 4 := by
  intro R
  obtain ⟨hΘ, a1, a2, b2, b3, b5, b4, b6, b7⟩ := h.basic
  set Θ := ρ * S ^ 2 * n * ε
  have hSε : 0 < S * ε ^ 2 := by have := h.hS; have := h.hε; positivity
  have e : (K ^ 2 / 2 + 1181) * S * (ρ * R ^ 2) ^ 2 +
      (L * K ^ 2 / 2 + 16 * L) * S ^ 2 * (ρ * R ^ 2) ^ 2 +
      2 * S * K ^ 2 * n ^ 2 * (ρ * R ^ 2) ^ 2 + ρ * R ^ 3 =
      S * ε ^ 2 * (2048 * (K ^ 2 * Θ ^ 2 * n ^ 2) + 4837376 * (Θ ^ 2 * n ^ 2) +
        2048 * (L * S * K ^ 2 * Θ ^ 2 * n ^ 2) + 65536 * (L * S * Θ ^ 2 * n ^ 2) +
        8192 * (K ^ 2 * Θ ^ 2 * n ^ 4) + 512 * (Θ * n ^ 2)) := by
    simp only [R, Θ]; ring
  rw [e]
  have : 2048 * (K ^ 2 * Θ ^ 2 * n ^ 2) + 4837376 * (Θ ^ 2 * n ^ 2) +
      2048 * (L * S * K ^ 2 * Θ ^ 2 * n ^ 2) + 65536 * (L * S * Θ ^ 2 * n ^ 2) +
      8192 * (K ^ 2 * Θ ^ 2 * n ^ 4) + 512 * (Θ * n ^ 2) ≤ 1 / 64 := by
    linarith
  have := mul_le_mul_of_nonneg_left this hSε.le
  linarith

theorem num_pred (h : NumHyp S ε n K L ρ) :
    let R := 8 * S * (n * ε)
    K * (2 * (n * ε)) * (S * (ρ * (2 * R) ^ 2)) + L * K ^ 2 / 2 * S ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 +
      1188 * S * (ρ * (2 * R) ^ 2) ^ 2 + 15 * L * S ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 +
      15 * L ^ 2 * S ^ 3 * (ρ * (2 * R) ^ 2) ^ 2 + 9 * ρ * R ^ 3 ≤ S * ε ^ 2 / 16 / 4 := by
  intro R
  obtain ⟨hΘ, a1, a2, b2, b3, b5, b4, b6, b7⟩ := h.basic
  set Θ := ρ * S ^ 2 * n * ε
  have hSε : 0 < S * ε ^ 2 := by have := h.hS; have := h.hε; positivity
  have hKΘn : K * Θ * n ^ 2 ≤ 1 / 10 ^ 7 := h.hq1
  have e : K * (2 * (n * ε)) * (S * (ρ * (2 * R) ^ 2)) +
      L * K ^ 2 / 2 * S ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 +
      1188 * S * (ρ * (2 * R) ^ 2) ^ 2 + 15 * L * S ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 +
      15 * L ^ 2 * S ^ 3 * (ρ * (2 * R) ^ 2) ^ 2 + 9 * ρ * R ^ 3 =
      S * ε ^ 2 * (512 * (K * Θ * n ^ 2) + 32768 * (L * S * K ^ 2 * Θ ^ 2 * n ^ 2) +
        77856768 * (Θ ^ 2 * n ^ 2) + 983040 * (L * S * Θ ^ 2 * n ^ 2) +
        983040 * ((L * S) ^ 2 * Θ ^ 2 * n ^ 2) + 4608 * (Θ * n ^ 2)) := by
    simp only [R, Θ]; ring
  rw [e]
  have : 512 * (K * Θ * n ^ 2) + 32768 * (L * S * K ^ 2 * Θ ^ 2 * n ^ 2) +
      77856768 * (Θ ^ 2 * n ^ 2) + 983040 * (L * S * Θ ^ 2 * n ^ 2) +
      983040 * ((L * S) ^ 2 * Θ ^ 2 * n ^ 2) + 4608 * (Θ * n ^ 2) ≤ 1 / 64 := by
    linarith
  have := mul_le_mul_of_nonneg_left this hSε.le
  linarith

theorem num_exit1 (h : NumHyp S ε n K L ρ) :
    let R := 8 * S * (n * ε)
    42 * ρ * S * (R + K / L * (n * ε + L * R)) ≤ 1 := by
  intro R
  obtain ⟨hΘ, a1, a2, b2, b3, b5, b4, b6, b7⟩ := h.basic
  have hS := h.hS; have hε := h.hε; have hn := h.hn; have hK := h.hK
  have hL := h.hL; have hρ := h.hρ
  have h1 : K / L * (n * ε) ≤ 16 * K * S * ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    have := h.hSL
    have : 0 ≤ K * ε := by positivity
    nlinarith
  have h2 : K / L * (n * ε + L * R) = K / L * (n * ε) + K * R := by
    rw [mul_add, show K / L * (L * R) = K * R by field_simp]
  have hR : R = 8 * S * (n * ε) := rfl
  have h3 : R + K / L * (n * ε + L * R) ≤ 32 * K * S * n * ε := by
    rw [h2, hR]
    have hKSε : 0 ≤ K * S * ε := by positivity
    have p1 : K * S * ε * 1 ≤ K * S * ε * n := mul_le_mul_of_nonneg_left (by linarith) hKSε
    have hSnε : 0 ≤ S * n * ε := by positivity
    have p2 : 1 * (S * n * ε) ≤ K * (S * n * ε) := mul_le_mul_of_nonneg_right hK hSnε
    have e1 : K * (8 * S * (n * ε)) = 8 * (K * (S * n * ε)) := by ring
    have e2 : 8 * S * (n * ε) = 8 * (1 * (S * n * ε)) := by ring
    have e3 : 16 * K * S * ε = 16 * (K * S * ε * 1) := by ring
    have e4 : 32 * K * S * n * ε = 16 * (K * S * ε * n) + 16 * (K * (S * n * ε)) := by ring
    rw [e1, e2, e4]
    rw [e3] at h1
    linarith
  have h4 : 42 * ρ * S * (R + K / L * (n * ε + L * R)) ≤ 42 * ρ * S * (32 * K * S * n * ε) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : 42 * ρ * S * (32 * K * S * n * ε) = 1344 * (K * (ρ * S ^ 2 * n * ε)) := by ring
  linarith

theorem num_exit2 (h : NumHyp S ε n K L ρ) :
    let R := 8 * S * (n * ε)
    K * (n * ε) * (S * (ρ * R ^ 2)) + 2 * S * (n * ε) ^ 2 / 21 +
      (2 * K ^ 2 / 21 + 1181) * S * (ρ * R ^ 2) ^ 2 +
      (L * K ^ 2 / 2 + 16 * L) * S ^ 2 * (ρ * R ^ 2) ^ 2 + 2 * (S * ε ^ 2 / 16) ≤
      R ^ 2 / (42 * S) := by
  intro R
  obtain ⟨hΘ, a1, a2, b2, b3, b5, b4, b6, b7⟩ := h.basic
  set Θ := ρ * S ^ 2 * n * ε
  have hS := h.hS; have hn := h.hn
  have hSε : 0 < S * ε ^ 2 := by have := h.hε; positivity
  have hKΘn : K * Θ * n ^ 2 ≤ 1 / 10 ^ 7 := h.hq1
  have eR : R ^ 2 / (42 * S) = S * ε ^ 2 * (32 / 21 * n ^ 2) := by
    simp only [R]; field_simp; ring
  have e : K * (n * ε) * (S * (ρ * R ^ 2)) + 2 * S * (n * ε) ^ 2 / 21 +
      (2 * K ^ 2 / 21 + 1181) * S * (ρ * R ^ 2) ^ 2 +
      (L * K ^ 2 / 2 + 16 * L) * S ^ 2 * (ρ * R ^ 2) ^ 2 + 2 * (S * ε ^ 2 / 16) =
      S * ε ^ 2 * (64 * (K * Θ * n ^ 2) + 2 / 21 * n ^ 2 +
        8192 / 21 * (K ^ 2 * Θ ^ 2 * n ^ 2) + 4837376 * (Θ ^ 2 * n ^ 2) +
        2048 * (L * S * K ^ 2 * Θ ^ 2 * n ^ 2) + 65536 * (L * S * Θ ^ 2 * n ^ 2) + 1 / 8) := by
    simp only [R, Θ]; ring
  rw [e, eR]
  apply mul_le_mul_of_nonneg_left _ hSε.le
  have hn2 : (16:ℝ) ≤ n ^ 2 := by nlinarith
  linarith

theorem num_err (h : NumHyp S ε n K L ρ) :
    let R := 8 * S * (n * ε)
    ρ * R ^ 2 ≤ ε / 10 := by
  intro R
  obtain ⟨hΘ, a1, -⟩ := h.basic
  have hε := h.hε; have hn := h.hn
  have e : ρ * R ^ 2 = 64 * ((ρ * S ^ 2 * n * ε) * n) * ε := by simp only [R]; ring
  rw [e]
  have h1 : (ρ * S ^ 2 * n * ε) * n ≤ (ρ * S ^ 2 * n * ε) * n ^ 2 := by
    have : 0 ≤ ρ * S ^ 2 * n * ε := hΘ
    exact mul_le_mul_of_nonneg_left (by nlinarith) this
  have : 64 * ((ρ * S ^ 2 * n * ε) * n) ≤ 1 / 10 := by linarith
  have := mul_le_mul_of_nonneg_right this hε.le
  linarith

theorem num_plain (h : NumHyp S ε n K L ρ) :
    S * ε ^ 2 / 16 + S * ε ^ 2 / 16 / (2 * n) ≤ (n * ε) ^ 2 / (2 * L) := by
  have hS := h.hS; have hε := h.hε; have hn := h.hn; have hL := h.hL
  have h1 : S * ε ^ 2 / 16 / (2 * n) ≤ S * ε ^ 2 / 16 := by
    apply div_le_self (by positivity); linarith
  have h2 : S * ε ^ 2 / 8 ≤ (n * ε) ^ 2 / (2 * L) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have := h.hLS
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    nlinarith
  linarith

end Numeric

end OracleTemplate.RestartedScheduleGD
