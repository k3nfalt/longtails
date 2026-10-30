import LongTails.Proofs.ScheduleCoordinateBounds

namespace OracleTemplate.ScheduleBlock

lemma mild_good_start {S R P a σ q : ℝ} (hS : 0 < S) (hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (hRS : S ≤ R) (hP0 : 1 ≤ P) (hP3 : P ≤ 3)
    (hq : q ≤ -(a ^ 2 * R * (P + 1) / 2) + P * a * (P * σ)) (hgood : 18 * σ ≤ S * a) :
    q ≤ -(S * a ^ 2 / 2) := by
  have hRP2 : 2 * S ≤ R * (P + 1) := by
    have h1 : 0 ≤ (R - S) * (P + 1) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ S * (P - 1) := mul_nonneg hS.le (by linarith)
    nlinarith
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
  linarith

lemma mild_bad_start {S R P a b σ q : ℝ} (hS : 0 < S) (hσ : 0 ≤ σ) (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hR3 : R ≤ 3 * S) (hP3 : P ≤ 3) (hq : q ≤ a * b)
    (hbb : b ≤ R * a + P * σ) (hbad : S * a < 18 * σ) :
    q ≤ -(S * a ^ 2 / 2) + 1188 * σ ^ 2 / S := by
  have hRa : R * a ≤ 3 * S * a := mul_le_mul_of_nonneg_right hR3 ha
  have hPσ : P * σ ≤ 3 * σ := mul_le_mul_of_nonneg_right hP3 hσ
  have hb57 : b ≤ 57 * σ := by linarith
  have hab : a * b * S ≤ 1026 * σ ^ 2 := by
    have h1 : a * b * S ≤ (S * a) * (57 * σ) := by
      have := mul_le_mul_of_nonneg_left hb57 (mul_nonneg hS.le ha)
      linarith
    have h2 : (S * a) * (57 * σ) ≤ (18 * σ) * (57 * σ) :=
      mul_le_mul_of_nonneg_right hbad.le (by positivity)
    nlinarith
  have hab' : a * b ≤ 1026 * σ ^ 2 / S := by rw [le_div_iff₀ hS]; exact hab
  have hSa2 : S * a ^ 2 / 2 ≤ 162 * σ ^ 2 / S := by
    rw [le_div_iff₀ hS]
    have h0 : 0 ≤ S * a := by positivity
    have := mul_le_mul hbad.le hbad.le h0 (by positivity)
    nlinarith
  have e : 1026 * σ ^ 2 / S + 162 * σ ^ 2 / S = 1188 * σ ^ 2 / S := by ring
  linarith

lemma strong_good_start {m S R P a σ q : ℝ} (hm : 0 < m) (ha : 0 ≤ a)
    (hRP : m * R = P - 1) (hP1 : 1 + m * S ≤ P) (hSm : 1 ≤ m * S)
    (hq : q ≤ -(a ^ 2 * R * (P + 1) / 2) + P * a * (P * σ)) (hgood : 16 * m * σ ≤ 3 * a) :
    q ≤ -(S * a ^ 2 / 2) := by
  have hP2 : 2 ≤ P := by linarith
  have hmain : 16 * m * (a ^ 2 * R * (P + 1) / 2) = 8 * a ^ 2 * (P ^ 2 - 1) := by
    have e : 16 * m * (a ^ 2 * R * (P + 1) / 2) = 8 * a ^ 2 * (m * R) * (P + 1) := by ring
    rw [e, hRP]; ring
  have herr : 16 * m * (P * a * (P * σ)) ≤ 3 * P ^ 2 * a ^ 2 := by
    have e : 16 * m * (P * a * (P * σ)) = (P ^ 2 * a) * (16 * m * σ) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hgood (mul_nonneg (sq_nonneg P) ha)
    have e2 : P ^ 2 * a * (3 * a) = 3 * P ^ 2 * a ^ 2 := by ring
    linarith
  have hP4 : 4 * (m * S) ≤ P ^ 2 := by nlinarith
  have h16q : 16 * m * q ≤ -(3 * P ^ 2 * a ^ 2) := by
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ 16 * m)
    have e : 16 * m * (-(a ^ 2 * R * (P + 1) / 2) + P * a * (P * σ)) =
        -(16 * m * (a ^ 2 * R * (P + 1) / 2)) + 16 * m * (P * a * (P * σ)) := by ring
    rw [e, hmain] at this
    have : 8 * a ^ 2 ≤ 2 * (P ^ 2 * a ^ 2) := by nlinarith [sq_nonneg a]
    nlinarith
  have hfin : 16 * m * (q + S * a ^ 2 / 2) ≤ 0 := by
    have : 12 * (m * S) * a ^ 2 ≤ 3 * P ^ 2 * a ^ 2 := by nlinarith [sq_nonneg a]
    nlinarith
  have : q + S * a ^ 2 / 2 ≤ 0 := by
    by_contra hc; push Not at hc
    have : 0 < 16 * m * (q + S * a ^ 2 / 2) := by positivity
    linarith
  linarith

lemma strong_bad_start {m S a b σ q : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (hσ : 0 ≤ σ)
    (hq : q ≤ a * b - m * b ^ 2 / 2) (hbad : 3 * a < 16 * m * σ) (hS : 0 ≤ S) :
    q ≤ -(S * a ^ 2 / 2) + 15 * m * σ ^ 2 + 15 * S * m ^ 2 * σ ^ 2 := by
  have h1 : a * b - m * b ^ 2 / 2 ≤ a ^ 2 / (2 * m) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a - m * b), hm.le]
  have ha2 : a ^ 2 ≤ 256 / 9 * (m * σ) ^ 2 := by
    have := mul_le_mul hbad.le hbad.le (by positivity) (by positivity)
    nlinarith
  have h2 : a ^ 2 / (2 * m) ≤ 15 * m * σ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have e : (m * σ) ^ 2 = m ^ 2 * σ ^ 2 := by ring
    rw [e] at ha2
    have : 0 ≤ m ^ 2 * σ ^ 2 := by positivity
    nlinarith
  have h3 : S * a ^ 2 / 2 ≤ 15 * S * m ^ 2 * σ ^ 2 := by
    have := mul_le_mul_of_nonneg_left ha2 hS
    have e : (m * σ) ^ 2 = m ^ 2 * σ ^ 2 := by ring
    rw [e] at this
    have : 0 ≤ S * (m ^ 2 * σ ^ 2) := by positivity
    nlinarith
  linarith

theorem neg_coord_U2 {m S R P γ δ σ : ℝ} (hm : 0 < m) (hS : 0 < S) (hσ : 0 ≤ σ)
    (hRP : m * R = P - 1) (hRS : S ≤ R) (hRPS : R ≤ P * S) (hP1 : 1 + m * S ≤ P)
    (hPmild : m * S < 1 → P ≤ 3) (hδ : |δ| ≤ P * σ) :
    γ * (-(R * γ) - δ) - m * (-(R * γ) - δ) ^ 2 / 2 ≤
      -(S * γ ^ 2 / 2) + 1188 * σ ^ 2 / S + 15 * m * σ ^ 2 + 15 * S * m ^ 2 * σ ^ 2 := by
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
  have h1 : 0 ≤ 1188 * σ ^ 2 / S := by positivity
  have h2 : 0 ≤ 15 * m * σ ^ 2 := by positivity
  have h3 : 0 ≤ 15 * S * m ^ 2 * σ ^ 2 := by positivity
  have hγu : γ * (-(R * γ) - δ) ≤ |γ| * |-(R * γ) - δ| := by
    rw [← abs_mul]; exact le_abs_self _
  rw [hγ2]
  by_cases hmild : m * S < 1
  · have hP3 := hPmild hmild
    have hR3 : R ≤ 3 * S := le_trans hRPS (by nlinarith)
    by_cases hgood : 18 * σ ≤ S * |γ|
    · have := mild_good_start hS hσ (abs_nonneg γ) hRS hP0 hP3 hqm hgood
      linarith
    · push Not at hgood
      have hmu : 0 ≤ m * (-(R * γ) - δ) ^ 2 / 2 := by positivity
      have hq2 : γ * (-(R * γ) - δ) - m * (-(R * γ) - δ) ^ 2 / 2 ≤
          |γ| * |-(R * γ) - δ| := by linarith
      have := mild_bad_start hS hσ (abs_nonneg γ) (abs_nonneg _) hR3 hP3 hq2 hu_le hgood
      linarith
  · push Not at hmild
    by_cases hgood : 16 * m * σ ≤ 3 * |γ|
    · have := strong_good_start hm (abs_nonneg γ) hRP hP1 hmild hqm hgood
      linarith
    · push Not at hgood
      have hq2 : γ * (-(R * γ) - δ) - m * (-(R * γ) - δ) ^ 2 / 2 ≤
          |γ| * |-(R * γ) - δ| - m * |-(R * γ) - δ| ^ 2 / 2 := by rw [← hu2]; linarith
      have := strong_bad_start hm (abs_nonneg γ) hσ hq2 hgood hS.le
      linarith

theorem pos_coord_U5 {lam R P γ δ : ℝ} (_hlam : 0 ≤ lam) (hR : 0 ≤ R) (hRP : lam * R = 1 - P)
    (hP : |P| ≤ 1) :
    γ * (-(R * γ) - δ) + lam * (-(R * γ) - δ) ^ 2 / 2 ≤ |γ| * |δ| + lam * δ ^ 2 / 2 := by
  have hP1 : -1 ≤ P := (abs_le.mp hP).1
  have hP2 : P ≤ 1 := (abs_le.mp hP).2
  have e : γ * (-(R * γ) - δ) + lam * (-(R * γ) - δ) ^ 2 / 2 =
      -(γ ^ 2 * R * (1 + P) / 2) - P * γ * δ + lam * δ ^ 2 / 2 := by
    have hP' : P = 1 - lam * R := by linarith
    subst hP'; ring
  rw [e]
  have h1 : 0 ≤ γ ^ 2 * R * (1 + P) / 2 := by
    have : 0 ≤ 1 + P := by linarith
    positivity
  have h2 : -(P * γ * δ) ≤ |γ| * |δ| := by
    have : |P * γ * δ| ≤ |γ| * |δ| := by
      rw [abs_mul, abs_mul]
      have : |P| * |γ| ≤ 1 * |γ| := mul_le_mul_of_nonneg_right hP (abs_nonneg γ)
      nlinarith [abs_nonneg δ, abs_nonneg γ]
    linarith [neg_abs_le (P * γ * δ)]
  linarith

theorem pos_coord_U4 {lam S R P γ δ : ℝ} (hS : 0 < S) (_hlam : 0 ≤ lam) (hRP : lam * R = 1 - P)
    (hfin : S * P ^ 2 ≤ R * (1 + P) / 2) :
    S * (P * γ - lam * δ) ^ 2 ≤
      4 * (-(γ * (-(R * γ) - δ) + lam * (-(R * γ) - δ) ^ 2 / 2)) + 2 * δ ^ 2 / S +
        2 * lam * δ ^ 2 + 2 * S * (lam * δ) ^ 2 := by
  have e : γ * (-(R * γ) - δ) + lam * (-(R * γ) - δ) ^ 2 / 2 =
      -(γ ^ 2 * R * (1 + P) / 2) - P * γ * δ + lam * δ ^ 2 / 2 := by
    have hP' : P = 1 - lam * R := by linarith
    subst hP'; ring
  rw [e]
  have hmain : S * P ^ 2 * γ ^ 2 ≤ γ ^ 2 * R * (1 + P) / 2 := by
    have := mul_le_mul_of_nonneg_left hfin (sq_nonneg γ)
    linarith
  have hyoung : -(P * γ * δ) ≤ S / 2 * (P * γ) ^ 2 + δ ^ 2 / (2 * S) := by
    have h := sq_nonneg (S * (P * γ) + δ)
    rw [show S / 2 * (P * γ) ^ 2 + δ ^ 2 / (2 * S) =
      ((S * (P * γ)) ^ 2 + δ ^ 2) / (2 * S) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hsq : (P * γ - lam * δ) ^ 2 ≤ 2 * (P * γ) ^ 2 + 2 * (lam * δ) ^ 2 := by
    nlinarith [sq_nonneg (P * γ + lam * δ)]
  have hd : 2 * δ ^ 2 / S = 4 * (δ ^ 2 / (2 * S)) := by field_simp; ring
  have hS2 : S * (P * γ - lam * δ) ^ 2 ≤ 2 * S * (P * γ) ^ 2 + 2 * S * (lam * δ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hS.le
    linarith
  have e2 : S * (P * γ) ^ 2 = S * P ^ 2 * γ ^ 2 := by ring
  rw [hd]
  linarith

end OracleTemplate.ScheduleBlock
