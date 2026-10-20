import LongTails.Proofs.RiverValleySequences

namespace OracleTemplate.RiverValley

lemma pow_le_inv_R {x : ℝ} {K : ℕ} {R : ℝ} (hx1 : x ≤ 1) (hR : 0 < R)
    (hK : Real.log R ≤ x * K) : (1 - x) ^ K ≤ 1 / R := by
  have h1 : (1 - x) ^ K ≤ Real.exp (-x) ^ K :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-x)]) K
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp (K * -x) ≤ Real.exp (-Real.log R) := Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log hR] at h2
  rw [one_div]; linarith

set_option maxHeartbeats 1000000 in
lemma tune_final {μ Lv Lh ε lR R Mc HA C SA A1 θA2 LA2 Γ : ℝ} (hμ : 0 < μ) (hμLv : μ ≤ Lv)
    (hε : 0 < ε) (hlR : 1 ≤ lR) (hRl : lR = Real.log R) (hR3 : 3 ≤ R) (hMc : 0 ≤ Mc)
    (hHA : HA ≤ Mc) (hC0 : 0 ≤ C) (hC : C ≤ Mc)
    (hSA : SA ≤ μ / 30) (hLh : 0 ≤ Lh) (hval : 32 * Lh * lR ≤ μ) (hΓ : Γ ≤ 1 / 16)
    (hA1 : A1 ≤ 3 * ε ^ 2 / 64) (hθA2 : θA2 ≤ ε ^ 2 / 1024 + ε ^ 2 / 64) (hA10 : 0 ≤ A1)
    (hθA20 : 0 ≤ θA2) (hLA20 : 0 ≤ LA2) (hLA2 : LA2 ≤ ε ^ 2 * R / 12) :
    let ηc := 1 / (8 * Lv + 256 * lR * Mc / (μ * ε ^ 2))
    let Kc := ⌈2 * lR * (8 * Lv + 256 * lR * Mc / (μ * ε ^ 2)) / μ⌉₊
    let Pb := 2 * (A1 + θA2 + Kc * ηc ^ 2 * C)
    0 ≤ ηc ∧ 8 * ηc * Lv ≤ 1 ∧ 10 * Lh * ηc * Kc ≤ 1 ∧
      Real.sqrt Pb + (1 + Γ) * Real.sqrt ((1 - ηc * μ / 2) ^ Kc * LA2 +
        2 / μ * (SA * Pb + ηc * HA)) ≤ ε := by
  intro ηc Kc Pb
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  set Dc := 8 * Lv + 256 * lR * Mc / (μ * ε ^ 2)
  have hX : 0 ≤ 256 * lR * Mc / (μ * ε ^ 2) := by
    have : 0 ≤ lR := by linarith
    positivity
  have hDc : 0 < Dc := by simp only [Dc]; linarith
  have hηcD : ηc * Dc = 1 := by have := hDc.ne'; simp only [ηc, Dc] at *; field_simp
  have hηc0 : 0 < ηc := by simp only [ηc]; positivity
  have hE : ηc * Dc = 8 * ηc * Lv + ηc * (256 * lR * Mc / (μ * ε ^ 2)) := by simp only [Dc]; ring
  have hηc8 : 8 * ηc * Lv ≤ 1 := by
    have := mul_nonneg hηc0.le hX; linarith
  have hηcM : ηc * (256 * lR * Mc) ≤ μ * ε ^ 2 := by
    have h1 : ηc * (256 * lR * Mc / (μ * ε ^ 2)) ≤ 1 := by
      have : 0 ≤ 8 * ηc * Lv := by positivity
      linarith
    have e : ηc * (256 * lR * Mc / (μ * ε ^ 2)) = ηc * (256 * lR * Mc) / (μ * ε ^ 2) := by ring
    rw [e, div_le_one (by positivity)] at h1
    exact h1
  -- Kc
  have hK1 : 2 * lR * Dc / μ ≤ Kc := Nat.le_ceil _
  have hK2 : (Kc : ℝ) < 2 * lR * Dc / μ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hηK : ηc * Kc ≤ 2 * lR / μ + 1 / (8 * Lv) := by
    have h1 := mul_le_mul_of_nonneg_left hK2.le hηc0.le
    have e : ηc * (2 * lR * Dc / μ + 1) = 2 * lR / μ * (ηc * Dc) + ηc := by ring
    rw [e, hηcD] at h1
    have : ηc ≤ 1 / (8 * Lv) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hlRμ : 1 / (8 * Lv) ≤ lR / μ := by
    rw [div_le_div_iff₀ (by positivity) hμ]; nlinarith
  have hηK3 : ηc * Kc ≤ 3 * lR / μ := by
    have : 2 * lR / μ + lR / μ = 3 * lR / μ := by ring
    linarith
  have hLhK : 10 * Lh * ηc * Kc ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hηK (by positivity : (0:ℝ) ≤ 10 * Lh)
    have a : 10 * Lh * (2 * lR / μ) ≤ 5 / 8 := by
      rw [show 10 * Lh * (2 * lR / μ) = 20 * (Lh * lR) / μ by ring, div_le_iff₀ hμ]; linarith
    have b : 10 * Lh * (1 / (8 * Lv)) ≤ 1 / 8 := by
      have hLhLv : 32 * Lh ≤ Lv := by
        have := mul_le_mul_of_nonneg_left hlR (by positivity : (0:ℝ) ≤ 32 * Lh); linarith
      rw [show 10 * Lh * (1 / (8 * Lv)) = 10 * Lh / (8 * Lv) by ring, div_le_iff₀ (by positivity)]
      linarith
    have e : 10 * Lh * ηc * Kc = 10 * Lh * (ηc * Kc) := by ring
    rw [e]; linarith
  refine ⟨hηc0.le, hηc8, hLhK, ?_⟩
  -- Pb
  have hKC : Kc * ηc ^ 2 * C ≤ 3 * ε ^ 2 / 256 := by
    have e : Kc * ηc ^ 2 * C = (ηc * Kc) * (ηc * C) := by ring
    have h1 : ηc * C ≤ μ * ε ^ 2 / (256 * lR) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hC hηc0.le
      nlinarith
    rw [e]
    have h2 := mul_le_mul hηK3 h1 (by positivity) (by positivity)
    have e2 : 3 * lR / μ * (μ * ε ^ 2 / (256 * lR)) = 3 * ε ^ 2 / 256 := by
      have : lR ≠ 0 := by linarith
      field_simp
    linarith
  have hPb : Pb ≤ 4 * ε ^ 2 / 25 := by
    simp only [Pb]; nlinarith [sq_nonneg ε]
  have hPb0 : 0 ≤ Pb := by simp only [Pb]; positivity
  -- Qb
  have hr : (1 - ηc * μ / 2) ^ Kc ≤ 1 / R := by
    apply pow_le_inv_R (by nlinarith) (by linarith)
    rw [← hRl]
    have h1 := mul_le_mul_of_nonneg_left hK1 (by positivity : (0:ℝ) ≤ ηc * μ / 2)
    have e : ηc * μ / 2 * (2 * lR * Dc / μ) = lR * (ηc * Dc) := by field_simp
    rw [e, hηcD] at h1; linarith
  have hr0 : 0 ≤ (1 - ηc * μ / 2) ^ Kc := pow_nonneg (by nlinarith) _
  have hQ1 : (1 - ηc * μ / 2) ^ Kc * LA2 ≤ ε ^ 2 / 12 := by
    have h1 := mul_le_mul hr hLA2 hLA20 (by positivity)
    have e : 1 / R * (ε ^ 2 * R / 12) = ε ^ 2 / 12 := by
      have : R ≠ 0 := by linarith
      field_simp
    linarith
  have hQ2 : 2 / μ * (SA * Pb) ≤ 8 * ε ^ 2 / 750 := by
    have h1 := mul_le_mul hSA hPb hPb0 (by positivity)
    have e : 2 / μ * (μ / 30 * (4 * ε ^ 2 / 25)) = 8 * ε ^ 2 / 750 := by field_simp; ring
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 / μ)
    linarith
  have hQ3 : 2 / μ * (ηc * HA) ≤ ε ^ 2 / 128 := by
    have h1 : ηc * HA ≤ μ * ε ^ 2 / 256 := by
      have := mul_le_mul_of_nonneg_left hHA hηc0.le
      have : ηc * Mc ≤ ηc * (lR * Mc) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlR hMc) hηc0.le
        nlinarith
      nlinarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 / μ)
    have e : 2 / μ * (μ * ε ^ 2 / 256) = ε ^ 2 / 128 := by field_simp; ring
    linarith
  have hQ : (1 - ηc * μ / 2) ^ Kc * LA2 + 2 / μ * (SA * Pb + ηc * HA) ≤ (ε / 3) ^ 2 := by
    have e : 2 / μ * (SA * Pb + ηc * HA) = 2 / μ * (SA * Pb) + 2 / μ * (ηc * HA) := by ring
    rw [e]; nlinarith [sq_nonneg ε]
  have hs1 : Real.sqrt Pb ≤ 2 * ε / 5 := by
    rw [show 4 * ε ^ 2 / 25 = (2 * ε / 5) ^ 2 by ring] at hPb
    exact Real.sqrt_le_sqrt hPb |>.trans (by rw [Real.sqrt_sq (by positivity)])
  have hs2 : Real.sqrt ((1 - ηc * μ / 2) ^ Kc * LA2 + 2 / μ * (SA * Pb + ηc * HA)) ≤ ε / 3 :=
    Real.sqrt_le_sqrt hQ |>.trans (by rw [Real.sqrt_sq (by positivity)])
  have := mul_le_mul (by linarith : 1 + Γ ≤ 17 / 16) hs2 (Real.sqrt_nonneg _) (by norm_num)
  linarith

end OracleTemplate.RiverValley
