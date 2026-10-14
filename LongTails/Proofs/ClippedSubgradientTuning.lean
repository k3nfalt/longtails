import LongTails.Algorithms.ClippedProjectedSubgradient

namespace OracleTemplate.WeaklyConvexHeavyTailed

open LongTails.Setups.WeaklyConvexHeavyTailed

lemma threshold_tail_nonneg (q : Params) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    0 ≤ q.σ * (4 * q.σ / q.ε) ^ (1 / (q.α - 1)) :=
  mul_nonneg hσ (Real.rpow_nonneg (div_nonneg (by linarith) hε.le) _)

lemma threshold_pos (q : Params) (hG : 0 < q.G) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    0 < threshold q := by
  unfold threshold
  have := threshold_tail_nonneg q hσ hε
  linarith

lemma two_G_le_threshold (q : Params) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) : 2 * q.G ≤ threshold q := by
  unfold threshold
  have := threshold_tail_nonneg q hσ hε
  linarith

lemma noiseScale_nonneg_term (q : Params) (hG : 0 < q.G) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    0 ≤ q.σ ^ q.α * (2 * threshold q) ^ (2 - q.α) :=
  mul_nonneg (Real.rpow_nonneg hσ _)
    (Real.rpow_nonneg (by linarith [threshold_pos q hG hσ hε]) _)

lemma noiseScale_pos (q : Params) (hG : 0 < q.G) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    0 < noiseScale q := by
  unfold noiseScale
  have := noiseScale_nonneg_term q hG hσ hε
  nlinarith [pow_pos hG 2]

lemma stepSize_pos (q : Params) (hρ : 0 < q.ρ) (hG : 0 < q.G) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    0 < stepSize q := by
  unfold stepSize
  have hN := noiseScale_pos q hG hσ hε
  exact div_pos (pow_pos hε 2) (mul_pos (mul_pos (by norm_num) hρ) hN)

lemma bias_le (q : Params) (hG : 0 < q.G) (hσ : 0 ≤ q.σ) (hα : 1 < q.α) (hε : 0 < q.ε) :
    q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1) ≤ q.ε / 4 := by
  have hα1 : 0 < q.α - 1 := by linarith
  have hτ := threshold_pos q hG hσ hε
  rcases eq_or_lt_of_le hσ with hσ0 | hσpos
  · rw [← hσ0, Real.zero_rpow (by linarith), zero_div]
    positivity
  · have hbase : q.σ * (4 * q.σ / q.ε) ^ (1 / (q.α - 1)) ≤ threshold q / 2 := by
      unfold threshold
      linarith
    have hb0 : 0 ≤ q.σ * (4 * q.σ / q.ε) ^ (1 / (q.α - 1)) := by positivity
    have hpow : (q.σ * (4 * q.σ / q.ε) ^ (1 / (q.α - 1))) ^ (q.α - 1) =
        q.σ ^ (q.α - 1) * (4 * q.σ / q.ε) := by
      rw [Real.mul_rpow hσ (by positivity), one_div, Real.rpow_inv_rpow (by positivity) hα1.ne']
    have hmono : (q.σ * (4 * q.σ / q.ε) ^ (1 / (q.α - 1))) ^ (q.α - 1) ≤
        (threshold q / 2) ^ (q.α - 1) :=
      Real.rpow_le_rpow hb0 hbase hα1.le
    rw [hpow] at hmono
    have hσα : q.σ ^ q.α = q.σ ^ (q.α - 1) * q.σ := by
      rw [← Real.rpow_add_one hσpos.ne' (q.α - 1)]
      congr 1; ring
    have hden : 0 < q.σ ^ (q.α - 1) * (4 * q.σ / q.ε) := by positivity
    calc q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)
        ≤ q.σ ^ q.α / (q.σ ^ (q.α - 1) * (4 * q.σ / q.ε)) :=
          div_le_div_of_nonneg_left (by positivity) hden hmono
      _ = q.ε / 4 := by
          rw [hσα]
          field_simp

lemma budget_rate (q : Params) (hρ : 0 < q.ρ) (hG : 0 < q.G) (hσ : 0 ≤ q.σ) (hα : 1 < q.α)
     (hε : 0 < q.ε) :
    4 * q.Δ / (stepSize q * (steps q + 1 : ℕ)) +
      4 * (stepSize q * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 +
        2 * q.ρ * stepSize q ^ 2 * noiseScale q) / stepSize q ≤ q.ε ^ 2 := by
  have hN := noiseScale_pos q hG hσ hε
  have hγ := stepSize_pos q hρ hG hσ hε
  have hB := bias_le q hG hσ hα hε
  have hB0 : 0 ≤ q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1) :=
    div_nonneg (Real.rpow_nonneg hσ _) (Real.rpow_nonneg (by linarith [threshold_pos q hG hσ hε]) _)
  have hk : 288 * q.ρ * q.Δ * noiseScale q / q.ε ^ 4 ≤ (steps q + 1 : ℕ) := by
    unfold steps
    push_cast
    linarith [Nat.le_ceil (288 * q.ρ * q.Δ * noiseScale q / q.ε ^ 4)]
  have hkpos : (0 : ℝ) < (steps q + 1 : ℕ) := by positivity
  have hterm1 : 4 * q.Δ / (stepSize q * (steps q + 1 : ℕ)) ≤ q.ε ^ 2 / 3 := by
    unfold stepSize
    have hden : 0 < q.ε ^ 2 / (24 * q.ρ * noiseScale q) * (steps q + 1 : ℕ) :=
      mul_pos (div_pos (pow_pos hε 2) (mul_pos (mul_pos (by norm_num) hρ) hN)) hkpos
    rw [div_le_iff₀ hden]
    have h1 : 288 * q.ρ * q.Δ * noiseScale q ≤ q.ε ^ 4 * (steps q + 1 : ℕ) := by
      rw [div_le_iff₀ (pow_pos hε 4)] at hk
      linarith
    have : q.ε ^ 2 / 3 * (q.ε ^ 2 / (24 * q.ρ * noiseScale q) * (steps q + 1 : ℕ)) =
        q.ε ^ 4 * (steps q + 1 : ℕ) / (72 * q.ρ * noiseScale q) := by
      field_simp
      ring
    rw [this, le_div_iff₀ (mul_pos (mul_pos (by norm_num) hρ) hN)]
    nlinarith [h1]
  have hterm2 : 4 * (stepSize q * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 +
      2 * q.ρ * stepSize q ^ 2 * noiseScale q) / stepSize q =
      4 * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 + 8 * q.ρ * stepSize q * noiseScale q := by
    field_simp
    ring
  have hterm3 : 8 * q.ρ * stepSize q * noiseScale q = q.ε ^ 2 / 3 := by
    unfold stepSize
    field_simp
    ring
  have hterm4 : 4 * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 ≤ q.ε ^ 2 / 4 := by
    have := pow_le_pow_left₀ hB0 hB 2
    nlinarith [this]
  rw [hterm2, hterm3]
  nlinarith [hterm1, hterm4]

end OracleTemplate.WeaklyConvexHeavyTailed
