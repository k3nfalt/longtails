import LongTails.Proofs.AcceleratedMarkovRates

namespace OracleTemplate.HeavyTailedMarkovGradient

lemma heavy_scale_identity {B σ R ε p : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (hR : 0 < R) (hε : 0 < ε) (hp : 1 < p) :
    σ ^ p * R ^ p / (ε ^ (p - 1) * ((B * σ * R / ε) ^ (p / (p - 1))) ^ (p - 1)) = ε / B ^ p := by
  have he : ε ^ p = ε ^ (p - 1) * ε := by
    calc
      _ = ε ^ ((p - 1) + 1) := by congr 1; ring
      _ = ε ^ (p - 1) * ε ^ (1 : ℝ) := Real.rpow_add hε _ _
      _ = _ := by rw [Real.rpow_one]
  rw [← Real.rpow_mul (by positivity : 0 ≤ B * σ * R / ε),
    div_mul_cancel₀ p (by linarith : p - 1 ≠ 0),
    Real.div_rpow (by positivity : 0 ≤ B * σ * R) hε.le,
    Real.mul_rpow (by positivity : 0 ≤ B * σ) hR.le, Real.mul_rpow hB.le hσ.le, he]
  have hb : B ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hB _)
  have hs : σ ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hσ _)
  have hr : R ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
  have he' : ε ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hε _)
  field_simp

lemma heavy_noise_identity {σ R ε N p : ℝ} (_hσ : 0 ≤ σ) (hR : 0 < R)
    (hε : 0 < ε) (hN : 0 < N) :
    4 * σ ^ p * R ^ (2 - p) * N ^ (p - 1) / (ε * N ^ 2 / (16 * R ^ 2)) ^ (p - 1) =
      (4 * 16 ^ (p - 1)) * (σ ^ p * R ^ p / (ε ^ (p - 1) * N ^ (p - 1))) := by
  have hr : R ^ (2 - p) * (R ^ 2) ^ (p - 1) = R ^ p := by
    rw [← Real.rpow_two R, ← Real.rpow_mul hR.le, ← Real.rpow_add hR]
    congr 1
    ring
  have hn : (N ^ 2) ^ (p - 1) = (N ^ (p - 1)) ^ 2 := by
    rw [← Real.rpow_two N, ← Real.rpow_two (N ^ (p - 1)),
      ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, mul_comm]
  rw [Real.div_rpow (by positivity : 0 ≤ ε * N ^ 2) (by positivity : 0 ≤ 16 * R ^ 2),
    Real.mul_rpow hε.le (sq_nonneg N), Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg R), hn]
  have he : ε ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hε _)
  have hn' : N ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hN _)
  have hr' : (R ^ 2) ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (sq_pos_of_pos hR) _)
  have hc : (16 : ℝ) ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp
  linear_combination σ ^ p * hr

lemma heavy_normalized_bound {σ R ε N p : ℝ} (hσ : 0 < σ) (hR : 0 < R)
    (hε : 0 < ε) (hp : 1 < p)
    (hN : (256 * σ * R / ε) ^ (p / (p - 1)) ≤ N) :
    σ ^ p * R ^ p / (ε ^ (p - 1) * N ^ (p - 1)) ≤ ε / (256 : ℝ) ^ p := by
  calc
    _ ≤ σ ^ p * R ^ p /
        (ε ^ (p - 1) * ((256 * σ * R / ε) ^ (p / (p - 1))) ^ (p - 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hN (by linarith)) (by positivity))
    _ = _ := heavy_scale_identity (by norm_num) hσ hR hε hp

lemma accelerated_heavy_noise_tuning {L σ R ε N p : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ)
    (hR : 0 < R) (hε : 0 < ε) (hN : 0 < N) (hp : 1 < p) (hp2 : p ≤ 2)
    (hbudget : (256 * σ * R / ε) ^ (p / (p - 1)) ≤ N) :
    4 * σ ^ p * R ^ (2 - p) * N ^ (p - 1) /
      (2 * L + ε * N ^ 2 / (16 * R ^ 2)) ^ (p - 1) ≤ ε / 4 := by
  by_cases hz : σ = 0
  · subst σ
    simp only [Real.zero_rpow (by linarith : p ≠ 0), mul_zero, zero_mul, zero_div]
    positivity
  have hσ' : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
  have hc : 4 * (16 : ℝ) ^ (p - 1) ≤ 64 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) (show p - 1 ≤ 1 by linarith)
    rw [Real.rpow_one] at hh
    linarith
  have hden : (256 : ℝ) ≤ 256 ^ p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 256) hp.le
  have he : ε / (256 : ℝ) ^ p ≤ ε / 256 := div_le_div_of_nonneg_left hε.le (by norm_num) hden
  calc
    _ ≤ 4 * σ ^ p * R ^ (2 - p) * N ^ (p - 1) / (ε * N ^ 2 / (16 * R ^ 2)) ^ (p - 1) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith))
    _ = (4 * 16 ^ (p - 1)) * (σ ^ p * R ^ p / (ε ^ (p - 1) * N ^ (p - 1))) :=
      heavy_noise_identity hσ hR hε hN
    _ ≤ (4 * 16 ^ (p - 1)) * (ε / (256 : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_left (heavy_normalized_bound hσ' hR hε hp hbudget) (by positivity)
    _ ≤ 64 * (ε / 256) := mul_le_mul hc he (by positivity) (by norm_num)
    _ = ε / 4 := by ring

lemma heavy_clip_identity {σ R ε V p : ℝ} (_hσ : 0 ≤ σ) (hR : 0 < R)
    (hε : 0 < ε) (hV : 0 < V) :
    2 * R * (σ ^ p / (ε * V / (2 * R)) ^ (p - 1)) =
      (2 : ℝ) ^ p * (σ ^ p * R ^ p / (ε ^ (p - 1) * V ^ (p - 1))) := by
  have hr : R * R ^ (p - 1) = R ^ p := by
    calc
      _ = R ^ (1 : ℝ) * R ^ (p - 1) := by rw [Real.rpow_one]
      _ = R ^ (1 + (p - 1)) := (Real.rpow_add hR _ _).symm
      _ = _ := by congr 1; ring
  have ht : (2 : ℝ) * 2 ^ (p - 1) = 2 ^ p := by
    calc
      _ = (2 : ℝ) ^ (1 : ℝ) * 2 ^ (p - 1) := by rw [Real.rpow_one]
      _ = 2 ^ (1 + (p - 1)) := (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = _ := by congr 1; ring
  rw [Real.div_rpow (by positivity : 0 ≤ ε * V) (by positivity : 0 ≤ 2 * R),
    Real.mul_rpow hε.le hV.le, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le]
  have he : ε ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hε _)
  have hv : V ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hV _)
  have hr' : R ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
  have ht' : (2 : ℝ) ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp
  calc
    _ = σ ^ p * (R * R ^ (p - 1)) * (2 * 2 ^ (p - 1)) := by ring
    _ = _ := by rw [hr, ht]; ring

lemma accelerated_clipping_tuning {L σ R ε p : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ)
    (hR : 0 < R) (hε : 0 < ε) (hp : 1 < p) (hp2 : p ≤ 2) :
    2 * R * (σ ^ p /
      ((4 * L * R + ε / R * (256 * σ * R / ε) ^ (p / (p - 1))) / 2) ^ (p - 1)) ≤ ε / 4 := by
  by_cases hz : σ = 0
  · subst σ
    simp only [Real.zero_rpow (by linarith : p ≠ 0), mul_zero, zero_div]
    positivity
  have hσ' : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
  let V := (256 * σ * R / ε) ^ (p / (p - 1))
  have hV : 0 < V := by dsimp [V]; positivity
  have hc : (2 : ℝ) ^ p ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 4 := by norm_num
  have hden : (256 : ℝ) ≤ 256 ^ p := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 256) hp.le
  have he : ε / (256 : ℝ) ^ p ≤ ε / 256 := div_le_div_of_nonneg_left hε.le (by norm_num) hden
  calc
    _ ≤ 2 * R * (σ ^ p / (ε * V / (2 * R)) ^ (p - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      change ε * V / (2 * R) ≤ (4 * L * R + ε / R * V) / 2
      have heq : ε * V / (2 * R) = (ε / R * V) / 2 := by ring
      rw [heq]
      linarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hL) hR]
    _ = (2 : ℝ) ^ p * (σ ^ p * R ^ p / (ε ^ (p - 1) * V ^ (p - 1))) :=
      heavy_clip_identity hσ hR hε hV
    _ = (2 : ℝ) ^ p * (ε / (256 : ℝ) ^ p) := by rw [heavy_scale_identity (by norm_num) hσ' hR hε hp]
    _ ≤ 4 * (ε / 256) := mul_le_mul hc he (by positivity) (by norm_num)
    _ ≤ ε / 4 := by linarith

lemma accelerated_mixing_tuning {L σ R ε p τ β : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ)
    (hR : 0 < R) (hε : 0 < ε) (hτ : 0 < τ) (hβ : 0 < β) (m : ℕ)
    (hbudget : τ * (256 * L * R ^ 2 / ε + 64 * (256 * σ * R / ε) ^ (p / (p - 1))) ^ (1 / β) ≤ (m : ℝ)) :
    12 * R * (4 * L * R + ε / R * (256 * σ * R / ε) ^ (p / (p - 1))) *
      (1 + (m : ℝ) / τ) ^ (-β) ≤ ε / 4 := by
  let V := (256 * σ * R / ε) ^ (p / (p - 1))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hH : 0 < 256 * L * R ^ 2 / ε + 64 * V := by positivity
  have hh := polynomial_mixing_tuning hτ hβ hH m hbudget
  calc
    _ ≤ 12 * R * (4 * L * R + ε / R * V) * (1 / (256 * L * R ^ 2 / ε + 64 * V)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 3 * ε / 16 := by field_simp; ring
    _ ≤ ε / 4 := by linarith

lemma accelerated_markov_tuning {L σ R ε p τ β N : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ)
    (hR : 0 < R) (hε : 0 < ε) (hτ : 0 < τ) (hβ : 0 < β)
    (hp : 1 < p) (hp2 : p ≤ 2) (hN : 0 < N)
    (hdet : Real.sqrt (32 * L * R ^ 2 / ε) ≤ N)
    (hnoise : (256 * σ * R / ε) ^ (p / (p - 1)) ≤ N) (m : ℕ)
    (hmix : τ * (256 * L * R ^ 2 / ε + 64 * (256 * σ * R / ε) ^ (p / (p - 1))) ^ (1 / β) ≤ (m : ℝ)) :
    let D := 2 * L + ε * N ^ 2 / (16 * R ^ 2)
    let C := 4 * L * R + ε / R * (256 * σ * R / ε) ^ (p / (p - 1))
    2 * D * R ^ 2 / N ^ 2 + 4 * σ ^ p * R ^ (2 - p) * N ^ (p - 1) / D ^ (p - 1) +
      (2 * R * (σ ^ p / (C / 2) ^ (p - 1)) + 12 * R * C * (1 + (m : ℝ) / τ) ^ (-β)) ≤ ε := by
  have h₁ := accelerated_initial_tuning hL hR hε hN hdet
  have h₂ := accelerated_heavy_noise_tuning hL hσ hR hε hN hp hp2 hnoise
  have h₃ := accelerated_clipping_tuning hL hσ hR hε hp hp2
  have h₄ := accelerated_mixing_tuning hL hσ hR hε hτ hβ m hmix
  dsimp
  linarith only [h₁, h₂, h₃, h₄]

end OracleTemplate.HeavyTailedMarkovGradient
