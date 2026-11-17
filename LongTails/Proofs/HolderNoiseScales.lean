import LongTails.Proofs.DyadicHolderTuning

namespace LongTails.Proofs.HolderNoiseScales

lemma level_power_domination {η ν : ℝ} (hη : 0 < η) (hν : ν ≤ 1 / 2) (j : ℕ) :
    ((2 : ℝ) ^ j * η) ^ (2 * ν) ≤ η ^ (2 * ν - 1) * ((2 : ℝ) ^ j * η) := by
  have hb : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hp : ((2 : ℝ) ^ j) ^ (2 * ν) ≤ (2 : ℝ) ^ j := by
    simpa using Real.rpow_le_rpow_of_exponent_le hb (show 2 * ν ≤ 1 by linarith)
  have he : η ^ (2 * ν) = η ^ (2 * ν - 1) * η := by
    calc η ^ (2 * ν) = η ^ ((2 * ν - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hη, Real.rpow_one]
  rw [Real.mul_rpow (by positivity) hη.le, he]
  calc ((2 : ℝ) ^ j) ^ (2 * ν) * (η ^ (2 * ν - 1) * η)
      ≤ (2 : ℝ) ^ j * (η ^ (2 * ν - 1) * η) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by ring

lemma level_variance_domination {M η ν : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (hν : ν ≤ 1 / 2) (j : ℕ) :
    M * ((2 : ℝ) ^ j * η) ^ (2 * ν) ≤
      (M * η ^ (2 * ν - 1)) * ((2 : ℝ) ^ j * η) := by
  calc _ ≤ M * (η ^ (2 * ν - 1) * ((2 : ℝ) ^ j * η)) :=
      mul_le_mul_of_nonneg_left (level_power_domination hη hν j) hM
    _ = _ := by ring

lemma effective_scale_le {L ε ν : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hν : 0 ≤ ν) :
    (ε / (4 * L)) ^ (2 * ν - 1) ≤ 4 * (L / ε) ^ (1 - 2 * ν) := by
  rw [show 2 * ν - 1 = -(1 - 2 * ν) by ring, Real.rpow_neg_eq_inv_rpow,
    inv_div, show 4 * L / ε = 4 * (L / ε) by ring,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
  have h4 : (4 : ℝ) ^ (1 - 2 * ν) ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (show 1 - 2 * ν ≤ 1 by linarith)
  exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (by positivity) _)

end LongTails.Proofs.HolderNoiseScales
