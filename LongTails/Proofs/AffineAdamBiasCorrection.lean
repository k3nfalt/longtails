import LongTails.Proofs.AffineAdamHistory

namespace LongTails.Proofs.AffineAdamBiasCorrection

noncomputable def memory (β : ℝ) (t : ℕ) : ℝ := β * (1 - β ^ t) / (1 - β ^ (t + 1))

lemma correction_pos {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    0 < 1 - β ^ (t + 1) := by
  exact sub_pos.mpr (pow_lt_one₀ hβ hβ1 (by omega))

lemma memory_bounds {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    0 ≤ memory β t ∧ memory β t ≤ β := by
  have hp : β ^ t ≤ 1 := pow_le_one₀ hβ hβ1.le
  have hd := correction_pos hβ hβ1 t
  constructor
  · exact div_nonneg (mul_nonneg hβ (sub_nonneg.mpr hp)) hd.le
  · rw [memory, div_le_iff₀ hd, pow_succ]
    nlinarith [mul_nonneg (pow_nonneg hβ t) (sub_nonneg.mpr hβ1.le)]

lemma corrected_recurrence {β u z : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (t : ℕ) (hu : t = 0 → u = 0) :
    (β * u + (1 - β) * z) / (1 - β ^ (t + 1)) =
      memory β t * (u / (1 - β ^ t)) + (1 - memory β t) * z := by
  cases t with
  | zero => simp [memory, hu rfl, (sub_pos.mpr hβ1).ne']
  | succ t =>
    have h0 := (correction_pos hβ hβ1 t).ne'
    have h1 := (correction_pos hβ hβ1 (t + 1)).ne'
    unfold memory
    field_simp
    ring

lemma corrected_momentum_transport {a m z g old r : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (har : a ≤ r) :
    |a * m + (1 - a) * z - g| ≤
      r * |m - old| + r * |g - old| + |z - g| := by
  have he : a * m + (1 - a) * z - g = a * (m - g) + (1 - a) * (z - g) := by ring
  rw [he]
  have ht := abs_add_le (a * (m - g)) ((1 - a) * (z - g))
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (sub_nonneg.mpr ha1)] at ht
  have hd : |m - g| ≤ |m - old| + |g - old| := by
    simpa only [abs_sub_comm old g] using abs_sub_le m old g
  have hmul := mul_le_mul_of_nonneg_left hd ha
  have hrate := mul_le_mul_of_nonneg_right har
    (add_nonneg (abs_nonneg (m - old)) (abs_nonneg (g - old)))
  nlinarith [mul_nonneg ha (abs_nonneg (z - g))]

end LongTails.Proofs.AffineAdamBiasCorrection
