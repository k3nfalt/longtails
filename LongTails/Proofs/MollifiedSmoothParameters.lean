import LongTails.Proofs.MollifiedSmoothHardFamily

namespace LongTails.Proofs.MollifiedSmoothParameters

noncomputable def amplitude (R : ℝ) (m : ℕ) : ℝ := R / (4 * Real.sqrt m)
noncomputable def deadWidth (R : ℝ) (m : ℕ) : ℝ := amplitude R m / (8 * m)
noncomputable def radius (R : ℝ) (m : ℕ) : ℝ := deadWidth R m / 64

lemma amplitude_pos (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) : 0 < amplitude R m := by
  unfold amplitude
  positivity

lemma deadWidth_pos (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) : 0 < deadWidth R m := by
  have ha := amplitude_pos R hR m hm
  unfold deadWidth
  positivity

lemma radius_pos (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) : 0 < radius R m := by
  have hd := deadWidth_pos R hR m hm
  unfold radius
  positivity

noncomputable def kernel (d : ℕ) (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := radius R m / 2
  rOut := radius R m
  rIn_pos := by have := radius_pos R hR m hm; positivity
  rIn_lt_rOut := by have := radius_pos R hR m hm; linarith

lemma amplitude_square (R : ℝ) (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * amplitude R m ^ 2 = (R / 4) ^ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold amplitude
  rw [div_pow, mul_pow, Real.sq_sqrt hm0.le]
  field_simp

lemma width_identity (R : ℝ) (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * deadWidth R m = amplitude R m / 8 := by
  unfold deadWidth
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma radius_bounds (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) :
    radius R m ≤ deadWidth R m / 16 ∧ radius R m ≤ (R / 4) / 128 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 ≤ Real.sqrt m := by
    have hh := Real.sqrt_le_sqrt hm1
    simpa only [Real.sqrt_one] using hh
  have ha := amplitude_pos R hR m hm
  have hd := deadWidth_pos R hR m hm
  have haR : amplitude R m ≤ R / 4 := by
    unfold amplitude
    apply div_le_div_of_nonneg_left hR.le (by norm_num)
    linarith
  have hdR : deadWidth R m ≤ R / 32 := by
    unfold deadWidth
    apply le_trans (div_le_div_of_nonneg_left ha.le (by norm_num : (0 : ℝ) < 8) (by linarith))
    linarith
  unfold radius
  constructor <;> linarith

lemma radius_gap (R : ℝ) (m : ℕ) (hm : 0 < m) :
    radius R m ^ 2 / 2 ≤ amplitude R m ^ 2 / (16384 * m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold radius deadWidth
  field_simp
  nlinarith [sq_nonneg (amplitude R m), mul_nonneg (sq_nonneg (amplitude R m)) (sub_nonneg.mpr hm1)]

lemma hiding_ratio (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) :
    R ^ 2 / (deadWidth R m / 8) ^ 2 = 65536 * (m : ℝ) ^ 3 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := Real.sq_sqrt hm0.le
  have hsn := (Real.sqrt_pos.mpr hm0).ne'
  unfold deadWidth amplitude
  field_simp
  nlinarith only [hs]

lemma hiding_dimension (m : ℕ) (hm : 0 < m) :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * (65536 * (m : ℝ) ^ 3) ≤ 262144 * (m : ℝ) ^ 5 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hh : (m : ℝ) ≤ (m : ℝ) ^ 5 := by
    simpa using pow_le_pow_right₀ hm1 (show 1 ≤ 5 by norm_num)
  nlinarith only [hh, pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 5]

lemma floor_length (L R ε : ℝ)
    (hlarge : 8192 ≤ Real.sqrt (L * R ^ 2 / ε)) (N : ℕ)
    (hN : N ≤ ⌊Real.sqrt (L * R ^ 2 / ε) / 16384⌋₊) :
    ((N + 1 : ℕ) : ℝ) ≤ Real.sqrt (L * R ^ 2 / ε) / 4096 := by
  have hh := Nat.floor_le (show 0 ≤ Real.sqrt (L * R ^ 2 / ε) / 16384 by positivity)
  have hn : (N : ℝ) ≤ (⌊Real.sqrt (L * R ^ 2 / ε) / 16384⌋₊ : ℝ) := by exact_mod_cast hN
  push_cast
  linarith

lemma accuracy_gap (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (m : ℕ) (hm : 0 < m)
    (hlen : (m : ℝ) ≤ Real.sqrt (L * R ^ 2 / ε) / 4096) :
    2 * ε < L * amplitude R m ^ 2 / (16384 * m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := Real.sq_sqrt (show 0 ≤ L * R ^ 2 / ε by positivity)
  have hms := pow_le_pow_left₀ hm0.le hlen 2
  have hsq : (4096 : ℝ) ^ 2 * (m : ℝ) ^ 2 * ε ≤ L * R ^ 2 := by
    rw [div_pow, hs] at hms
    have hh : (4096 : ℝ) ^ 2 * (m : ℝ) ^ 2 ≤ L * R ^ 2 / ε := by nlinarith only [hms]
    exact (le_div_iff₀ hε).mp hh
  have ha := amplitude_square R m hm
  apply (lt_div_iff₀ (by positivity : 0 < 16384 * (m : ℝ))).mpr
  have hpos : 0 < ε * (m : ℝ) ^ 2 := by positivity
  apply (mul_lt_mul_iff_right₀ hm0).mp
  have he := congrArg (fun t : ℝ => 16 * L * t) ha
  nlinarith only [hsq, he, hpos]

end LongTails.Proofs.MollifiedSmoothParameters
