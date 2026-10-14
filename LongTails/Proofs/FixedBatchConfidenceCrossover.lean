import LongTails.Proofs.FixedBatchConfidenceParameters

namespace OracleTemplate.FixedBatchConfidence

lemma nonvacuous_small {e δ : ℝ} (he : 0 < e) (N : ℕ)
    (hN : N < ⌊min (Real.sqrt (1 / e)) (1 / δ) / (65536 * e)⌋₊) :
    e < 1 / 128 := by
  have hf : 1 ≤ ⌊min (Real.sqrt (1 / e)) (1 / δ) / (65536 * e)⌋₊ := by omega
  have hB := (Nat.one_le_floor_iff _).mp hf
  have hd : 0 < 65536 * e := by positivity
  have hh : 65536 * e ≤ Real.sqrt (1 / e) := by
    have hm : 65536 * e ≤ min (Real.sqrt (1 / e)) (1 / δ) := by
      simpa only [one_mul] using (le_div_iff₀ hd).mp hB
    exact hm.trans (min_le_left _ _)
  by_contra hn
  have he' : 1 / 128 ≤ e := le_of_not_gt hn
  have hi : 1 / e ≤ 128 := (div_le_iff₀ he).mpr (by linarith)
  have hs : Real.sqrt (1 / e) ≤ 12 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  linarith

lemma bias_margin_small {e t : ℝ} (he : 0 < e) (he' : e < 1 / 128)
    (ht : 0 < t) (ht' : t ≤ 1 / (2048 * e)) :
    2 * e < min 1 (1 / (2 * t)) / 8 := by
  have hp := (le_div_iff₀ (by positivity : 0 < 2048 * e)).mp ht'
  have h1 : 16 * e < 1 := by linarith
  have h2 : 16 * e < 1 / (2 * t) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hm := lt_min h1 h2
  linarith

lemma bias_margin_short {e t : ℝ} (he' : e < 1 / 128)
    (ht : 0 < t) (ht' : t < 2) :
    2 * e < min 1 (1 / (2 * t)) / 8 := by
  have h1 : (1 / 4 : ℝ) < 1 := by norm_num
  have h2 : 1 / 4 < 1 / (2 * t) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
  have hm := lt_min h1 h2
  linarith

lemma large_confidence_bias {e δ n t : ℝ} (he : 0 < e) (he' : e < 1 / 128)
    (hδ : 1 / 64 ≤ δ) (hn : 0 < n) (ht : 0 < t) (htn : t ≤ 2 * n)
    (hN : n ≤ 1 / (65536 * δ * e)) :
    e < min 1 (1 / (2 * t)) / 8 := by
  have hδ0 : 0 < δ := by linarith
  have hd : 0 < 65536 * δ * e := by positivity
  have hp := (le_div_iff₀ hd).mp hN
  have hne : n * e ≤ 1 / 1024 := by
    have hmul := mul_le_mul_of_nonneg_right hδ (show 0 ≤ 65536 * n * e by positivity)
    nlinarith
  have hte : t * e ≤ 1 / 512 := by nlinarith
  have h1 : 8 * e < 1 := by linarith
  have h2 : 8 * e < 1 / (2 * t) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hm := lt_min h1 h2
  linarith

lemma scale_margin {e F η : ℝ} (he : 0 < e) (hF : 2 * e < F)
    (hη0 : 0 < η) (hη2 : η < 2) : e < F / η := by
  apply (lt_div_iff₀ hη0).mpr
  nlinarith

lemma crossover_budget_bounds {e δ : ℝ} (he : 0 < e) {N : ℕ}
    (hN : N < ⌊min (Real.sqrt (1 / e)) (1 / δ) / (65536 * e)⌋₊) :
    (N : ℝ) ≤ 1 / (65536 * e * Real.sqrt e) ∧
      (N : ℝ) ≤ 1 / (65536 * δ * e) := by
  have h := (Nat.lt_of_lt_floor hN).le
  have hd : 0 < 65536 * e := by positivity
  have h1 := h.trans (div_le_div_of_nonneg_right (min_le_left _ _) hd.le)
  have h2 := h.trans (div_le_div_of_nonneg_right (min_le_right _ _) hd.le)
  constructor
  · convert h1 using 1
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    ring
  · convert h2 using 1; ring

lemma small_step_time {e η : ℝ} {b K N : ℕ}
    (he : 0 < e) (hη : 0 < η) (hb : 0 < b) (hKN : K * b ≤ N)
    (hstep : η / b ≤ 32 * Real.sqrt e)
    (hN : (N : ℝ) ≤ 1 / (65536 * e * Real.sqrt e)) :
    η * (K : ℝ) ≤ 1 / (2048 * e) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hn : ((K * b : ℕ) : ℝ) ≤ N := by exact_mod_cast hKN
  have heq : η * (K : ℝ) = (η / b) * ((K * b : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [heq]
  calc
    _ ≤ (η / b) * (N : ℝ) := mul_le_mul_of_nonneg_left hn (div_nonneg hη.le hb0.le)
    _ ≤ (32 * Real.sqrt e) * (1 / (65536 * e * Real.sqrt e)) :=
      mul_le_mul hstep hN (by positivity) (by positivity)
    _ = 1 / (2048 * e) := by field_simp; ring

lemma rare_threshold_margin {e δ η : ℝ} {b K N : ℕ}
    (he : 0 < e) (hδ : 0 < δ) (hb : 0 < b) (hK : 0 < K)
    (hKN : K * b ≤ N) (hstep : 32 * Real.sqrt e < η / b)
    (hN : (N : ℝ) ≤ 1 / (65536 * δ * e)) :
    2 * e < min ((η / b) ^ 2 / 512)
      (1 / (16384 * δ * ((K * b : ℕ) : ℝ))) := by
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hs2 := Real.sq_sqrt he.le
  have hn : 0 < ((K * b : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hK hb
  have hnN : ((K * b : ℕ) : ℝ) ≤ N := by exact_mod_cast hKN
  have hp := (le_div_iff₀ (by positivity : 0 < 65536 * δ * e)).mp (hnN.trans hN)
  apply lt_min
  · nlinarith [sq_nonneg (η / (b : ℝ) - 32 * Real.sqrt e)]
  · apply (lt_div_iff₀ (by positivity : 0 < 16384 * δ * ((K * b : ℕ) : ℝ))).mpr
    nlinarith

lemma normalized_budget_formula {L R ε δ : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hδ : 0 < δ) :
    min (Real.sqrt (1 / (ε / (L * R ^ 2)))) (1 / δ) /
      (65536 * (ε / (L * R ^ 2))) =
        L * R ^ 2 * min (Real.sqrt (L * R ^ 2 / ε)) (1 / δ) / (65536 * ε) := by
  rw [one_div_div]
  field_simp

end OracleTemplate.FixedBatchConfidence
