import LongTails.Proofs.ManyConstraintTuning

namespace LongTails.Proofs.ManyConstraintBudget

open LongTails.Proofs.ManyConstraintTuning OracleTemplate.Katyusha

variable {m : ℕ} [NeZero m] {κ σ ε L R : ℝ}

lemma t_le (hκ : 1 ≤ κ) (hσ : 0 ≤ σ) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R) :
    (tT m κ σ ε L R : ℝ) ≤
      1 + 272 * Real.sqrt (κ / m) * (σ * R / ε + R * Real.sqrt (L / ε)) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  set Γ := σ * R / ε + R * Real.sqrt (L / ε)
  have hΓ : 0 ≤ Γ := by positivity
  have hA : Real.sqrt (LtT κ σ ε L / (((2 * m : ℕ) : ℝ) * muT ε R)) ≤
      272 * Real.sqrt (κ / m) * Γ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e1 : (272 * Real.sqrt (κ / m) * Γ) ^ 2 = 73984 * (κ / m) * Γ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    have e2 : Γ ^ 2 ≥ σ ^ 2 * R ^ 2 / ε ^ 2 + R ^ 2 * L / ε := by
      have hs : Real.sqrt (L / ε) ^ 2 = L / ε := Real.sq_sqrt (by positivity)
      have : Γ ^ 2 = (σ * R / ε) ^ 2 + 2 * (σ * R / ε) * (R * Real.sqrt (L / ε)) +
          R ^ 2 * Real.sqrt (L / ε) ^ 2 := by simp only [Γ]; ring
      rw [this, hs]
      have : 0 ≤ 2 * (σ * R / ε) * (R * Real.sqrt (L / ε)) := by positivity
      have e : (σ * R / ε) ^ 2 = σ ^ 2 * R ^ 2 / ε ^ 2 := by ring
      have e' : R ^ 2 * (L / ε) = R ^ 2 * L / ε := by ring
      linarith
    rw [e1]
    have hlhs : LtT κ σ ε L / (((2 * m : ℕ) : ℝ) * muT ε R) =
        192 * R ^ 2 * LtT κ σ ε L / (m * ε) := by
      unfold muT; push_cast; field_simp; ring
    have hLt : LtT κ σ ε L ≤ 385 * κ * (σ ^ 2 / ε + L) := by
      unfold LtT betaT
      have : 0 ≤ σ ^ 2 / ε := by positivity
      nlinarith
    rw [hlhs, div_le_iff₀ (by positivity)]
    have h1 : 192 * R ^ 2 * LtT κ σ ε L ≤ 192 * R ^ 2 * (385 * κ * (σ ^ 2 / ε + L)) :=
      mul_le_mul_of_nonneg_left hLt (by positivity)
    have h2 : 192 * R ^ 2 * (385 * κ * (σ ^ 2 / ε + L)) =
        73920 * κ * (σ ^ 2 * R ^ 2 / ε ^ 2 + R ^ 2 * L / ε) * ε := by
      field_simp; ring
    have h3 : 73984 * (κ / m) * Γ ^ 2 * (m * ε) = 73984 * κ * Γ ^ 2 * ε := by
      field_simp
    rw [h3]
    have h4 : 73920 * κ * (σ ^ 2 * R ^ 2 / ε ^ 2 + R ^ 2 * L / ε) * ε ≤
        73984 * κ * Γ ^ 2 * ε := by
      have : 0 ≤ σ ^ 2 * R ^ 2 / ε ^ 2 + R ^ 2 * L / ε := by positivity
      have hk : 0 ≤ κ * ε := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left e2 hk]
    linarith
  unfold tT tuning
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · have : 0 ≤ 272 * Real.sqrt (κ / m) * Γ := by positivity
    linarith
  · have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg
      (LtT κ σ ε L / (((2 * m : ℕ) : ℝ) * muT ε R)))
    change ((⌈Real.sqrt (LtT κ σ ε L / (((2 * m : ℕ) : ℝ) * muT ε R))⌉₊ : ℕ) : ℝ) ≤ _
    linarith

lemma logX_bounds (hκ : 1 ≤ κ) (hσ : 0 ≤ σ) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R) :
    0 ≤ logX κ σ ε L R ∧ logX κ σ ε L R ≤
      Real.log (50000 * κ * (1 + σ * R / ε + L * R ^ 2 / ε) ^ 2) := by
  have hLt : LtT κ σ ε L ≤ 385 * κ * (σ ^ 2 / ε + L) := by
    unfold LtT betaT
    have : 0 ≤ σ ^ 2 / ε := by positivity
    nlinarith
  have hLt0 := LtT_pos (σ := σ) hκ hε hL
  have hX0 : 1 ≤ 64 * (2 * σ * R + 2 * LtT κ σ ε L * R ^ 2 + 3 * ε) / ε := by
    rw [le_div_iff₀ hε]
    have : 0 ≤ 2 * σ * R + 2 * LtT κ σ ε L * R ^ 2 := by positivity
    nlinarith
  refine ⟨Real.log_nonneg hX0, Real.log_le_log (by linarith) ?_⟩
  set a := σ * R / ε
  set c := L * R ^ 2 / ε
  have ha : 0 ≤ a := by positivity
  have hc : 0 ≤ c := by positivity
  have hX : 64 * (2 * σ * R + 2 * LtT κ σ ε L * R ^ 2 + 3 * ε) / ε =
      64 * (2 * a + 2 * (LtT κ σ ε L * R ^ 2 / ε) + 3) := by
    simp only [a]; field_simp
  have hB : LtT κ σ ε L * R ^ 2 / ε ≤ 385 * κ * (a ^ 2 + c) := by
    have : 385 * κ * (a ^ 2 + c) = 385 * κ * (σ ^ 2 / ε + L) * R ^ 2 / ε := by
      simp only [a, c]; field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ hε.le
    exact mul_le_mul_of_nonneg_right hLt (by positivity)
  rw [hX]
  have hsq : 1 + 2 * a + a ^ 2 + c ≤ (1 + a + c) ^ 2 := by nlinarith
  have hk : 0 ≤ κ - 1 := by linarith
  have : 2 * a + 770 * κ * (a ^ 2 + c) + 3 ≤ 770 * κ * (1 + a + c) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 770 * κ by linarith),
      mul_nonneg hk ha]
  nlinarith

lemma ST_le (hκ : 1 ≤ κ) (hσ : 0 ≤ σ) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R) :
    ManyConstraintTuning.ST m κ σ ε L R ≤ ⌈(13 + 3264 * Real.sqrt (κ / m) * (σ * R / ε + R * Real.sqrt (L / ε))) *
      Real.log (50000 * κ * (1 + σ * R / ε + L * R ^ 2 / ε) ^ 2)⌉₊ := by
  unfold ManyConstraintTuning.ST
  apply Nat.ceil_mono
  obtain ⟨h0, h1⟩ := logX_bounds (σ := σ) hκ hσ hε hL hR
  have ht := t_le (m := m) hκ hσ hε hL hR
  have hpos : 0 ≤ 12 * (tT m κ σ ε L R : ℝ) + 1 := by positivity
  calc (12 * (tT m κ σ ε L R : ℝ) + 1) * logX κ σ ε L R
      ≤ (12 * (tT m κ σ ε L R : ℝ) + 1) *
          Real.log (50000 * κ * (1 + σ * R / ε + L * R ^ 2 / ε) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hpos
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (h0.trans h1)
        linarith

lemma bT_le (hκ : 1 ≤ κ) (hσ : 0 ≤ σ) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R) :
    bT m κ σ ε L R ≤
      ⌈3 + 544 * (σ * R / ε + R * Real.sqrt (L / ε)) / Real.sqrt (m * κ)⌉₊ := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hκ0 : 0 < κ := by linarith
  set Γ := σ * R / ε + R * Real.sqrt (L / ε)
  have hΓ : 0 ≤ Γ := by positivity
  have ht := t_le (m := m) hκ hσ hε hL hR
  have hLt0 := LtT_pos (σ := σ) hκ hε hL
  have hT0 := tT_pos (m := m) (κ := κ) (σ := σ) (ε := ε) (L := L) (R := R)
  have hratio : (tT m κ σ ε L R : ℝ) * (768 * σ ^ 2 / ε + 2 * L) / LtT κ σ ε L ≤
      2 * (tT m κ σ ε L R : ℝ) / κ := by
    rw [div_le_div_iff₀ hLt0 hκ0]
    have hb : 384 * κ * (σ ^ 2 / ε + L) ≤ LtT κ σ ε L := by unfold LtT betaT; linarith
    have : (768 * σ ^ 2 / ε + 2 * L) * κ ≤ 2 * (384 * κ * (σ ^ 2 / ε + L)) := by
      have : 0 ≤ σ ^ 2 / ε := by positivity
      have e : 768 * σ ^ 2 / ε = 768 * (σ ^ 2 / ε) := by ring
      rw [e]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * (tT m κ σ ε L R : ℝ) by positivity)]
  have hsk : Real.sqrt (κ / m) / κ = 1 / Real.sqrt (m * κ) := by
    rw [Real.sqrt_div hκ0.le, Real.sqrt_mul hm.le]
    have : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ0
    have : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ0.le
    field_simp
    linarith
  have h2 : 2 * (tT m κ σ ε L R : ℝ) / κ ≤ 3 + 544 * Γ / Real.sqrt (m * κ) := by
    have : 2 * (tT m κ σ ε L R : ℝ) / κ ≤
        2 / κ + 544 * Γ * (Real.sqrt (κ / m) / κ) := by
      have e : 2 / κ + 544 * Γ * (Real.sqrt (κ / m) / κ) =
          2 * (1 + 272 * Real.sqrt (κ / m) * Γ) / κ := by field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) hκ0.le
    rw [hsk] at this
    have hk2 : 2 / κ ≤ 2 := by rw [div_le_iff₀ hκ0]; linarith
    have e : 544 * Γ * (1 / Real.sqrt (m * κ)) = 544 * Γ / Real.sqrt (m * κ) := by ring
    linarith
  unfold bT
  apply max_le
  · apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.pos_iff_ne_zero.mp
    apply Nat.lt_ceil.mpr
    push_cast
    have : 0 ≤ 544 * Γ / Real.sqrt (m * κ) := by positivity
    linarith
  · exact Nat.ceil_mono (hratio.trans h2)

end LongTails.Proofs.ManyConstraintBudget
