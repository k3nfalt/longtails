import LongTails.Proofs.FixedBatchConfidenceDynamics

namespace OracleTemplate.FixedBatchConfidence

lemma amplitude_calibration {t δ N : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hN : 0 < N) :
    let A := min (1 / 2) (1 / (64 * t ^ 2 * δ * N))
    0 < A ∧ A ≤ 1 / 2 ∧ t * A * (8 * t * δ) * N ≤ 1 / 8 ∧
      t ^ 2 * A / 256 = min (t ^ 2 / 512) (1 / (16384 * δ * N)) := by
  let A := min (1 / 2) (1 / (64 * t ^ 2 * δ * N))
  have hden : 0 < 64 * t ^ 2 * δ * N := by positivity
  have hA0 : 0 < A := lt_min (by norm_num) (by positivity)
  have hA1 : A ≤ 1 / 2 := min_le_left _ _
  have hA2 : A * (64 * t ^ 2 * δ * N) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨hA0, hA1, by nlinarith, ?_⟩
  have he1 : t ^ 2 / 256 * (1 / 2) = t ^ 2 / 512 := by ring
  have he2 : t ^ 2 / 256 * (1 / (64 * t ^ 2 * δ * N)) =
      1 / (16384 * δ * N) := by
    field_simp
    norm_num
  change t ^ 2 * min (1 / 2) (1 / (64 * t ^ 2 * δ * N)) / 256 = _
  rw [show t ^ 2 * min (1 / 2) (1 / (64 * t ^ 2 * δ * N)) / 256 =
      (t ^ 2 / 256) * min (1 / 2) (1 / (64 * t ^ 2 * δ * N)) by ring,
    mul_min_of_nonneg _ _ (by positivity), he1, he2]

lemma amplitude_square_roots {A : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1 / 2) :
    0 ≤ Real.sqrt A ∧ 0 ≤ Real.sqrt (1 - A) ∧
      (Real.sqrt A) ^ 2 + (Real.sqrt (1 - A)) ^ 2 = 1 ∧
        1 / 2 ≤ (Real.sqrt (1 - A)) ^ 2 := by
  have hAc : 0 ≤ 1 - A := by linarith
  rw [Real.sq_sqrt hA0, Real.sq_sqrt hAc]
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, by ring, by linarith⟩

lemma prefix_threshold_calibration {t A p N : ℝ}
    (ht : 0 < t) (hA : 0 < A) (hbudget : t * A * p * N ≤ 1 / 8) :
    0 < 1 / (4 * t * A) ∧ p * N ≤ (1 / (4 * t * A)) / 2 := by
  constructor
  · positivity
  · rw [div_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * t * A * 2)).mpr
    nlinarith

lemma below_prefix_threshold {t A C : ℝ} (ht : 0 < t) (hA : 0 < A)
    (hC : C < 1 / (4 * t * A)) : t * A * C ≤ 1 / 4 := by
  have hh := (lt_div_iff₀ (by positivity : 0 < 4 * t * A)).mp hC
  nlinarith

lemma window_calibration {η δ : ℝ} {b K : ℕ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hb : 0 < b) (hK : 2 ≤ η * (K : ℝ)) :
    let m := ⌈1 / (2 * η)⌉₊
    let p := 8 * η * δ / b
    0 < m ∧ m ≤ K ∧ 0 < p ∧ p ≤ 1 / 8 ∧
      4 * δ ≤ ((m * b : ℕ) : ℝ) * p ∧ ((m * b : ℕ) : ℝ) * p ≤ 8 * δ ∧
        1 / 4 ≤ (1 - η) ^ (m - 1) := by
  intro m p
  have hm := recovery_window hη0 hη1
  have hmK : m ≤ K := by
    have hh : (m : ℝ) ≤ K := by nlinarith [hm.2.2.1]
    exact_mod_cast hh
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 / 8 := by
    apply (div_le_iff₀ hb0).mpr
    nlinarith
  have he : ((m * b : ℕ) : ℝ) * p = 8 * δ * (η * (m : ℝ)) := by
    dsimp [p]
    push_cast
    field_simp
  refine ⟨hm.1, hmK, hp0, hp1, ?_, ?_, ?_⟩
  · rw [he]
    nlinarith [hm.2.1]
  · rw [he]
    nlinarith [hm.2.2.1]
  · linarith [hm.2.2.2]

end OracleTemplate.FixedBatchConfidence
