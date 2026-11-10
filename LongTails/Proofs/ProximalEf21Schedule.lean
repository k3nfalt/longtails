import LongTails.Proofs.ProximalEf21ScalarCore

open scoped BigOperators

namespace LongTails.Proofs.ProximalEf21Schedule

open LongTails.Proofs.ProximalEf21ScalarCore

lemma real_two_power_sum (s : ℕ) :
    (∑ j ∈ Finset.range s, (2 : ℝ) ^ j) = (2 : ℝ) ^ s - 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma real_four_power_sum (s : ℕ) :
    (∑ j ∈ Finset.range s, (4 : ℝ) ^ j) = ((4 : ℝ) ^ s - 1) / 3 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma dyadic_inverse_sums {L : ℝ} (hL : 0 < L) (s : ℕ) :
    (∑ j ∈ Finset.range (s + 1), 1 / (2 * L / (2 : ℝ) ^ j)) ≤
        2 / (2 * L / (2 : ℝ) ^ s) ∧
    (∑ j ∈ Finset.range (s + 1), 1 / (2 * L / (2 : ℝ) ^ j) ^ 2) ≤
        4 / (3 * (2 * L / (2 : ℝ) ^ s) ^ 2) := by
  have hpower : ∀ j : ℕ, (0 : ℝ) < 2 ^ j := fun j => pow_pos (by norm_num) j
  have hinv : ∀ j : ℕ, 1 / (2 * L / (2 : ℝ) ^ j) = (2 : ℝ) ^ j / (2 * L) := by
    intro j
    field_simp [ne_of_gt hL, ne_of_gt (hpower j)]
  have hinv₂ : ∀ j : ℕ, 1 / (2 * L / (2 : ℝ) ^ j) ^ 2 =
      (4 : ℝ) ^ j / (4 * L ^ 2) := by
    intro j
    have hp : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    field_simp [ne_of_gt hL, ne_of_gt (hpower j)]
    nlinarith [hp]
  constructor
  · simp_rw [hinv]
    rw [← Finset.sum_div, real_two_power_sum, pow_succ]
    have hr : 2 / (2 * L / (2 : ℝ) ^ s) = 2 * (2 : ℝ) ^ s / (2 * L) := by
      field_simp [ne_of_gt hL, ne_of_gt (hpower s)]
    rw [hr]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  · simp_rw [hinv₂]
    rw [← Finset.sum_div, real_four_power_sum, pow_succ]
    have hr : 4 / (3 * (2 * L / (2 : ℝ) ^ s) ^ 2) =
        (4 * (4 : ℝ) ^ s / 3) / (4 * L ^ 2) := by
      have hh := hinv₂ s
      field_simp [ne_of_gt hL, ne_of_gt (hpower s)] at hh ⊢
      nlinarith only [hh]
    rw [hr]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

lemma dyadic_ceiling_bounds {a : ℝ} (ha : 1 ≤ a) :
    a ≤ (2 : ℝ) ^ ⌈Real.log a / Real.log 2⌉₊ ∧
      (2 : ℝ) ^ ⌈Real.log a / Real.log 2⌉₊ < 2 * a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha
  have hq : 0 ≤ Real.log a / Real.log 2 := div_nonneg hlog (le_of_lt hlog₂)
  have hlo := Nat.le_ceil (Real.log a / Real.log 2)
  have hhi := Nat.ceil_lt_add_one hq
  have hmullo := mul_le_mul_of_nonneg_right hlo (le_of_lt hlog₂)
  have hmulhi := mul_lt_mul_of_pos_right hhi hlog₂
  have hcancel : Real.log a / Real.log 2 * Real.log 2 = Real.log a := by
    field_simp [ne_of_gt hlog₂]
  rw [hcancel] at hmullo
  have hexpand : (Real.log a / Real.log 2 + 1) * Real.log 2 =
      Real.log a + Real.log 2 := by
    field_simp [ne_of_gt hlog₂]
    <;> ring
  rw [hexpand] at hmulhi
  constructor
  · calc
      a = Real.exp (Real.log a) := (Real.exp_log ha0).symm
      _ ≤ Real.exp ((⌈Real.log a / Real.log 2⌉₊ : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hmullo
      _ = (2 : ℝ) ^ ⌈Real.log a / Real.log 2⌉₊ := by
        rw [← Real.log_pow]
        exact Real.exp_log (pow_pos (by norm_num) _)
  · have he : (2 : ℝ) ^ ⌈Real.log a / Real.log 2⌉₊ =
        Real.exp ((⌈Real.log a / Real.log 2⌉₊ : ℝ) * Real.log 2) := by
      rw [← Real.log_pow]
      exact (Real.exp_log (pow_pos (by norm_num) _)).symm
    rw [he]
    calc
      Real.exp ((⌈Real.log a / Real.log 2⌉₊ : ℝ) * Real.log 2) <
          Real.exp (Real.log a + Real.log 2) := Real.exp_lt_exp.mpr hmulhi
      _ = 2 * a := by rw [Real.exp_add, Real.exp_log ha0,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring

lemma terminal_regularization_bounds {L R ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hεupper : ε ≤ L * R ^ 2) :
    let S := ⌈Real.log (32768 * L * R ^ 2 / ε) / Real.log 2⌉₊
    ε / (32768 * R ^ 2) < 2 * L / (2 : ℝ) ^ S ∧
      2 * L / (2 : ℝ) ^ S ≤ ε / (16384 * R ^ 2) := by
  dsimp
  have ha : 1 ≤ 32768 * L * R ^ 2 / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith
  obtain ⟨hlo, hhi⟩ := dyadic_ceiling_bounds ha
  have hp : (0 : ℝ) < 2 ^ ⌈Real.log (32768 * L * R ^ 2 / ε) / Real.log 2⌉₊ :=
    pow_pos (by norm_num) _
  constructor
  · apply (div_lt_div_iff₀ (by positivity : 0 < 32768 * R ^ 2) hp).2
    have h := mul_lt_mul_of_pos_right hhi hε
    field_simp [ne_of_gt hε] at h
    nlinarith only [h]
  · apply (div_le_div_iff₀ hp (by positivity : 0 < 16384 * R ^ 2)).2
    have h := mul_le_mul_of_nonneg_right hlo (le_of_lt hε)
    field_simp [ne_of_gt hε] at h
    nlinarith only [h]

lemma ceiling_exponential_decay {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a) :
    Real.exp (-θ * (⌈Real.log a / θ⌉₊ : ℝ)) ≤ 1 / a := by
  have hceil := Nat.le_ceil (Real.log a / θ)
  have hmul := mul_le_mul_of_nonneg_left hceil (le_of_lt hθ)
  have hid : θ * (Real.log a / θ) = Real.log a := by field_simp [ne_of_gt hθ]
  rw [hid] at hmul
  calc
    Real.exp (-θ * (⌈Real.log a / θ⌉₊ : ℝ)) ≤ Real.exp (-Real.log a) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = 1 / a := by rw [Real.exp_neg, Real.exp_log ha]; rfl

lemma batch_ceiling_bound {q : ℝ} (hq : 0 ≤ q) :
    ((max 1 ⌈q⌉₊ : ℕ) : ℝ) ≤ 1 + q := by
  rw [Nat.cast_max]
  norm_num only [Nat.cast_one]
  apply max_le
  · linarith
  · have h := Nat.ceil_lt_add_one hq
    linarith

lemma positive_stage_length_bound {μ γ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hsmall : μ * γ ≤ 1) :
    ((⌈512 * Real.log 16 / (μ * γ)⌉₊ : ℕ) : ℝ) ≤
      (512 * Real.log 16 + 1) / (μ * γ) := by
  have hlog : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 512 * Real.log 16 / (μ * γ) by positivity)
  have hone : 1 ≤ 1 / (μ * γ) := by
    apply (le_div_iff₀ (mul_pos hμ hγ)).2
    simpa using hsmall
  have hid : (512 * Real.log 16 + 1) / (μ * γ) =
      512 * Real.log 16 / (μ * γ) + 1 / (μ * γ) := by ring
  rw [hid]
  linarith

lemma single_stage_sample_bound {μ γ R σ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hR : 0 < R) (hsmall : μ * γ ≤ 1) :
    ((max 1 ⌈γ * σ ^ 2 / (μ * R ^ 2)⌉₊ : ℕ) : ℝ) *
        ((⌈512 * Real.log 16 / (μ * γ)⌉₊ : ℕ) : ℝ) ≤
      (512 * Real.log 16 + 1) * (1 / (γ * μ) + σ ^ 2 / (μ ^ 2 * R ^ 2)) := by
  have hB := batch_ceiling_bound (show 0 ≤ γ * σ ^ 2 / (μ * R ^ 2) by positivity)
  have hK := positive_stage_length_bound hμ hγ hsmall
  have hprod := mul_le_mul hB hK (Nat.cast_nonneg _)
    (show 0 ≤ 1 + γ * σ ^ 2 / (μ * R ^ 2) by positivity)
  have hid :
      (1 + γ * σ ^ 2 / (μ * R ^ 2)) * ((512 * Real.log 16 + 1) / (μ * γ)) =
      (512 * Real.log 16 + 1) * (1 / (γ * μ) + σ ^ 2 / (μ ^ 2 * R ^ 2)) := by
    field_simp [ne_of_gt hμ, ne_of_gt hγ, ne_of_gt hR]
    <;> ring
  simpa only [hid] using hprod

lemma inner_polynomial_bound_to_exponential
    (Λ : ℕ → ℝ) {μ γ σ² bias² B : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hB : 0 < B)
    (hsmall : μ * γ ≤ 512) (hΛ : 0 ≤ Λ 0)
    (hσ : 0 ≤ σ²) (hb : 0 ≤ bias²)
    (hstep : ∀ t, Λ (t + 1) ≤
      (1 - μ * γ / 512) * Λ t + 6 * γ * bias² + 2 * μ * γ ^ 2 * σ² / B) :
    ∀ k, Λ k ≤ Real.exp (-μ * γ * k / 512) * Λ 0 +
      3072 * bias² / μ + 1024 * γ * σ² / B := by
  intro k
  have hg := inner_geometric_bound Λ hμ hγ hB hsmall hstep k
  have hq : 0 ≤ 1 - μ * γ / 512 := by linarith
  have he : 1 - μ * γ / 512 ≤ Real.exp (-μ * γ / 512) := by
    have h := Real.add_one_le_exp (-μ * γ / 512)
    linarith
  have hp : (1 - μ * γ / 512) ^ k ≤ (Real.exp (-μ * γ / 512)) ^ k :=
    pow_le_pow_left₀ hq he k
  have hpowexp : (Real.exp (-μ * γ / 512)) ^ k =
      Real.exp (-μ * γ * k / 512) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpowexp] at hp
  have htransient := mul_le_mul_of_nonneg_right hp hΛ
  have hfloor : 0 ≤ 3072 * bias² / μ + 1024 * γ * σ² / B := by positivity
  have hdiscard := mul_nonneg (pow_nonneg hq k) hfloor
  nlinarith only [hg, htransient, hdiscard]

lemma homotopy_budget_numerical_constants :
    (2 * 32768 * 1572864 * (512 * 15 + 1) : ℝ) ≤ 1125899906842624 ∧
    ((4 / 3) * 32768 ^ 2 * (512 * 15 + 1) : ℝ) ≤ 1125899906842624 ∧
    (512 * 786432 : ℝ) + 1 ≤ 1125899906842624 ∧
    (128 : ℝ) + 1 ≤ 1125899906842624 := by
  norm_num

end LongTails.Proofs.ProximalEf21Schedule
