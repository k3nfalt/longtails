import LongTails.Proofs.ProximalEf21Schedule

open scoped BigOperators

noncomputable section

namespace LongTails.Proofs.ProximalEf21CountedBudget

open LongTails.Proofs.ProximalEf21Schedule

noncomputable def mu (L : ℝ) (s : ℕ) : ℝ := 2 * L / (2 : ℝ) ^ s
noncomputable def gamma (L δ : ℝ) : ℝ := δ / (1572864 * L)
noncomputable def lastStage (L R ε : ℝ) : ℕ := ⌈Real.log (32768 * L * R ^ 2 / ε) / Real.log 2⌉₊
noncomputable def batches (L R σ δ : ℝ) (s : ℕ) : ℕ := max 1 ⌈gamma L δ * σ ^ 2 / (mu L s * R ^ 2)⌉₊
noncomputable def length (L R δ H : ℝ) (s : ℕ) : ℕ := if s = 0 then ⌈512 / (mu L 0 * gamma L δ) * Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2))⌉₊ else ⌈512 * Real.log 16 / (mu L s * gamma L δ)⌉₊
noncomputable def samples (L R σ δ H ε : ℝ) : ℕ := ∑ s ∈ Finset.range (lastStage L R ε + 1), batches L R σ δ s * length L R δ H s
noncomputable def rounds (L R δ H ε : ℝ) : ℕ := ∑ s ∈ Finset.range (lastStage L R ε + 1), length L R δ H s
noncomputable def sampleBudget (L R σ δ H ε : ℝ) : ℕ := ⌈1152921504606846976 * (L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2 + (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) * Real.log (2 + H / (L * R ^ 2)))⌉₊
noncomputable def roundBudget (L R δ H ε : ℝ) : ℕ := ⌈1152921504606846976 * (L * R ^ 2 / (δ * ε) + Real.log (2 + H / (L * R ^ 2)) / δ)⌉₊

lemma mu_positive {L : ℝ} (hL : 0 < L) (s : ℕ) : 0 < mu L s := by
  unfold mu
  positivity

lemma mu_le_initial {L : ℝ} (hL : 0 < L) (s : ℕ) : mu L s ≤ 2 * L := by
  have hp : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  unfold mu
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) s)).2
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * L by positivity)]

lemma mu_dyadic (L : ℝ) (s : ℕ) : mu L s = 2 * mu L (s + 1) := by
  unfold mu
  rw [pow_succ]
  field_simp
  <;> ring

lemma mu_step_small {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (s : ℕ) : mu L s * gamma L δ ≤ 1 := by
  have hg : 0 < gamma L δ := by unfold gamma; positivity
  have hm := mul_le_mul_of_nonneg_right (mu_le_initial hL s) hg.le
  have hid : 2 * L * gamma L δ = δ / 786432 := by
    unfold gamma
    field_simp [ne_of_gt hL]
    <;> ring
  rw [hid] at hm
  linarith

lemma batches_positive (L R σ δ : ℝ) (s : ℕ) : 0 < batches L R σ δ s := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma batch_floor {L R σ δ : ℝ} (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ)
    (s : ℕ) : gamma L δ * σ ^ 2 / (batches L R σ δ s : ℝ) ≤ mu L s * R ^ 2 := by
  have hμ := mu_positive hL s
  have hB : (0 : ℝ) < batches L R σ δ s := by exact_mod_cast batches_positive L R σ δ s
  have hlo : gamma L δ * σ ^ 2 / (mu L s * R ^ 2) ≤ (batches L R σ δ s : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈gamma L δ * σ ^ 2 / (mu L s * R ^ 2)⌉₊)
  have h := (div_le_iff₀ (show 0 < mu L s * R ^ 2 by positivity)).mp hlo
  apply (div_le_iff₀ hB).2
  nlinarith only [h]

lemma positive_length_decay {L R δ H : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) {s : ℕ} (hs : s ≠ 0) :
    Real.exp (-mu L s * gamma L δ * (length L R δ H s : ℝ) / 512) ≤ 1 / 16 := by
  have hμ := mu_positive hL s
  have hg : 0 < gamma L δ := by unfold gamma; positivity
  have hid : 512 * Real.log 16 / (mu L s * gamma L δ) =
      Real.log 16 / (mu L s * gamma L δ / 512) := by ring
  have h := ceiling_exponential_decay
    (show 0 < mu L s * gamma L δ / 512 by positivity) (by norm_num : (0 : ℝ) < 16)
  unfold length
  rw [if_neg hs, hid]
  convert h using 1 <;> congr 1 <;> ring

lemma initial_length_decay {L R δ H : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hH : 0 ≤ H) :
    Real.exp (-mu L 0 * gamma L δ * (length L R δ H 0 : ℝ) / 512) * H ≤
      8192 * mu L 0 * R ^ 2 / 2 := by
  have hμ := mu_positive hL 0
  have hg : 0 < gamma L δ := by unfold gamma; positivity
  have ha : 0 < 2 + 2 * H / (8192 * mu L 0 * R ^ 2) := by positivity
  have hid : 512 / (mu L 0 * gamma L δ) *
      Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) =
      Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) /
        (mu L 0 * gamma L δ / 512) := by ring
  have he := ceiling_exponential_decay
    (show 0 < mu L 0 * gamma L δ / 512 by positivity) ha
  have he' : Real.exp (-mu L 0 * gamma L δ * (length L R δ H 0 : ℝ) / 512) ≤
      1 / (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) := by
    unfold length
    rw [if_pos rfl, hid]
    convert he using 1 <;> congr 1 <;> ring
  have hb := LongTails.Proofs.ProximalEf21ScalarCore.initialize_stage hH
    (show 0 < 8192 * mu L 0 * R ^ 2 by positivity)
  have hm := mul_le_mul_of_nonneg_right he' hH
  calc
    _ ≤ 1 / (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) * H := hm
    _ = H / (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) := by ring
    _ ≤ _ := hb

lemma initial_round_bound {L R δ H : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H) :
    (length L R δ H 0 : ℝ) ≤
      1073741824 / δ * Real.log (2 + H / (L * R ^ 2)) := by
  have hden : 0 < L * R ^ 2 := by positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have harg : 2 ≤ 2 + H / (L * R ^ 2) := by positivity
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 + H / (L * R ^ 2)) :=
    hlog2.trans (Real.log_le_log (by norm_num) harg)
  have hid : mu L 0 * gamma L δ = δ / 786432 := by
    unfold mu gamma
    norm_num
    field_simp [ne_of_gt hL]
    <;> ring
  have hμ0 : mu L 0 = 2 * L := by simp [mu]
  have ha : 2 + 2 * H / (8192 * mu L 0 * R ^ 2) ≤ 2 + H / (L * R ^ 2) := by
    rw [hμ0]
    have hfrac : 2 * H / (8192 * (2 * L) * R ^ 2) =
        (1 / 8192 : ℝ) * (H / (L * R ^ 2)) := by ring
    rw [hfrac]
    have hz : 0 ≤ H / (L * R ^ 2) := by positivity
    linarith
  have hl := Real.log_le_log (by positivity : 0 < 2 + 2 * H / (8192 * mu L 0 * R ^ 2)) ha
  have hq : 0 ≤ 512 / (mu L 0 * gamma L δ) *
      Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) := by
    have ha1 : 1 ≤ 2 + 2 * H / (8192 * mu L 0 * R ^ 2) := by positivity
    have hlg := Real.log_nonneg ha1
    rw [hid]
    positivity
  have hc := (Nat.ceil_lt_add_one hq).le
  change (length L R δ H 0 : ℝ) ≤
    512 / (mu L 0 * gamma L δ) * Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) + 1 at hc
  have hm := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 512 / (mu L 0 * gamma L δ) by rw [hid]; positivity)
  have hcoef : 512 / (mu L 0 * gamma L δ) = 402653184 / δ := by
    rw [hid]
    field_simp [ne_of_gt hδ]
    <;> ring
  rw [hcoef] at hc hm
  have hlogδ : 1 ≤ 2 / δ * Real.log (2 + H / (L * R ^ 2)) := by
    apply (mul_le_mul_left hδ).mp
    field_simp [ne_of_gt hδ]
    nlinarith only [hδ1, hlog]
  have hlognon : 0 ≤ Real.log (2 + H / (L * R ^ 2)) := by linarith
  have hslack : 0 ≤ (1073741824 - 402653184 - 2 : ℝ) / δ *
      Real.log (2 + H / (L * R ^ 2)) := by positivity
  nlinarith only [hc, hm, hlogδ, hslack]

lemma initial_sample_bound {L R σ δ H : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H) :
    (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) ≤
      1073741824 * (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) *
        Real.log (2 + H / (L * R ^ 2)) := by
  have hγ : 0 < gamma L δ := by unfold gamma; positivity
  have hμ := mu_positive hL 0
  have hB := batch_ceiling_bound (show 0 ≤ gamma L δ * σ ^ 2 / (mu L 0 * R ^ 2) by positivity)
  change (batches L R σ δ 0 : ℝ) ≤ 1 + gamma L δ * σ ^ 2 / (mu L 0 * R ^ 2) at hB
  have hK := initial_round_bound hL hR hδ hδ1 hH
  have hp := mul_le_mul hB hK (Nat.cast_nonneg _)
    (show 0 ≤ 1 + gamma L δ * σ ^ 2 / (mu L 0 * R ^ 2) by positivity)
  have hid : (1 + gamma L δ * σ ^ 2 / (mu L 0 * R ^ 2)) *
      (1073741824 / δ * Real.log (2 + H / (L * R ^ 2))) =
      1073741824 * (1 / δ + σ ^ 2 / (3145728 * L ^ 2 * R ^ 2)) *
        Real.log (2 + H / (L * R ^ 2)) := by
    unfold mu gamma
    norm_num
    field_simp [ne_of_gt hL, ne_of_gt hR, ne_of_gt hδ]
    <;> ring
  rw [hid] at hp
  have hσ : σ ^ 2 / (3145728 * L ^ 2 * R ^ 2) ≤ σ ^ 2 / (L ^ 2 * R ^ 2) := by
    have hq : 0 ≤ σ ^ 2 / (L ^ 2 * R ^ 2) := by positivity
    have heq : σ ^ 2 / (3145728 * L ^ 2 * R ^ 2) =
      (σ ^ 2 / (L ^ 2 * R ^ 2)) / 3145728 := by ring
    rw [heq]
    linarith
  have hlog : 0 ≤ Real.log (2 + H / (L * R ^ 2)) :=
    Real.log_nonneg (by positivity)
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_left hσ (1 / δ)) (by norm_num : (0 : ℝ) ≤ 1073741824)) hlog
  exact hp.trans hs

lemma exact_round_sum_bound {L R δ H ε : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (rounds L R δ H ε : ℝ) ≤ (length L R δ H 0 : ℝ) +
      (512 * Real.log 16 + 1) * (2 / (gamma L δ * mu L (lastStage L R ε))) := by
  have hγ : 0 < gamma L δ := by unfold gamma; positivity
  have hC : 0 ≤ 512 * Real.log 16 + 1 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    linarith
  have hpoint : ∀ s, (length L R δ H s : ℝ) ≤
      (if s = 0 then (length L R δ H 0 : ℝ) else 0) +
      (512 * Real.log 16 + 1) / (mu L s * gamma L δ) := by
    intro s
    by_cases hs : s = 0
    · subst s
      simp only [if_pos rfl]
      have hh : 0 ≤ (512 * Real.log 16 + 1) / (mu L 0 * gamma L δ) := by positivity
      linarith
    · simpa only [length, if_neg hs, zero_add] using
        positive_stage_length_bound (mu_positive hL s) hγ (mu_step_small hL hδ hδ1 s)
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.range (lastStage L R ε + 1)) => hpoint s)
  have hz : (∑ s ∈ Finset.range (lastStage L R ε + 1),
      if s = 0 then (length L R δ H 0 : ℝ) else 0) = length L R δ H 0 := by simp
  have hsum := (dyadic_inverse_sums hL (lastStage L R ε)).1
  have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (512 * Real.log 16 + 1) / gamma L δ by positivity)
  have hid (s : ℕ) : (512 * Real.log 16 + 1) / (mu L s * gamma L δ) =
      ((512 * Real.log 16 + 1) / gamma L δ) * (1 / mu L s) := by ring
  simp_rw [hid] at hs
  rw [Finset.sum_add_distrib, hz, ← Finset.mul_sum] at hs
  have hcount : (rounds L R δ H ε : ℝ) =
      ∑ s ∈ Finset.range (lastStage L R ε + 1), (length L R δ H s : ℝ) := by
    simp [rounds, Nat.cast_sum]
  rw [hcount]
  change _ ≤ (512 * Real.log 16 + 1) / gamma L δ * (2 / mu L (lastStage L R ε)) at hscaled
  nlinarith only [hs, hscaled]

lemma exact_sample_sum_bound {L R σ δ H ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (samples L R σ δ H ε : ℝ) ≤
      (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) +
      (512 * Real.log 16 + 1) *
        (2 / (gamma L δ * mu L (lastStage L R ε)) +
          4 * σ ^ 2 / (3 * (mu L (lastStage L R ε)) ^ 2 * R ^ 2)) := by
  have hγ : 0 < gamma L δ := by unfold gamma; positivity
  have hC : 0 ≤ 512 * Real.log 16 + 1 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    linarith
  have hpoint : ∀ s, (batches L R σ δ s : ℝ) * (length L R δ H s : ℝ) ≤
      (if s = 0 then (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) else 0) +
      (512 * Real.log 16 + 1) *
        (1 / (gamma L δ * mu L s) + σ ^ 2 / ((mu L s) ^ 2 * R ^ 2)) := by
    intro s
    by_cases hs : s = 0
    · subst s
      simp only [if_pos rfl]
      have hh : 0 ≤ (512 * Real.log 16 + 1) *
          (1 / (gamma L δ * mu L 0) + σ ^ 2 / ((mu L 0) ^ 2 * R ^ 2)) := by positivity
      linarith
    · simpa only [batches, length, if_neg hs, zero_add] using
        single_stage_sample_bound (mu_positive hL s) hγ hR (mu_step_small hL hδ hδ1 s)
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.range (lastStage L R ε + 1)) => hpoint s)
  have hz : (∑ s ∈ Finset.range (lastStage L R ε + 1),
      if s = 0 then (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) else 0) =
      (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) := by simp
  obtain ⟨h1, h2⟩ := dyadic_inverse_sums hL (lastStage L R ε)
  have h1s := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / gamma L δ by positivity)
  have h2s := mul_le_mul_of_nonneg_left h2 (show 0 ≤ σ ^ 2 / R ^ 2 by positivity)
  have hid (s : ℕ) : 1 / (gamma L δ * mu L s) + σ ^ 2 / ((mu L s) ^ 2 * R ^ 2) =
      (1 / gamma L δ) * (1 / mu L s) + (σ ^ 2 / R ^ 2) * (1 / (mu L s) ^ 2) := by ring
  simp_rw [hid] at hs
  rw [Finset.sum_add_distrib, hz, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hcombined := mul_le_mul_of_nonneg_left (add_le_add h1s h2s) hC
  have hcount : (samples L R σ δ H ε : ℝ) =
      ∑ s ∈ Finset.range (lastStage L R ε + 1),
        (batches L R σ δ s : ℝ) * (length L R δ H s : ℝ) := by
    simp [samples, Nat.cast_sum, Nat.cast_mul]
  rw [hcount]
  change (512 * Real.log 16 + 1) *
      ((1 / gamma L δ) * (∑ s ∈ Finset.range (lastStage L R ε + 1), 1 / mu L s) +
       (σ ^ 2 / R ^ 2) * (∑ s ∈ Finset.range (lastStage L R ε + 1), 1 / (mu L s) ^ 2)) ≤
    (512 * Real.log 16 + 1) *
      ((1 / gamma L δ) * (2 / mu L (lastStage L R ε)) +
       (σ ^ 2 / R ^ 2) * (4 / (3 * (mu L (lastStage L R ε)) ^ 2))) at hcombined
  nlinarith only [hs, hcombined]

lemma terminal_inverse_bounds {L R ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2) :
    1 / mu L (lastStage L R ε) ≤ 32768 * R ^ 2 / ε ∧
      1 / (mu L (lastStage L R ε)) ^ 2 ≤ (32768 * R ^ 2 / ε) ^ 2 := by
  have hl := (terminal_regularization_bounds hL hR hε hεL).1.le
  change ε / (32768 * R ^ 2) ≤ mu L (lastStage L R ε) at hl
  have hm := mu_positive hL (lastStage L R ε)
  have h1 : 1 / mu L (lastStage L R ε) ≤ 32768 * R ^ 2 / ε := by
    apply (div_le_div_iff₀ hm hε).2
    have h := (div_le_iff₀ (show 0 < 32768 * R ^ 2 by positivity)).mp hl
    simpa [mul_comm] using h
  refine ⟨h1, ?_⟩
  have ha : 0 ≤ 1 / mu L (lastStage L R ε) := by positivity
  have hb : 0 ≤ 32768 * R ^ 2 / ε := by positivity
  have hsq : (1 / mu L (lastStage L R ε)) ^ 2 ≤ (32768 * R ^ 2 / ε) ^ 2 := by
    nlinarith
  simpa only [div_pow, one_pow] using hsq

lemma leading_cost_bound {L R σ δ ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ)
    (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2) :
    (512 * Real.log 16 + 1) *
      (2 / (gamma L δ * mu L (lastStage L R ε)) +
        4 * σ ^ 2 / (3 * (mu L (lastStage L R ε)) ^ 2 * R ^ 2)) ≤
      1125899906842624 * (L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2) := by
  have hγ : 0 < gamma L δ := by unfold gamma; positivity
  obtain ⟨h1, h2⟩ := terminal_inverse_bounds hL hR hε hεL
  have hlog : Real.log 16 ≤ 15 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
    norm_num at h
    exact h
  have hC : 0 ≤ 512 * Real.log 16 + 1 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    linarith
  have ha := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / gamma L δ by positivity)
  have hb := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * σ ^ 2 / (3 * R ^ 2) by positivity)
  have hcoef : 512 * Real.log 16 + 1 ≤ 7681 := by linarith
  have hsum := add_le_add ha hb
  have hright : 0 ≤ (2 / gamma L δ) * (32768 * R ^ 2 / ε) +
      (4 * σ ^ 2 / (3 * R ^ 2)) * (32768 * R ^ 2 / ε) ^ 2 := by positivity
  have hprod := mul_le_mul hcoef hsum (by positivity) (by norm_num : (0 : ℝ) ≤ 7681)
  have haid : (2 / gamma L δ) * (32768 * R ^ 2 / ε) =
      (2 * 32768 * 1572864 : ℝ) * (L * R ^ 2 / (δ * ε)) := by
    unfold gamma
    field_simp [ne_of_gt hL, ne_of_gt hδ, ne_of_gt hε]
    <;> ring
  have hbid : (4 * σ ^ 2 / (3 * R ^ 2)) * (32768 * R ^ 2 / ε) ^ 2 =
      ((4 / 3) * 32768 ^ 2 : ℝ) * (σ ^ 2 * R ^ 2 / ε ^ 2) := by
    field_simp [ne_of_gt hR, ne_of_gt hε]
    <;> ring
  rw [haid, hbid] at hprod
  have ha0 : 0 ≤ L * R ^ 2 / (δ * ε) := by positivity
  have hb0 : 0 ≤ σ ^ 2 * R ^ 2 / ε ^ 2 := by positivity
  have hca : (7681 * (2 * 32768 * 1572864) : ℝ) ≤ 1125899906842624 := by norm_num
  have hcb : (7681 * ((4 / 3) * 32768 ^ 2) : ℝ) ≤ 1125899906842624 := by norm_num
  have hca' := mul_le_mul_of_nonneg_right hca ha0
  have hcb' := mul_le_mul_of_nonneg_right hcb hb0
  have hLid : 2 / (gamma L δ * mu L (lastStage L R ε)) +
      4 * σ ^ 2 / (3 * (mu L (lastStage L R ε)) ^ 2 * R ^ 2) =
      (2 / gamma L δ) * (1 / mu L (lastStage L R ε)) +
      (4 * σ ^ 2 / (3 * R ^ 2)) * (1 / (mu L (lastStage L R ε)) ^ 2) := by ring
  rw [hLid]
  nlinarith only [hprod, hca', hcb']

lemma counted_sample_budget {L R σ δ H ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hH : 0 ≤ H) (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2) :
    samples L R σ δ H ε ≤ sampleBudget L R σ δ H ε := by
  have hs := exact_sample_sum_bound (R := R) (σ := σ) (H := H) (ε := ε) hL hR hδ hδ1
  have hi := initial_sample_bound (σ := σ) hL hR hδ hδ1 hH
  have hl := leading_cost_bound (σ := σ) hL hR hδ hε hεL
  have hlog : 0 ≤ Real.log (2 + H / (L * R ^ 2)) := Real.log_nonneg (by positivity)
  have ha : 0 ≤ L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2 := by positivity
  have hb : 0 ≤ (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) * Real.log (2 + H / (L * R ^ 2)) := by positivity
  have ha' := mul_le_mul_of_nonneg_right
    (by norm_num : (1125899906842624 : ℝ) ≤ 1152921504606846976) ha
  have hb' := mul_le_mul_of_nonneg_right
    (by norm_num : (1073741824 : ℝ) ≤ 1152921504606846976) hb
  have hreal : (samples L R σ δ H ε : ℝ) ≤
      1152921504606846976 * (L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2 +
        (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) * Real.log (2 + H / (L * R ^ 2))) := by
    nlinarith only [hs, hi, hl, ha', hb']
  have hc := hreal.trans (Nat.le_ceil _)
  exact_mod_cast hc

lemma counted_round_budget {L R δ H ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hH : 0 ≤ H) (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2) :
    rounds L R δ H ε ≤ roundBudget L R δ H ε := by
  have hs := exact_round_sum_bound (R := R) (H := H) (ε := ε) hL hδ hδ1
  have hi := initial_round_bound hL hR hδ hδ1 hH
  have hl := leading_cost_bound (σ := 0) hL hR hδ hε hεL
  norm_num only [zero_pow, zero_mul, mul_zero, zero_div, add_zero] at hl
  have hlog : 0 ≤ Real.log (2 + H / (L * R ^ 2)) := Real.log_nonneg (by positivity)
  have ha : 0 ≤ L * R ^ 2 / (δ * ε) := by positivity
  have hb : 0 ≤ Real.log (2 + H / (L * R ^ 2)) / δ := by positivity
  have ha' := mul_le_mul_of_nonneg_right
    (by norm_num : (1125899906842624 : ℝ) ≤ 1152921504606846976) ha
  have hb' := mul_le_mul_of_nonneg_right
    (by norm_num : (1073741824 : ℝ) ≤ 1152921504606846976) hb
  have hreal : (rounds L R δ H ε : ℝ) ≤
      1152921504606846976 * (L * R ^ 2 / (δ * ε) + Real.log (2 + H / (L * R ^ 2)) / δ) := by
    nlinarith only [hs, hi, hl, ha', hb']
  have hc := hreal.trans (Nat.le_ceil _)
  exact_mod_cast hc

end LongTails.Proofs.ProximalEf21CountedBudget
