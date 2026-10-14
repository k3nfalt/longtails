import LongTails.Proofs.FixedBatchConfidenceNormalized
import LongTails.Proofs.FixedBatchConfidenceDeterministic
import LongTails.Proofs.FixedBatchConfidenceCrossover
import LongTails.Proofs.FixedBatchConfidenceInstance

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.FixedBatchConfidence

open LongTails.Setups.FixedBatchConfidence

lemma deterministic_hard_instance {e δ η ell : ℝ} {b K : ℕ}
    (hb : 0 < b) (hδ : δ < 1) (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1)
    (herror : e < ell * (1 - η * ell) ^ (2 * K) / 2) :
    ∃ (p : unitInterval) (a v : Space), ‖a‖ ^ 2 ≤ 1 ∧ ‖v‖ ^ 2 ≤ 1 ∧
      let P := Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p
      let G := fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ •
        ∑ i, ⟪(if z i then a else v), x⟫ • (if z i then a else v)
      let X := fun ξ : ℕ → Bool => MarkovQuadratic.iterate G η (pair 1 0)
        (fun k i => ξ (k * b + i.val)) K
      δ < P.real {ξ | e < (p : ℝ) * (⟪a, X ξ⟫ ^ 2 / 2) +
        (1 - p) * (⟪v, X ξ⟫ ^ 2 / 2)} := by
  have ha : ‖pair (Real.sqrt ell) 0‖ ^ 2 ≤ 1 := by
    simpa only [pair_norm_sq, Real.sq_sqrt hell0, zero_pow (by omega : 2 ≠ 0), add_zero] using hell1
  refine ⟨0, pair (Real.sqrt ell) 0, pair (Real.sqrt ell) 0, ha, ha, ?_⟩
  apply deterministic_failure_probability _ hb _ _ _ _ _ _ hδ
  simpa only [Real.sq_sqrt hell0] using herror

lemma stable_hard_instance {e δ η : ℝ} {b K N : ℕ}
    (he : 0 < e) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hb : 0 < b) (hKN : K * b ≤ N)
    (hN : N < ⌊min (Real.sqrt (1 / e)) (1 / δ) / (65536 * e)⌋₊) :
    ∃ (p : unitInterval) (a v : Space), ‖a‖ ^ 2 ≤ 1 ∧ ‖v‖ ^ 2 ≤ 1 ∧
      let P := Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p
      let G := fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ •
        ∑ i, ⟪(if z i then a else v), x⟫ • (if z i then a else v)
      let X := fun ξ : ℕ → Bool => MarkovQuadratic.iterate G η (pair 1 0)
        (fun k i => ξ (k * b + i.val)) K
      δ < P.real {ξ | 2 * e < (p : ℝ) * (⟪a, X ξ⟫ ^ 2 / 2) +
        (1 - p) * (⟪v, X ξ⟫ ^ 2 / 2)} := by
  have he' := nonvacuous_small he N hN
  have hδ : δ < 1 := by linarith
  by_cases hK : K = 0
  · apply deterministic_hard_instance (ell := 1) hb hδ (by norm_num) le_rfl
    simp only [hK, mul_zero, pow_zero, mul_one]
    linarith
  have hK0 : 0 < K := Nat.pos_of_ne_zero hK
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK0
  have ht : 0 < η * (K : ℝ) := mul_pos hη0 hKreal
  have hbds := crossover_budget_bounds he hN
  obtain ⟨hell0, hell1, hbias⟩ := scalar_tuning hη0 hK0
  by_cases hstep : η / b ≤ 32 * Real.sqrt e
  · have htime := small_step_time he hη0 hb hKN hstep hbds.1
    have hmargin := bias_margin_small he he' ht htime
    apply deterministic_hard_instance hb hδ hell0.le hell1
    have heq : 2 * η * (K : ℝ) = 2 * (η * (K : ℝ)) := by ring
    rw [← heq] at hmargin
    exact hmargin.trans_le hbias
  by_cases htime : η * (K : ℝ) < 2
  · have hmargin := bias_margin_short he' ht htime
    apply deterministic_hard_instance hb hδ hell0.le hell1
    have heq : 2 * η * (K : ℝ) = 2 * (η * (K : ℝ)) := by ring
    rw [← heq] at hmargin
    exact hmargin.trans_le hbias
  obtain ⟨p, a, c, ha, hc, hac, hprob⟩ := calibrated_rare_probability hη0 hη1 hδ0 hδ1 hb
    (le_of_not_gt htime)
  refine ⟨p, pair a c, pair 0 1, ?_, ?_, ?_⟩
  · rw [pair_norm_sq, hac]
  · norm_num [pair_norm_sq]
  · dsimp only at hprob ⊢
    apply hprob.trans_le
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ξ hξ
    have hmargin := rare_threshold_margin he hδ0 hb hK0 hKN (lt_of_not_ge hstep) hbds.2
    have hh := hmargin.trans_le hξ
    simp only [Set.mem_ofPred_eq, pair_inner_vector, zero_mul, one_mul, zero_add]
    nlinarith [hh]

lemma boolean_feature_scale {b : ℕ} (a v : Space) (η s : ℝ) (ξ : ℕ → Bool) (K : ℕ) :
    MarkovQuadratic.iterate
      (fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ •
        ∑ i, ⟪(if z i then s • a else s • v), x⟫ • (if z i then s • a else s • v))
      η (pair 1 0) (fun k i => ξ (k * b + i.val)) K =
    MarkovQuadratic.iterate
      (fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ •
        ∑ i, ⟪(if z i then a else v), x⟫ • (if z i then a else v))
      (η * s ^ 2) (pair 1 0) (fun k i => ξ (k * b + i.val)) K := by
  have h := boolean_batch_affine_iterate (b := b) 0 a v η 1 s ξ K
  simp only [zero_add, one_smul, sub_zero] at h
  rw [iterate_oracle_map
    (fun (x : Space) (z : Fin b → Space) => (b : ℝ)⁻¹ • ∑ i, ⟪z i, x⟫ • z i)
    (fun (z : Fin b → Bool) i => if z i then s • a else s • v)]
  exact h

lemma normalized_hard_instance {e δ η : ℝ} {b K N : ℕ}
    (he : 0 < e) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη0 : 0 < η)
    (hb : 0 < b) (hKN : K * b ≤ N)
    (hN : N < ⌊min (Real.sqrt (1 / e)) (1 / δ) / (65536 * e)⌋₊) :
    ∃ (p : unitInterval) (a v : Space), ‖a‖ ^ 2 ≤ 1 ∧ ‖v‖ ^ 2 ≤ 1 ∧
      let P := Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p
      let G := fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ •
        ∑ i, ⟪(if z i then a else v), x⟫ • (if z i then a else v)
      let X := fun ξ : ℕ → Bool => MarkovQuadratic.iterate G η (pair 1 0)
        (fun k i => ξ (k * b + i.val)) K
      δ < P.real {ξ | e < (p : ℝ) * (⟪a, X ξ⟫ ^ 2 / 2) +
        (1 - p) * (⟪v, X ξ⟫ ^ 2 / 2)} := by
  have he' := nonvacuous_small he N hN
  by_cases hK : K = 0
  · apply deterministic_hard_instance (ell := 1) hb hδ1 (by norm_num) le_rfl
    simp only [hK, mul_zero, pow_zero, mul_one]
    linarith
  have hK0 : 0 < K := Nat.pos_of_ne_zero hK
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK0
  by_cases hη2 : 2 ≤ η
  · apply deterministic_hard_instance (ell := 1) hb hδ1 (by norm_num) le_rfl
    have hs : 1 ≤ (1 - η) ^ 2 := by nlinarith
    have hp : 1 ≤ ((1 - η) ^ 2) ^ K := one_le_pow₀ hs
    rw [mul_one, one_mul, pow_mul]
    linarith
  have hη2' : η < 2 := lt_of_not_ge hη2
  by_cases hδsmall : δ ≤ 1 / 64
  · by_cases hη1 : η ≤ 1
    · obtain ⟨p, a, v, ha, hv, hp⟩ := stable_hard_instance he hδ0 hδsmall hη0 hη1 hb hKN hN
      refine ⟨p, a, v, ha, hv, ?_⟩
      dsimp only at hp ⊢
      apply hp.trans_le
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro ξ hξ
      change e < _
      change 2 * e < _ at hξ
      linarith
    · obtain ⟨p, a, v, ha, hv, hp⟩ := stable_hard_instance he hδ0 hδsmall
        (by norm_num : (0 : ℝ) < 1) le_rfl hb hKN hN
      let s := Real.sqrt (1 / η)
      have hs : s ^ 2 = 1 / η := Real.sq_sqrt (by positivity)
      have hs0 : 0 ≤ s ^ 2 := sq_nonneg _
      have hs1 : s ^ 2 ≤ 1 := by rw [hs]; exact (div_le_one hη0).mpr (by linarith)
      have hnorm (w : Space) (hw : ‖w‖ ^ 2 ≤ 1) : ‖s • w‖ ^ 2 ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        exact (mul_le_mul_of_nonneg_left hw hs0).trans (by simpa using hs1)
      refine ⟨p, s • a, s • v, hnorm a ha, hnorm v hv, ?_⟩
      dsimp only at hp ⊢
      apply hp.trans_le
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro ξ hξ
      change e < _
      rw [boolean_feature_scale, hs, mul_one_div_cancel (ne_of_gt hη0)]
      simp only [inner_smul_left, conj_trivial, mul_pow]
      have hh := scale_margin he hξ hη0 hη2'
      rw [hs]
      convert hh using 1; ring
  · have hδlarge : 1 / 64 ≤ δ := (lt_of_not_ge hδsmall).le
    have hKle : K ≤ N := (Nat.le_mul_of_pos_right K hb).trans hKN
    have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le hKreal (by exact_mod_cast hKle)
    have htime : η * (K : ℝ) ≤ 2 * (N : ℝ) := by
      have hKNreal : (K : ℝ) ≤ N := by exact_mod_cast hKle
      nlinarith
    have hbds := crossover_budget_bounds he hN
    obtain ⟨hell0, hell1, hbias⟩ := scalar_tuning hη0 hK0
    have hmargin := large_confidence_bias he he' hδlarge hN0
      (mul_pos hη0 hKreal) htime hbds.2
    apply deterministic_hard_instance hb hδ1 hell0.le hell1
    have heq : 2 * η * (K : ℝ) = 2 * (η * (K : ℝ)) := by ring
    rw [← heq] at hmargin
    exact hmargin.trans_le hbias

end OracleTemplate.FixedBatchConfidence
