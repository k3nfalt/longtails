import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.HolderNoisePhase

lemma reciprocal_exponent {ν : ℝ} (hν : 0 < ν) : (2 * ν) * (1 / (2 * ν)) = 1 := by
  field_simp

lemma normalized_high_term {L M ν σ ε : ℝ} (hL : 0 < L) (hM : 0 ≤ M) (hν : 0 < ν)
    (hσ : 0 ≤ σ) (hε : 0 < ε) :
    (M * (ε / L) ^ (2 * ν) / ε ^ 2) ^ (1 / (2 * ν)) *
      (σ ^ 2 / ε ^ 2) ^ (1 - 1 / (2 * ν)) =
      M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / (L * ε) := by
  let α := 1 / (2 * ν)
  have hnum : 0 ≤ M * (ε / L) ^ (2 * ν) := by positivity
  have he : (2 * ν) * α = 1 := reciprocal_exponent hν
  have h1 : ((ε / L) ^ (2 * ν)) ^ α = ε / L := by
    rw [← Real.rpow_mul (div_nonneg hε.le hL.le), he, Real.rpow_one]
  have h2 : (σ ^ 2) ^ (1 - α) = σ ^ (2 - 1 / ν) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hσ]
    congr 1
    dsimp [α]
    field_simp
  have hd : (ε ^ 2) ^ α * (ε ^ 2) ^ (1 - α) = ε ^ 2 := by
    rw [← Real.rpow_add (sq_pos_of_pos hε), show α + (1 - α) = 1 by ring, Real.rpow_one]
  change (M * (ε / L) ^ (2 * ν) / ε ^ 2) ^ α * (σ ^ 2 / ε ^ 2) ^ (1 - α) = _
  rw [Real.div_rpow hnum (sq_nonneg ε), Real.div_rpow (sq_nonneg σ) (sq_nonneg ε),
    Real.mul_rpow hM (Real.rpow_nonneg (div_nonneg hε.le hL.le) _), h1, h2, div_mul_div_comm, hd]
  field_simp
  ring

lemma normalized_low_term {L M ν Δ ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    (L * Δ / ε ^ 2) * (M * (ε / L) ^ (2 * ν) / ε ^ 2) =
      Δ * M * (L / ε) ^ (1 - 2 * ν) / ε ^ 3 := by
  have hr : 0 < L / ε := div_pos hL hε
  have hi : (ε / L) ^ (2 * ν) = (L / ε) ^ (-2 * ν) := by
    rw [show ε / L = (L / ε)⁻¹ by field_simp, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
    congr 1
    ring
  have hp : (L / ε) ^ (1 - 2 * ν) = (L / ε) * (L / ε) ^ (-2 * ν) := by
    rw [show 1 - 2 * ν = 1 + (-2 * ν) by ring, Real.rpow_add hr, Real.rpow_one]
  rw [hi, hp]
  field_simp

lemma normalized_phase {L M ν σ Δ ε : ℝ} (hL : 0 < L) (hM : 0 ≤ M) (hν : 0 < ν)
    (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (L * Δ / ε ^ 2) * min (σ ^ 2 / ε ^ 2)
      (max (M * (ε / L) ^ (2 * ν) / ε ^ 2)
        ((M * (ε / L) ^ (2 * ν) / ε ^ 2) ^ (1 / (2 * ν)) *
          (σ ^ 2 / ε ^ 2) ^ (1 - 1 / (2 * ν)))) =
    min (Δ * L * σ ^ 2 / ε ^ 4)
      (Δ / ε ^ 3 * max (M * (L / ε) ^ (1 - 2 * ν))
        (M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν))) := by
  rw [mul_min_of_nonneg _ _ (show 0 ≤ L * Δ / ε ^ 2 by positivity),
    mul_max_of_nonneg _ _ (show 0 ≤ L * Δ / ε ^ 2 by positivity),
    mul_max_of_nonneg _ _ (show 0 ≤ Δ / ε ^ 3 by positivity),
    normalized_low_term hL hε, normalized_high_term hL hM hν hσ hε]
  congr 1
  · ring
  · congr 1
    · ring
    · field_simp

lemma mixed_power_ratio {A U α : ℝ} (hA : 0 < A) (hU : 0 ≤ U) :
    U ^ α * A ^ (1 - α) = A * (U / A) ^ α := by
  rw [Real.rpow_sub hA, Real.rpow_one, Real.div_rpow hU hA.le]
  ring

lemma low_phase {A U ν : ℝ} (hA : 0 < A) (hU : 0 < U) (hν : 0 < ν) (hνh : ν ≤ 1 / 2) :
    min A (max U (U ^ (1 / (2 * ν)) * A ^ (1 - 1 / (2 * ν)))) = min A U := by
  by_cases hAU : A ≤ U
  · rw [min_eq_left (hAU.trans (le_max_left _ _)), min_eq_left hAU]
  · have hUA : U ≤ A := le_of_not_ge hAU
    have hr : U / A ≤ 1 := (div_le_one hA).mpr hUA
    have hα : 1 ≤ 1 / (2 * ν) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hm := mul_le_mul_of_nonneg_left
      (Real.rpow_le_self_of_le_one (div_nonneg hU.le hA.le) hr hα) hA.le
    have he : A * (U / A) = U := by field_simp
    rw [he, ← mixed_power_ratio hA hU.le] at hm
    rw [max_eq_left hm]

lemma phase_optimizer {A U ν : ℝ} (hA : 0 < A) (hU : 0 < U) (hν : 0 < ν) :
    ∃ τ v : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 0 < v ∧ v ≤ A ∧ v ≤ U * τ ^ (-2 * ν) ∧
      τ * v = min A (max U (U ^ (1 / (2 * ν)) * A ^ (1 - 1 / (2 * ν)))) := by
  by_cases hνh : ν ≤ 1 / 2
  · refine ⟨1, min A U, by norm_num, le_rfl, lt_min hA hU, min_le_left _ _, ?_, ?_⟩
    · simp
    · rw [one_mul, low_phase hA hU hν hνh]
  · let α := 1 / (2 * ν)
    have hα0 : 0 < α := by dsimp [α]; positivity
    have hα1 : α ≤ 1 := by
      dsimp [α]
      rw [div_le_one (by positivity)]
      linarith
    by_cases hAU : A ≤ U
    · refine ⟨1, A, by norm_num, le_rfl, hA, le_rfl, ?_, ?_⟩
      · simpa using hAU
      · rw [one_mul, min_eq_left (hAU.trans (le_max_left _ _))]
    · have hUA : U ≤ A := le_of_not_ge hAU
      have hr0 : 0 < U / A := div_pos hU hA
      have hr1 : U / A ≤ 1 := (div_le_one hA).mpr hUA
      let τ := (U / A) ^ α
      have hτ0 : 0 < τ := Real.rpow_pos_of_pos hr0 _
      have hτ1 : τ ≤ 1 := Real.rpow_le_one hr0.le hr1 hα0.le
      have hs : U * τ ^ (-2 * ν) = A := by
        dsimp [τ]
        rw [← Real.rpow_mul hr0.le]
        have he : α * (-2 * ν) = -1 := by dsimp [α]; field_simp
        rw [he, Real.rpow_neg_one]
        field_simp
      have hmix : U ^ α * A ^ (1 - α) = A * τ := mixed_power_ratio hA hU.le
      have hUτ : U ≤ A * τ := by
        have h := mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hr0.le hr1 hα1) hA.le
        have he : A * (U / A) = U := by field_simp
        simpa only [he] using h
      have hτA : A * τ ≤ A := by nlinarith
      refine ⟨τ, A, hτ0, hτ1, hA, le_rfl, hs.ge, ?_⟩
      change τ * A = min A (max U (U ^ α * A ^ (1 - α)))
      rw [hmix, max_eq_right hUτ, min_eq_right hτA]
      ring

end LongTails.Proofs.HolderNoisePhase

namespace LongTails.Proofs.HolderNoiseLowerReduction

open HolderNoisePhase

lemma select_noise_regime {D A U ν : ℝ} (hD : 0 < D) (hA : 0 ≤ A) (hU : 0 ≤ U) (hν : 0 < ν)
    (N : ℕ)
    (hbudget : (N : ℝ) ≤ (D + A + D * min A (max U (U ^ (1 / (2 * ν)) * A ^ (1 - 1 / (2 * ν))))) / (2 : ℝ) ^ 80)
    (hdet : ¬ (N : ℝ) ≤ D / (2 : ℝ) ^ 40) (hinit : ¬ (N : ℝ) ≤ A / 64) :
    ∃ τ v : ℝ, 0 < τ ∧ τ ≤ 1 ∧ (2 : ℝ) ^ 22 ≤ D * τ ∧ (2 : ℝ) ^ 24 ≤ v ∧
      v ≤ A ∧ v ≤ U * τ ^ (-2 * ν) ∧
      (N : ℝ) ≤ (D * τ) * v / (2 : ℝ) ^ 60 ∧ (N : ℝ) ≤ D * (1 + A) := by
  let R := D * min A (max U (U ^ (1 / (2 * ν)) * A ^ (1 - 1 / (2 * ν))))
  have hRA : R ≤ D * A := mul_le_mul_of_nonneg_left (min_le_left _ _) hD.le
  have hND : D < (2 : ℝ) ^ 40 * N := by
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40)).mp (lt_of_not_ge hdet)
    nlinarith
  have hNA : A < 64 * N := by
    have h := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 64)).mp (lt_of_not_ge hinit)
    linarith
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hNR : (2 : ℝ) ^ 70 * N ≤ R := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 80)).mp hbudget
    change (N : ℝ) * 2 ^ 80 ≤ D + A + R at h
    norm_num at h hND ⊢
    nlinarith
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hNR
  have hApos : 0 < A := by nlinarith
  have hUpos : 0 < U := by
    by_contra hu
    have he : U = 0 := le_antisymm (le_of_not_gt hu) hU
    have hα : (1 / (2 * ν) : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hz : R = 0 := by
      dsimp only [R]
      rw [he, Real.zero_rpow hα, zero_mul, max_self, min_eq_right hA, mul_zero]
    linarith
  obtain ⟨τ, v, hτ0, hτ1, hv0, hvA, hvU, he⟩ := phase_optimizer hApos hUpos hν
  have hR : R = (D * τ) * v := by dsimp [R]; rw [← he]; ring
  have hτD : D * τ ≤ D := by nlinarith
  have hDt : (2 : ℝ) ^ 22 ≤ D * τ := by
    by_contra ht
    have ht' : D * τ ≤ (2 : ℝ) ^ 22 := le_of_not_ge ht
    have hr : R ≤ (2 : ℝ) ^ 22 * A := by
      rw [hR]
      exact mul_le_mul ht' hvA hv0.le (by positivity)
    norm_num at hNR hr
    nlinarith
  have hv : (2 : ℝ) ^ 24 ≤ v := by
    by_contra ht
    have ht' : v ≤ (2 : ℝ) ^ 24 := le_of_not_ge ht
    have hr : R ≤ D * (2 : ℝ) ^ 24 := by
      rw [hR]
      exact mul_le_mul hτD ht' hv0.le hD.le
    norm_num at hNR hr hND
    nlinarith
  have hNrate : (N : ℝ) ≤ (D * τ) * v / (2 : ℝ) ^ 60 := by
    rw [le_div_iff₀ (by positivity)]
    rw [← hR]
    norm_num at hNR ⊢
    nlinarith
  have hNdim : (N : ℝ) ≤ D * (1 + A) := by
    have hNle : (N : ℝ) ≤ R := by norm_num at hNR; nlinarith
    nlinarith
  exact ⟨τ, v, hτ0, hτ1, hDt, hv, hvA, hvU, hNrate, hNdim⟩

end LongTails.Proofs.HolderNoiseLowerReduction
