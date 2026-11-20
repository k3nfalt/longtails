import LongTails.Algorithms.DistributedLocalExtragradientTuning
import LongTails.Proofs.DistributedJacobianStrongGrowthTuning

namespace LongTails.Proofs.DistributedJacobianStrongGrowthParameters

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientTuning

lemma growth_gt_one (p : Params) (hp : valid p) : 1 < growth p := by
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  dsimp [growth]
  nlinarith [sq_nonneg p.ρ]

lemma radius_properties (p : Params) (hp : valid p) (T : ℕ) :
    0 < radius p T ∧ radius p T ≤ p.R ∧
      p.M * radius p T ≤ p.L / (16 * (p.L / p.μ) * p.ρ * growth p ^ T) ∧
        (p.M = 0 → radius p T = p.R) := by
  rcases hp with ⟨_, _, _, _, _, _, hμ, hμL, hρ, hM, hR, _, _⟩
  have hL : 0 < p.L := hμ.trans_le hμL
  have hG : 0 < growth p := by dsimp [growth]; positivity
  exact DistributedJacobianStrongGrowthTuning.localization_radius hL hR
    (div_pos hL hμ) (by linarith) (pow_pos hG T) hM

lemma localDepth_properties (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    1 ≤ localDepth p ∧ (localDepth p : ℝ) ≤ p.L / p.μ ∧
      64 * (p.L / p.μ) * growth p ^ localDepth p ≤ (p.n : ℝ) := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hκ : 1 ≤ p.L / p.μ := (one_le_div hμ).mpr hp.2.2.2.2.2.2.2.1
  exact DistributedJacobianStrongGrowthTuning.worker_local_depth hκ (growth_gt_one p hp) hn

lemma contraction_properties (p : Params) (hp : valid p) (T : ℕ)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ) :
    0 < contraction p T ∧ contraction p T ≤ 1 / 64 := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hL : 0 < p.L := hμ.trans_le hp.2.2.2.2.2.2.2.1
  have ht : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hκ : 0 < p.L / p.μ := div_pos hL hμ
  refine ⟨by dsimp [contraction]; positivity, ?_⟩
  change (T : ℝ) / (64 * (p.L / p.μ)) ≤ 1 / 64
  apply (div_le_iff₀ (by positivity : 0 < 64 * (p.L / p.μ))).mpr
  nlinarith

lemma warm_precision (p : Params) (hp : valid p) (T : ℕ) :
    0 < warmSpacing p T ∧ p.R ≤ warmSpacing p T * ((2 ^ warmWidth p T - 1 : ℕ) : ℝ) / 2 := by
  have hr := (radius_properties p hp T).1
  have hd : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hsqrt : 0 < Real.sqrt (p.d : ℝ) := Real.sqrt_pos.mpr hd
  have hs : 0 < warmSpacing p T := by dsimp [warmSpacing]; positivity
  exact ⟨hs, DistributedJacobianStrongGrowthTuning.quantization_width_range hs⟩

lemma refinement_precision (p : Params) (hp : valid p) (T : ℕ)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ) :
    0 < refinementSpacing p T ∧
      clipRadius p T ≤ refinementSpacing p T * ((2 ^ refinementWidth p T - 1 : ℕ) : ℝ) / 2 := by
  have hc := (contraction_properties p hp T hT hTκ).1
  have hd : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hsqrt : 0 < Real.sqrt (p.d : ℝ) := Real.sqrt_pos.mpr hd
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hs : 0 < refinementSpacing p T := by dsimp [refinementSpacing]; positivity
  exact ⟨hs, DistributedJacobianStrongGrowthTuning.quantization_width_range hs⟩

lemma warmCount_normal_form (p : Params) (hp : valid p) (T : ℕ) :
    warmCount p T =
      ⌈(Real.log (4 * p.R ^ 2 / (radius p T / (4 * Real.sqrt p.d)) ^ 2) +
        (2 / (p.n : ℝ)) * Real.log (1 / (p.ε ^ 2 / (8 * p.R ^ 2)))) /
          (p.μ ^ 2 / (p.ρ * p.L ^ 2))⌉₊ := by
  have hr := (radius_properties p hp T).1
  have hd : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hsqrt : 0 < Real.sqrt (p.d : ℝ) := Real.sqrt_pos.mpr hd
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hL : 0 < p.L := hμ.trans_le hp.2.2.2.2.2.2.2.1
  have hρ : 0 < p.ρ := lt_of_lt_of_le zero_lt_one hp.2.2.2.2.2.2.2.2.1
  have hR : 0 < p.R := hp.2.2.2.2.2.2.2.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have he : 4 * p.R ^ 2 / (radius p T / (4 * Real.sqrt p.d)) ^ 2 =
      64 * p.d * p.R ^ 2 / radius p T ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hd.le]
    field_simp
    ring
  have hδ : 1 / (p.ε ^ 2 / (8 * p.R ^ 2)) = 8 * p.R ^ 2 / p.ε ^ 2 := by field_simp
  rw [he, hδ]
  unfold warmCount
  congr 1
  field_simp

lemma warm_accuracy_radius (p : Params) (hp : valid p) (T : ℕ) :
    Real.sqrt p.d * (radius p T / (4 * Real.sqrt p.d) + warmSpacing p T) = 3 * radius p T / 8 := by
  have hd : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hsqrt : 0 < Real.sqrt (p.d : ℝ) := Real.sqrt_pos.mpr hd
  unfold warmSpacing
  field_simp
  ring

lemma refinement_accuracy_terms (p : Params) (hp : valid p) (T : ℕ)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ) :
    (1 - contraction p T / 2) ^ refinementCount p T * radius p T ^ 2 ≤ p.ε ^ 2 / 4 ∧
      (2 / contraction p T) * (1 + 2 / contraction p T) *
        (Real.sqrt p.d * refinementSpacing p T) ^ 2 ≤ 3 * p.ε ^ 2 / 32 := by
  have hc := contraction_properties p hp T hT hTκ
  have hc1 : contraction p T ≤ 1 := by linarith [hc.2]
  have hr := (radius_properties p hp T).1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨DistributedJacobianStrongGrowthTuning.refinement_count_bound hc.1 hc1 hr hε,
    DistributedJacobianStrongGrowthTuning.refinement_rounding_floor hc.1 hc1 p.d hp.1⟩

lemma warm_confidence (p : Params) (hp : valid p) (T : ℕ) (hεR : p.ε < p.R) :
    let δ := p.ε ^ 2 / (8 * p.R ^ 2)
    let θ := Real.exp (-(2 / (p.n : ℝ)) * Real.log (1 / δ)) / 4
    0 < θ ∧ θ ≤ 1 ∧ (2 * Real.sqrt θ) ^ (p.n : ℕ) = δ ∧
      (1 - p.μ ^ 2 / (p.ρ * p.L ^ 2)) ^ warmCount p T * p.R ^ 2 /
        (radius p T / (4 * Real.sqrt p.d)) ^ 2 ≤ θ := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hμL : p.μ ≤ p.L := hp.2.2.2.2.2.2.2.1
  have hL : 0 < p.L := hμ.trans_le hμL
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  have hR : 0 < p.R := hp.2.2.2.2.2.2.2.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have ht : 0 < p.μ ^ 2 / (p.ρ * p.L ^ 2) := by positivity
  have ht1 : p.μ ^ 2 / (p.ρ * p.L ^ 2) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hρ (sq_nonneg p.L)
    nlinarith
  have hδ : 0 < p.ε ^ 2 / (8 * p.R ^ 2) := by positivity
  have hδ1 : p.ε ^ 2 / (8 * p.R ^ 2) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hconf := DistributedJacobianStrongGrowthTuning.confidence_parameter hδ hδ1
    (p.n : ℕ) p.n.pos
  refine ⟨hconf.1, hconf.2.1, hconf.2.2, ?_⟩
  have hr := (radius_properties p hp T).1
  have hd : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hsqrt : 0 < Real.sqrt (p.d : ℝ) := Real.sqrt_pos.mpr hd
  rw [warmCount_normal_form p hp T]
  exact DistributedJacobianStrongGrowthTuning.warm_count_bound ht ht1 hR
    (by positivity) (p.n : ℕ)

lemma baseline_accuracy_term (p : Params) (hp : valid p) :
    (1 - p.μ ^ 2 / (p.ρ * p.L ^ 2)) ^ baselineCount p * p.R ^ 2 ≤ p.ε ^ 2 := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hμL : p.μ ≤ p.L := hp.2.2.2.2.2.2.2.1
  have hL : 0 < p.L := hμ.trans_le hμL
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  have hR : 0 < p.R := hp.2.2.2.2.2.2.2.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have ht : 0 < p.μ ^ 2 / (p.ρ * p.L ^ 2) := by positivity
  have ht1 : p.μ ^ 2 / (p.ρ * p.L ^ 2) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hρ (sq_nonneg p.L)
    nlinarith
  have hceil := Nat.le_ceil (p.ρ * (p.L / p.μ) ^ 2 * Real.log (p.R ^ 2 / p.ε ^ 2))
  have he : (p.μ ^ 2 / (p.ρ * p.L ^ 2)) *
      (p.ρ * (p.L / p.μ) ^ 2 * Real.log (p.R ^ 2 / p.ε ^ 2)) =
        Real.log (p.R ^ 2 / p.ε ^ 2) := by field_simp
  have htime := mul_le_mul_of_nonneg_left hceil ht.le
  rw [he] at htime
  have hb := SymmetricReverseFisherGeometry.one_sub_pow_le_exp ht.le ht1 (baselineCount p)
  have hexp : Real.exp (-(p.μ ^ 2 / (p.ρ * p.L ^ 2)) * baselineCount p) ≤
      Real.exp (-Real.log (p.R ^ 2 / p.ε ^ 2)) := by
    apply Real.exp_le_exp.mpr
    change Real.log (p.R ^ 2 / p.ε ^ 2) ≤
      (p.μ ^ 2 / (p.ρ * p.L ^ 2)) * (baselineCount p : ℝ) at htime
    linarith
  calc
    _ ≤ Real.exp (-Real.log (p.R ^ 2 / p.ε ^ 2)) * p.R ^ 2 :=
      mul_le_mul_of_nonneg_right (hb.trans hexp) (sq_nonneg p.R)
    _ = p.ε ^ 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp

end LongTails.Proofs.DistributedJacobianStrongGrowthParameters
