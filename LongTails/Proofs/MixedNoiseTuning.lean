import LongTails.Proofs.MixedNoiseEnergy
import LongTails.Proofs.MixedNoiseBudget

namespace OracleTemplate.MixedNoise

lemma allocated_energy_bound {C r M η S V G Z U : ℝ} (m : ℕ)
    (a b : ℕ → ℝ) (a0 b0 : ℝ) (T : ℕ)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hG : 0 ≤ G)
    (hrel : ∑ l ∈ Finset.range m, r * b l ≤ 2 / C)
    (hinit : ∑ l ∈ Finset.range m, r * a l * (4 : ℝ) ^ l ≤ 1 / C)
    (hsp : ∑ l ∈ Finset.range m, M ^ 2 * b l * ((4 : ℝ) ^ l) ^ 2 * η ^ 2 ≤ 1 / C)
    (hroot : r * b0 ≤ 1 / C) (hroot0 : r * a0 * (4 : ℝ) ^ m ≤ 1 / C)
    (hnoise : Z ≤ U / C) :
    (∑ l ∈ Finset.range m, (2 * r * b l * S + 5 * r * a l * (4 : ℝ) ^ l * G +
      81 * M ^ 2 * b l * ((4 : ℝ) ^ l) ^ 2 * (η ^ 2 * V))) +
      (r * b0 * S + r * a0 * (4 : ℝ) ^ m * G + T * Z) ≤
      5 * S / C + 6 * G / C + 81 * V / C + T * U / C := by
  have he : (∑ l ∈ Finset.range m, (2 * r * b l * S + 5 * r * a l * (4 : ℝ) ^ l * G +
      81 * M ^ 2 * b l * ((4 : ℝ) ^ l) ^ 2 * (η ^ 2 * V))) =
      2 * (∑ l ∈ Finset.range m, r * b l) * S +
      5 * (∑ l ∈ Finset.range m, r * a l * (4 : ℝ) ^ l) * G +
      81 * (∑ l ∈ Finset.range m, M ^ 2 * b l * ((4 : ℝ) ^ l) ^ 2 * η ^ 2) * V := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [he]
  have h1 := mul_le_mul_of_nonneg_right hrel hS
  have h2 := mul_le_mul_of_nonneg_right hinit hG
  have h3 := mul_le_mul_of_nonneg_right hsp hV
  have h4 := mul_le_mul_of_nonneg_right hroot hS
  have h5 := mul_le_mul_of_nonneg_right hroot0 hG
  have h6 := mul_le_mul_of_nonneg_left hnoise (Nat.cast_nonneg T)
  simp only [div_eq_mul_inv] at h1 h2 h3 h4 h5 h6 ⊢
  nlinarith only [h1, h2, h3, h4, h5, h6]

lemma inverse_batch_allocations {C r M η : ℝ} (hC : 0 < C)
    (m : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ l < m, 0 < a l) (hb : ∀ l < m, 0 < b l)
    (hrel : ∀ l < m, C * r * 2 ^ l ≤ b l)
    (hinit : ∀ l < m, C * r * 2 ^ m * (2 : ℝ) ^ l ≤ a l)
    (hsp : ∀ l < m, C * (M ^ 2 * η ^ 2) * 2 ^ m * ((2 : ℝ) ^ l) ^ 3 ≤ b l) :
    (∑ l ∈ Finset.range m, r * (b l)⁻¹) ≤ 2 / C ∧
    (∑ l ∈ Finset.range m, r * (a l)⁻¹ * (4 : ℝ) ^ l) ≤ 1 / C ∧
    (∑ l ∈ Finset.range m, M ^ 2 * (b l)⁻¹ * ((4 : ℝ) ^ l) ^ 2 * η ^ 2) ≤ 1 / C := by
  have hpow (l : ℕ) : (4 : ℝ) ^ l = ((2 : ℝ) ^ l) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  refine ⟨by simpa only [div_eq_mul_inv] using relative_allocation hC b m hb hrel, ?_, ?_⟩
  · have h := geometric_weighted_allocation hC a m 1 ha (by simpa using hinit)
    simpa only [hpow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  · have h := geometric_weighted_allocation hC b m 3 hb hsp
    convert h using 1
    congr 1
    funext l
    rw [hpow]
    simp only [div_eq_mul_inv]
    ring

lemma tuned_edge_batch_lower (L r M σ Δ ε : ℝ) (t l : ℕ)
    (hl : l < hierarchyDepth L M σ Δ ε) :
    max 1 ⌈4096 * (r * 2 ^ l + M ^ 2 * (1 / (2 * L)) ^ 2 *
      2 ^ hierarchyDepth L M σ Δ ε * ((2 : ℝ) ^ l) ^ 3)⌉₊ ≤
      (tunedConfig L r M σ Δ ε).batch t l := by
  simp only [tunedConfig, show ¬ l = hierarchyDepth L M σ Δ ε from Nat.ne_of_lt hl,
    ↓reduceIte]
  omega

lemma tuned_startup_batch_lower (L r M σ Δ ε : ℝ) (t l : ℕ)
    (hl : l < hierarchyDepth L M σ Δ ε) (ht : t < 4 ^ (l + 1)) :
    max 1 ⌈4096 * r * 2 ^ hierarchyDepth L M σ Δ ε * (2 : ℝ) ^ l⌉₊ ≤
      (tunedConfig L r M σ Δ ε).batch t l := by
  simp only [tunedConfig, show ¬ l = hierarchyDepth L M σ Δ ε from Nat.ne_of_lt hl,
    ht, ↓reduceIte]
  omega

lemma tuned_root_batch_lower (L r M σ Δ ε : ℝ) (t : ℕ) :
    max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊ ≤
      (tunedConfig L r M σ Δ ε).batch t (hierarchyDepth L M σ Δ ε) := by
  simp only [tunedConfig, ↓reduceIte]
  split_ifs <;> omega

lemma tuned_initial_batch_lower (L r M σ Δ ε : ℝ) :
    max 1 ⌈4096 * (r * (4 : ℕ) ^ hierarchyDepth L M σ Δ ε + σ ^ 2 / ε ^ 2)⌉₊ ≤
      (tunedConfig L r M σ Δ ε).batch 0 (hierarchyDepth L M σ Δ ε) := by
  simp only [tunedConfig, ↓reduceIte, Nat.cast_pow]
  omega

lemma componentWeight_le_of_batch_lower (cfg : Config) {t l B : ℕ}
    (ht : t < cfg.T) (hl : l ≤ cfg.m) (hB : 0 < B)
    (hbatch : B ≤ cfg.batch (t / 4 ^ l * 4 ^ l) l) :
    componentWeight cfg t l ≤ (B : ℝ)⁻¹ := by
  apply (componentWeight_le_inv_batch cfg ht hl).trans
  apply inv_anti₀ (by exact_mod_cast hB)
  exact_mod_cast hbatch.trans (Nat.le_max_right _ _)

lemma tuned_component_weights (L r M σ Δ ε : ℝ) {t l : ℕ}
    (ht : t < (tunedConfig L r M σ Δ ε).T)
    (hl : l < hierarchyDepth L M σ Δ ε) :
    componentWeight (tunedConfig L r M σ Δ ε) t l ≤
      ((max 1 ⌈4096 * (r * 2 ^ l + M ^ 2 * (1 / (2 * L)) ^ 2 *
        2 ^ hierarchyDepth L M σ Δ ε * ((2 : ℝ) ^ l) ^ 3)⌉₊ : ℕ) : ℝ)⁻¹ ∧
    (t < 4 ^ (l + 1) → componentWeight (tunedConfig L r M σ Δ ε) t l ≤
      ((max 1 ⌈4096 * r * 2 ^ hierarchyDepth L M σ Δ ε * (2 : ℝ) ^ l⌉₊ : ℕ) : ℝ)⁻¹) := by
  constructor
  · exact componentWeight_le_of_batch_lower _ ht hl.le (by omega)
      (tuned_edge_batch_lower L r M σ Δ ε _ l hl)
  · intro hsmall
    exact componentWeight_le_of_batch_lower _ ht hl.le (by omega)
      (tuned_startup_batch_lower L r M σ Δ ε _ l hl
        ((Nat.div_mul_le_self t (4 ^ l)).trans_lt hsmall))

lemma tuned_root_weights (L r M σ Δ ε : ℝ) {t : ℕ}
    (ht : t < (tunedConfig L r M σ Δ ε).T) :
    componentWeight (tunedConfig L r M σ Δ ε) t (hierarchyDepth L M σ Δ ε) ≤
      ((max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ)⁻¹ ∧
    (t < 4 ^ hierarchyDepth L M σ Δ ε →
      componentWeight (tunedConfig L r M σ Δ ε) t (hierarchyDepth L M σ Δ ε) ≤
        ((max 1 ⌈4096 * (r * (4 : ℝ) ^ hierarchyDepth L M σ Δ ε + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ)⁻¹) := by
  constructor
  · exact componentWeight_le_of_batch_lower _ ht le_rfl (by omega)
      (tuned_root_batch_lower L r M σ Δ ε _)
  · intro hsmall
    apply componentWeight_le_of_batch_lower _ ht le_rfl (by omega)
    change t < 4 ^ (tunedConfig L r M σ Δ ε).m at hsmall
    rw [Nat.div_eq_of_lt hsmall, Nat.zero_mul]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, tunedConfig] using tuned_initial_batch_lower L r M σ Δ ε

lemma inverse_scaled_bound {C v b : ℝ} (hC : 0 < C) (hb : 0 < b) (halloc : C * v ≤ b) :
    v * b⁻¹ ≤ 1 / C := by
  rw [← div_eq_mul_inv, div_le_div_iff₀ hb hC]
  nlinarith only [halloc]

lemma tuned_inverse_allocations (L r M σ Δ ε : ℝ) (hr : 0 ≤ r) :
    let m := hierarchyDepth L M σ Δ ε
    let a := fun l => ((max 1 ⌈4096 * r * 2 ^ m * (2 : ℝ) ^ l⌉₊ : ℕ) : ℝ)
    let b := fun l => ((max 1 ⌈4096 * (r * 2 ^ l + M ^ 2 * (1 / (2 * L)) ^ 2 *
      2 ^ m * ((2 : ℝ) ^ l) ^ 3)⌉₊ : ℕ) : ℝ)
    (∑ l ∈ Finset.range m, r * (b l)⁻¹) ≤ 2 / 4096 ∧
    (∑ l ∈ Finset.range m, r * (a l)⁻¹ * (4 : ℝ) ^ l) ≤ 1 / 4096 ∧
    (∑ l ∈ Finset.range m, M ^ 2 * (b l)⁻¹ * ((4 : ℝ) ^ l) ^ 2 *
      (1 / (2 * L)) ^ 2) ≤ 1 / 4096 := by
  dsimp only
  apply inverse_batch_allocations (by norm_num : (0 : ℝ) < 4096)
  · intro l hl
    exact_mod_cast (show 0 < max 1 ⌈4096 * r * 2 ^ hierarchyDepth L M σ Δ ε * (2 : ℝ) ^ l⌉₊ by omega)
  · intro l hl
    positivity
  · intro l hl
    apply le_trans _ (rounded_batch_lower _)
    have h : 0 ≤ M ^ 2 * (1 / (2 * L)) ^ 2 * 2 ^ hierarchyDepth L M σ Δ ε * ((2 : ℝ) ^ l) ^ 3 := by positivity
    nlinarith only [h]
  · intro l hl
    simpa only [pow_one] using rounded_batch_lower (4096 * r * 2 ^ hierarchyDepth L M σ Δ ε * (2 : ℝ) ^ l)
  · intro l hl
    apply le_trans _ (rounded_batch_lower _)
    have h : 0 ≤ r * (2 : ℝ) ^ l := mul_nonneg hr (by positivity)
    nlinarith only [h]

lemma tuned_root_allocations (r σ ε : ℝ) (m : ℕ) (hr : 0 ≤ r) (hε : 0 < ε) :
    let B := ((max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ)
    let B0 := ((max 1 ⌈4096 * (r * (4 : ℝ) ^ m + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ)
    r * B⁻¹ ≤ 1 / 4096 ∧ r * B0⁻¹ * (4 : ℝ) ^ m ≤ 1 / 4096 ∧
      σ ^ 2 * B⁻¹ ≤ ε ^ 2 / 4096 := by
  dsimp only
  have hn : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
  have hB := rounded_batch_lower (4096 * (r + σ ^ 2 / ε ^ 2))
  have hB0 := rounded_batch_lower (4096 * (r * (4 : ℝ) ^ m + σ ^ 2 / ε ^ 2))
  have hbp : (0 : ℝ) < ((max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ) := by positivity
  have hb0p : (0 : ℝ) < ((max 1 ⌈4096 * (r * (4 : ℝ) ^ m + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ) := by positivity
  refine ⟨inverse_scaled_bound (by norm_num) hbp (by linarith), ?_, ?_⟩
  · have h := inverse_scaled_bound (v := r * (4 : ℝ) ^ m) (by norm_num : (0 : ℝ) < 4096) hb0p (by linarith)
    nlinarith only [h]
  · have h := inverse_scaled_bound (v := σ ^ 2 / ε ^ 2) (by norm_num : (0 : ℝ) < 4096) hbp (by linarith)
    have hh := mul_le_mul_of_nonneg_right h (sq_nonneg ε)
    have he : σ ^ 2 / ε ^ 2 * ((max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ)⁻¹ * ε ^ 2 =
        σ ^ 2 * ((max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ)⁻¹ := by field_simp
    rw [he] at hh
    nlinarith only [hh]

lemma tuned_iterations_divisible (L r M σ Δ ε : ℝ) (l : ℕ)
    (hl : l ≤ (tunedConfig L r M σ Δ ε).m) :
    ∃ n, (tunedConfig L r M σ Δ ε).T = n * 4 ^ l := by
  have hq : 4 ^ (tunedConfig L r M σ Δ ε).m ∣ (tunedConfig L r M σ Δ ε).T := by
    dsimp only [tunedConfig]
    split_ifs
    · exact dvd_zero _
    · exact dvd_mul_right _ _
  obtain ⟨n, hn⟩ := (pow_dvd_pow 4 hl).trans hq
  exact ⟨n, by simpa only [Nat.mul_comm] using hn⟩

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type} [MeasurableSpace Ω]

lemma tuned_error_energy (p : Measure Ω) [IsProbabilityMeasure p]
    (L r M σ Δ ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {K : NNReal} (hG : LipschitzWith K G)
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2 ∂p ≤
      r * (‖G x‖ ^ 2 + ‖G y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2)
    (x0 : E) :
    let cfg := tunedConfig L r M σ Δ ε
    let P := Measure.infinitePi fun _ : ℕ => p
    let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
    let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
    let U := fun seed ξ t => ∑ l ∈ Finset.range (cfg.m + 1),
      (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l
    let S := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖G (X seed ξ t)‖ ^ 2 ∂P) ∂Q
    let V := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖U seed ξ t‖ ^ 2 ∂P) ∂Q
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖U seed ξ t - G (X seed ξ t)‖ ^ 2 ∂P) ∂Q) ≤
      5 * S / 4096 + 6 * ‖G x0‖ ^ 2 / 4096 + 81 * V / 4096 + cfg.T * ε ^ 2 / 4096 := by
  dsimp only
  let cfg := tunedConfig L r M σ Δ ε
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
  let U := fun seed ξ t => ∑ l ∈ Finset.range (cfg.m + 1),
    (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l
  let S := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖G (X seed ξ t)‖ ^ 2 ∂P) ∂Q
  let V := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖U seed ξ t‖ ^ 2 ∂P) ∂Q
  let a := fun l => ((max 1 ⌈4096 * r * 2 ^ cfg.m * (2 : ℝ) ^ l⌉₊ : ℕ) : ℝ)
  let b := fun l => ((max 1 ⌈4096 * (r * 2 ^ l + M ^ 2 * cfg.η ^ 2 *
    2 ^ cfg.m * ((2 : ℝ) ^ l) ^ 3)⌉₊ : ℕ) : ℝ)
  let B := ((max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ)
  let B0 := ((max 1 ⌈4096 * (r * (4 : ℝ) ^ cfg.m + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ)
  have ha (l : ℕ) : 0 < a l := by dsimp [a]; positivity
  have hb (l : ℕ) : 0 < b l := by dsimp [b]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have H := aggregate_error_energy p cfg g hg G hG r M σ hgi hmean hnoise hbound hdiff hmixed x0 hr
    (tuned_iterations_divisible L r M σ Δ ε)
    (fun l => (a l)⁻¹) (fun l => (b l)⁻¹) B0⁻¹ B⁻¹
    (fun l _ => inv_nonneg.mpr (ha l).le) (fun l _ => inv_nonneg.mpr (hb l).le)
    (inv_nonneg.mpr hB0.le) (inv_nonneg.mpr hB.le)
    (fun l hl t ht => (tuned_component_weights L r M σ Δ ε ht hl).1)
    (fun l hl t ht hsmall => (tuned_component_weights L r M σ Δ ε ht hl).2 hsmall)
    (fun t ht => (tuned_root_weights L r M σ Δ ε ht).1)
    (fun t ht hsmall => (tuned_root_weights L r M σ Δ ε ht).2 hsmall)
  have hD := integrated_displacement_energy P Q X U cfg.η cfg.T
    (fun seed ξ _ ht => iteration_path_step cfg g x0 seed ξ ht)
  dsimp only at H
  rw [hD] at H
  have hc := tuned_inverse_allocations L r M σ Δ ε hr
  have hc0 := tuned_root_allocations r σ ε cfg.m hr hε
  have hS : 0 ≤ S := integral_nonneg (fun _ => integral_nonneg (fun _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hV : 0 ≤ V := integral_nonneg (fun _ => integral_nonneg (fun _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply H.trans
  simpa only [S, V, X, U, P, Q, B, cfg, tunedConfig, mul_assoc] using (allocated_energy_bound cfg.m (fun l => (a l)⁻¹) (fun l => (b l)⁻¹)
    B0⁻¹ B⁻¹ cfg.T hS hV (sq_nonneg ‖G x0‖) hc.1 hc.2.1 hc.2.2 hc0.1 hc0.2.1 hc0.2.2)

end OracleTemplate.MixedNoise
