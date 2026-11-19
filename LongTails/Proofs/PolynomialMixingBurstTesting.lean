import LongTails.Proofs.PolynomialMixingBurstCalibration
import LongTails.Proofs.PolynomialMixingLowerBound

open MeasureTheory

namespace LongTails.Proofs.PolynomialMixingBurst

open LongTails.Setups.PolynomialMixingSubgradient
open LongTails.Proofs.PolynomialMixingLowerBound

lemma burst_prefix_silent (m N : ℕ) (a : unitInterval) :
    (1 - (a : ℝ)) ^ (N + m) ≤
      (burstLaw m a : Measure Path).real (commonPrefix 0 N) := by
  change _ ≤ ((bitsLaw a).map (burst m)).real _
  rw [map_measureReal_apply (measurable_burst m) (measurableSet_commonPrefix _ (measurableSet_singleton _) _),
    ← silent_probability]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  exact fun _ hb => burst_zero_on_silent hb

lemma burst_prefix_active (m N : ℕ) (a : unitInterval) :
    1 - (1 - (a : ℝ)) ^ (m - N) ≤
      (burstLaw m a : Measure Path).real (commonPrefix 1 N) := by
  let shift := fun (b : Bits) (k : ℕ) => b (N + k)
  have hs : Measurable shift := by unfold shift; fun_prop
  have hm : (bitsLaw a).real (shift ⁻¹' (silent (m - N))ᶜ) = 1 - (1 - (a : ℝ)) ^ (m - N) := by
    rw [← map_measureReal_apply hs (measurableSet_silent _).compl, bits_shift a N,
      measureReal_compl (measurableSet_silent _), probReal_univ, silent_probability]
  change _ ≤ ((bitsLaw a).map (burst m)).real _
  rw [← hm, map_measureReal_apply (measurable_burst m) (measurableSet_commonPrefix _ (measurableSet_singleton _) _)]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro b hb k hk
  change ¬ ∀ i < m - N, b (N + i) = false at hb
  push Not at hb
  obtain ⟨i, hi, ha⟩ := hb
  apply ite_eq_left
  refine ⟨⟨N + i - k, by omega⟩, ?_⟩
  have he : k + (N + i - k) = N + i := by omega
  simp only [he]
  exact Bool.eq_true_of_not_eq_false ha

lemma zero_marginal (m : ℕ) (a : unitInterval) :
    ((burstLaw m a : Measure Path).map (fun z => z 0)).real {0} = (1 - (a : ℝ)) ^ m := by
  rw [map_measureReal_apply (measurable_pi_apply 0) (measurableSet_singleton _)]
  change ((bitsLaw a).map (burst m)).real _ = _
  rw [map_measureReal_apply (measurable_burst m)
    ((measurable_pi_apply 0) (measurableSet_singleton (0 : ℝ))), ← silent_probability]
  congr 1
  ext b
  change (if ∃ i : Fin m, b (0 + i.val) = true then (1 : ℝ) else 0) = 0 ↔ ∀ j < m, b j = false
  simp only [zero_add]
  constructor
  · intro h j hj
    cases he : b j
    · rfl
    · have hex : ∃ i : Fin m, b i.val = true := ⟨⟨j, hj⟩, he⟩
      simp [hex] at h
  · intro h
    apply ite_eq_right
    rintro ⟨i, hi⟩
    simp [h _ i.isLt] at hi

lemma common_failure {W X : Type*} [MeasurableSpace W] (P : Measure W)
    [IsProbabilityMeasure P] (H : Set W) (x y : W → X) (B C : Set X)
    (hB : MeasurableSet (x ⁻¹' B)) (hC : MeasurableSet (y ⁻¹' C))
    (hs : Disjoint B C) (he : ∀ w ∈ H, x w = y w) {δ : ℝ}
    (hδ : 2 * δ < P.real H) :
    ¬(1 - δ ≤ P.real (x ⁻¹' B) ∧ 1 - δ ≤ P.real (y ⁻¹' C)) := by
  rintro ⟨hb, hc⟩
  have hsub : H ⊆ (x ⁻¹' B)ᶜ ∪ (y ⁻¹' C)ᶜ := by
    intro w hw
    by_cases hx : x w ∈ B
    · right
      intro hy
      exact Set.disjoint_left.mp hs hx (by rw [he w hw]; exact hy)
    · exact Or.inl hx
  have h := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
  rw [measureReal_compl hB, measureReal_compl hC, probReal_univ] at h
  linarith


lemma stationary_mass_bounds (a β τ : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 4) :
    let m := width a β τ
    let l := arrival a β τ ha.le (show a ≤ 1 by linarith)
    let π := (burstLaw m l : Measure Path).map (fun z => z 0)
    a / 2 ≤ π.real ({0}ᶜ) ∧ π.real ({0}ᶜ) ≤ a ∧ 1 - a ≤ π.real {0} := by
  let m := width a β τ
  let l := arrival a β τ ha.le (show a ≤ 1 by linarith)
  let P := burstLaw m l
  let π := (P : Measure Path).map (fun z => z 0)
  let : IsProbabilityMeasure π := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply 0).aemeasurable).mpr inferInstance
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (width_pos a β τ).ne'
  have hml : (m : ℝ) * (l : ℝ) = a := by change (m : ℝ) * (a / m) = a; field_simp
  have hl := burst_probability_lower l.2.1 l.2.2 m
  rw [hml] at hl
  have hu := one_add_mul_le_pow (a := -(l : ℝ)) (by linarith [l.2.2]) m
  rw [mul_neg, hml] at hu
  change a / 2 ≤ π.real ({0}ᶜ) ∧ π.real ({0}ᶜ) ≤ a ∧ 1 - a ≤ π.real {0}
  rw [measureReal_compl (measurableSet_singleton _), probReal_univ, zero_marginal]
  have hhalf : a / 2 ≤ a / (1 + a) := by
    apply div_le_div_of_nonneg_left ha.le (by positivity)
    linarith
  simpa only [sub_eq_add_neg] using
    And.intro (hhalf.trans hl) (And.intro (by linarith : 1 - (1 + -(l : ℝ)) ^ m ≤ a) hu)

lemma rare_silence (a β τ δ : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 4)
    (hδ : 0 < δ) (N : ℕ)
    (hn : (N : ℝ) ≤ width a β τ * Real.log (1 / (4 * δ)) / (2 * a)) :
    let l := arrival a β τ ha.le (show a ≤ 1 by linarith)
    2 * δ < (burstLaw (width a β τ) l : Measure Path).real (commonPrefix 0 N) := by
  let m := width a β τ
  let l := arrival a β τ ha.le (show a ≤ 1 by linarith)
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast width_pos a β τ
  have hl : (l : ℝ) ≤ a := by
    change a / (m : ℝ) ≤ a
    exact div_le_self ha.le hm
  have h₁ := silence_lower l.2.1 (by linarith : (l : ℝ) ≤ 1 / 2) N
  have h₂ : 4 * δ ≤ Real.exp (-2 * (l : ℝ) * N) := by
    rw [← Real.exp_log (by positivity : 0 < 4 * δ), Real.exp_le_exp]
    have he := (le_div_iff₀ (by positivity : 0 < 2 * a)).mp hn
    rw [one_div, Real.log_inv] at he
    change Real.log (4 * δ) ≤ -2 * (a / m) * N
    apply (mul_le_mul_iff_left₀ (by linarith : 0 < (m : ℝ))).mp
    field_simp
    dsimp [m] at *
    linarith
  have hml : (m : ℝ) * (l : ℝ) = a := by
    change (m : ℝ) * (a / m) = a
    field_simp
  have h₃ := one_add_mul_le_pow (a := -(l : ℝ)) (by linarith [l.2.2]) m
  rw [mul_neg, hml] at h₃
  have he := burst_prefix_silent m N l
  rw [pow_add] at he
  apply lt_of_lt_of_le _ he
  have hb : (1 - (l : ℝ)) ^ N ≥ 4 * δ := h₂.trans h₁
  have hb' : (1 - (l : ℝ)) ^ m ≥ 1 - a := h₃
  have := mul_le_mul hb hb' (by linarith) (pow_nonneg (sub_nonneg.mpr l.2.2) N)
  nlinarith [mul_le_mul_of_nonneg_left ha' hδ.le]

lemma rare_trap (δ β τ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 32) (N : ℕ)
    (hn : 2 * N ≤ width (8 * δ) β τ) :
    let a := 8 * δ
    let l := arrival a β τ (by positivity) (show a ≤ 1 by dsimp [a]; linarith)
    2 * δ < (burstLaw (width a β τ) l : Measure Path).real (commonPrefix 1 N) := by
  let m := width (8 * δ) β τ
  let l := arrival (8 * δ) β τ (by positivity) (by linarith)
  have hm : 0 < (m : ℝ) := by exact_mod_cast width_pos (8 * δ) β τ
  have hml : (m : ℝ) * (l : ℝ) = 8 * δ := by
    change (m : ℝ) * (8 * δ / m) = _
    field_simp
  have hN : N ≤ m := by change 2 * N ≤ m at hn; omega
  have hN' : 2 * (N : ℝ) ≤ m := by exact_mod_cast hn
  have hl := burst_probability_lower l.2.1 l.2.2 (m - N)
  apply lt_of_lt_of_le _ (hl.trans (burst_prefix_active m N l))
  have hnon : 0 ≤ (((m - N : ℕ) : ℝ) * (l : ℝ)) := mul_nonneg (Nat.cast_nonneg _) l.2.1
  apply (lt_div_iff₀ (by linarith)).mpr
  rw [Nat.cast_sub hN] at *
  have hh := mul_le_mul_of_nonneg_right hN' l.2.1
  have hsmall : ((m : ℝ) - N) * (l : ℝ) ≤ 8 * δ := by nlinarith [mul_nonneg (Nat.cast_nonneg N) l.2.1]
  nlinarith [mul_le_mul_of_nonneg_left (hsmall.trans (show 8 * δ ≤ 1 / 4 by linarith)) hδ.le]

end LongTails.Proofs.PolynomialMixingBurst
