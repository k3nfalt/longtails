import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.FixedBatchConfidenceDynamics
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Function
open scoped BigOperators

namespace OracleTemplate.FixedBatchConfidence

lemma bernoulli_pattern_probability (p : unitInterval) {n : ℕ} (v : Fin n → Bool) :
    (Measure.pi (fun _ : Fin n => bernoulliMeasure true false p)).real {v} =
      ∏ i, if v i then (p : ℝ) else 1 - p := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  change (bernoulliMeasure true false p).real {v i} = _
  cases v i <;> simp

lemma bernoulli_one_hot_probability (p : unitInterval) {n : ℕ} (i : Fin n) :
    (Measure.pi (fun _ : Fin n => bernoulliMeasure true false p)).real
      {Function.update (fun _ => false) i true} =
      (p : ℝ) * (1 - p) ^ (n - 1) := by
  rw [bernoulli_pattern_probability]
  have hf : (fun j : Fin n => if Function.update (fun _ => false) i true j then
      (p : ℝ) else 1 - p) = Function.update (fun _ => 1 - (p : ℝ)) i p := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.card_sdiff_of_subset (show {i} ⊆ (Finset.univ : Finset (Fin n)) by simp)]

lemma bernoulli_exactly_one_probability (p : unitInterval) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => bernoulliMeasure true false p)).real
      (⋃ i : Fin n, {Function.update (fun _ => false) i true}) =
      (n : ℝ) * p * (1 - p) ^ (n - 1) := by
  have hd : Pairwise (Disjoint on
      (fun i : Fin n => ({Function.update (fun _ => false) i true} : Set (Fin n → Bool)))) := by
    intro i j hij
    apply Set.disjoint_singleton.mpr
    intro h
    have hh := congrFun h i
    simp [Function.update_of_ne hij] at hh
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_singleton _)]
  simp only [bernoulli_one_hot_probability, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

lemma bernoulli_count_integrable (p : unitInterval) (n : ℕ) :
    Integrable (fun v : Fin n → Bool => ∑ i, if v i then (1 : ℝ) else 0)
      (Measure.pi (fun _ : Fin n => bernoulliMeasure true false p)) := by
  apply integrable_finsetSum
  intro i _
  exact integrable_comp_eval (μ := fun _ : Fin n => bernoulliMeasure true false p) (i := i) (integrable_bernoulliMeasure true false p
    (fun v : Bool => if v then (1 : ℝ) else 0))

lemma bernoulli_count_integral (p : unitInterval) (n : ℕ) :
    (∫ v : Fin n → Bool, ∑ i, if v i then (1 : ℝ) else 0
      ∂Measure.pi (fun _ : Fin n => bernoulliMeasure true false p)) = (n : ℝ) * p := by
  rw [integral_finsetSum]
  · have hi (i : Fin n) :
        (∫ v : Fin n → Bool, (if v i then (1 : ℝ) else 0)
          ∂Measure.pi (fun _ : Fin n => bernoulliMeasure true false p)) = p := by
      rw [integral_comp_eval (μ := fun _ : Fin n => bernoulliMeasure true false p) (i := i)
        (integrable_bernoulliMeasure true false p
          (fun v : Bool => if v then (1 : ℝ) else 0)).aestronglyMeasurable,
        integral_bernoulliMeasure]
      simp
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro i _
    exact integrable_comp_eval (μ := fun _ : Fin n => bernoulliMeasure true false p) (i := i) (integrable_bernoulliMeasure true false p
      (fun v : Bool => if v then (1 : ℝ) else 0))

lemma probability_small_of_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ} {c : ℝ}
    (hf : Measurable f) (hi : Integrable f P) (hn : ∀ ω, 0 ≤ f ω)
    (hc : 0 < c) (he : (∫ ω, f ω ∂P) ≤ c / 2) :
    1 / 2 ≤ P.real {ω | f ω < c} := by
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hi c
  have hb : P.real {ω | c ≤ f ω} ≤ 1 / 2 := by nlinarith
  have hs : {ω | f ω < c} = {ω | c ≤ f ω}ᶜ := by ext ω; simp
  rw [hs, measureReal_compl (measurableSet_le measurable_const hf), probReal_univ]
  linarith

lemma iid_finite_block_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (k n : ℕ) :
    MeasurePreserving (fun ω (i : Fin n) => ξ (k + i.val) ω) P
      (Measure.pi fun _ : Fin n => p) := by
  refine ⟨Measurable.of_eval (fun i => h.measurable (k + i.val)), ?_⟩
  have hinj : Function.Injective (fun i : Fin n => k + i.val) := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel hij)
  have hi := h.independent.precomp hinj
  simpa only [h.marginal] using hi.map_fun_eq_pi_map
    (fun i : Fin n => (h.measurable (k + i.val)).aemeasurable)

lemma iid_prefix_window_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure P] (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n m : ℕ) :
    MeasurePreserving
      (fun ω => ((fun i : Fin n => ξ i ω), (fun i : Fin m => ξ (n + i.val) ω))) P
      ((Measure.pi fun _ : Fin n => p).prod (Measure.pi fun _ : Fin m => p)) := by
  have hm := h.measurable
  have hpref : P.map (fun ω (i : Fin n) => ξ i ω) = Measure.pi (fun _ : Fin n => p) := by
    simpa only [Nat.zero_add] using (iid_finite_block_law h 0 n).map_eq
  have hind := (h.prefix_tail_independent n).comp measurable_id
    (Measurable.of_eval (fun i : Fin m => measurable_pi_apply i.val))
  refine ⟨by fun_prop, ?_⟩
  have hh := hind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  simpa only [Function.comp_def, id_eq, hpref,
    (iid_finite_block_law h n m).map_eq, Nat.zero_add] using hh

lemma independent_window_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {A B : Set Ω} {δ : ℝ}
    (hind : IndepSet A B P) (hδ : 0 < δ)
    (hA : 1 / 2 ≤ P.real A) (hB : 7 / 2 * δ ≤ P.real B) :
    δ < P.real (A ∩ B) := by
  have he : P.real (A ∩ B) = P.real A * P.real B := by
    simp only [measureReal_def, hind.measure_inter_eq_mul, ENNReal.toReal_mul]
  have hh := mul_le_mul hA hB (by linarith : 0 ≤ 7 / 2 * δ) (by positivity : 0 ≤ P.real A)
  rw [he]
  nlinarith

lemma iid_good_window_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (p : unitInterval)
    {ξ : ℕ → Ω → Bool}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (bernoulliMeasure true false p) P)
    (n m : ℕ) {c δ : ℝ} (hc : 0 < c) (hmean : (n : ℝ) * p ≤ c / 2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hlo : 4 * δ ≤ (m : ℝ) * p) (hhi : (m : ℝ) * p ≤ 8 * δ) :
    δ < P.real {ω | (∑ i : Fin n, if ξ i ω then (1 : ℝ) else 0) < c ∧
      (fun i : Fin m => ξ (n + i.val) ω) ∈
        ⋃ j : Fin m, {Function.update (fun _ => false) j true}} := by
  let A : Set (Fin n → Bool) := {v | (∑ i, if v i then (1 : ℝ) else 0) < c}
  let B : Set (Fin m → Bool) := ⋃ j : Fin m, {Function.update (fun _ => false) j true}
  let μ := Measure.pi (fun _ : Fin n => bernoulliMeasure true false p)
  let ν := Measure.pi (fun _ : Fin m => bernoulliMeasure true false p)
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have hB : MeasurableSet B := (Set.toFinite B).measurableSet
  have hgood : 1 / 2 ≤ μ.real A := by
    apply probability_small_of_integral μ Measurable.of_discrete
      (bernoulli_count_integrable p n) (fun _ => by positivity) hc
    simpa only [μ, bernoulli_count_integral] using hmean
  have hone : 7 / 2 * δ ≤ ν.real B := by
    rw [show ν.real B = (m : ℝ) * p * (1 - p) ^ (m - 1) from
      bernoulli_exactly_one_probability p m]
    exact one_rare_lower p.2.1 hδ0.le hδ1 hlo hhi
  have hlaw := iid_prefix_window_law h n m
  have heq : P {ω | (∑ i : Fin n, if ξ i ω then (1 : ℝ) else 0) < c ∧
      (fun i : Fin m => ξ (n + i.val) ω) ∈ B} = (μ.prod ν) (A ×ˢ B) := by
    rw [← hlaw.map_eq, Measure.map_apply hlaw.measurable (hA.prod hB)]
    rfl
  change δ < (P {ω | (∑ i : Fin n, if ξ i ω then (1 : ℝ) else 0) < c ∧
      (fun i : Fin m => ξ (n + i.val) ω) ∈ B}).toReal
  rw [heq, Measure.prod_prod, ENNReal.toReal_mul]
  change δ < μ.real A * ν.real B
  have hh := mul_le_mul hgood hone (by linarith : 0 ≤ 7 / 2 * δ) (by positivity : 0 ≤ μ.real A)
  nlinarith

end OracleTemplate.FixedBatchConfidence
