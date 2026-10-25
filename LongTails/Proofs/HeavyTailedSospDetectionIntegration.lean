import LongTails.Proofs.HeavyTailedSospDetection
import LongTails.Proofs.HeavyTailedSospWork

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace LongTails.Proofs.HeavyTailedSospDetectionIntegration


open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open HeavyTailedProductProcess HeavyTailedSospExecution HeavyTailedSospDetection
open HeavyTailedSospWork HeavyTailedSospEpochIntegration

lemma ncInit_detector_choice (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target n : ℕ) (ξ : ℕ → Aux p c × p.Ω) (v : Space p)
    (hnc : (trajectory (sampleStep p c g H) n (initial p target) ξ).phase = .ncInit v) :
    detectorChoice p c H
      (trajectory (sampleStep p c g H) (n - detectorCalls c) (initial p target) ξ).point
      (fun k => ξ (n - detectorCalls c + k)) (max 1 c.repeats) = some v := by
  obtain ⟨hDn, hstart, _⟩ := ncInit_detector_origin p c g H target n ξ v hnc
  let s := trajectory (sampleStep p c g H) (n - detectorCalls c) (initial p target) ξ
  have hs : {s with phase := .probeInit 0 none} = s := by
    rw [← hstart]
  have hcomplete := detector_complete p c g H s (fun k => ξ (n - detectorCalls c + k))
  rw [hs] at hcomplete
  have htraj : trajectory (sampleStep p c g H) n (initial p target) ξ =
      trajectory (sampleStep p c g H) (detectorCalls c) s
        (fun k => ξ (n - detectorCalls c + k)) := by
    conv_lhs => rw [← Nat.sub_add_cancel hDn]
    exact trajectory_add _ _ _ _ _
  rw [htraj] at hnc
  change (trajectory (sampleStep p c g H)
    (max 1 c.repeats * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups)) s _).phase = _ at hnc
  rw [hcomplete] at hnc
  cases hc : detectorChoice p c H s.point (fun k => ξ (n - detectorCalls c + k)) (max 1 c.repeats) with
  | none =>
    simp only [hc] at hnc
    unfold startCycle at hnc
    split at hnc <;> contradiction
  | some w =>
    simp only [hc, Phase.ncInit.injEq] at hnc
    simp only [hnc]

lemma measurable_detectorStart (p : Params) : Measurable (detectorStart p) := by
  have hh : Measurable (Function.uncurry (fun ph (_ : Unit) => detectorStart p ph)) := by
    apply HeavyTailedSospMeasurable.measurable_phase_uncurry p
    · exact measurable_const
    · exact measurable_const
    · have hm : Measurable (Function.uncurry
          (fun a (w : ℕ × Unit) => detectorStart p
            (.probeInit w.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm a)))) := by
        apply HeavyTailedSospMeasurable.measurable_sum_uncurry (F :=
          fun (a : Space p ⊕ PUnit.{1}) (w : ℕ × Unit) => detectorStart p
            (.probeInit w.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm a)))
        · convert (measurable_const (a := (0 : ℕ))) using 1
          funext z
          rcases z with ⟨v, k, u⟩
          cases k <;> rfl
        · have hk : Measurable (fun k : ℕ => detectorStart p (.probeInit k none)) :=
            measurable_of_countable _
          exact hk.comp measurable_snd.fst
      have hz : Measurable (fun w : (ℕ × HeavyTailedSospMeasurable.AcceptedCode p) × Unit =>
          (w.1.2, (w.1.1, w.2))) := by fun_prop
      exact hm.comp hz
    all_goals exact measurable_const
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

def selectedStartEvent (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (S : Set (Space p × Space p)) : Set (State p × (ℕ → Aux p c × p.Ω)) :=
  {z | detectorStart p z.1.phase = 1 ∧
    ∃ v, detectorChoice p c H z.1.point z.2 (max 1 c.repeats) = some v ∧ (z.1.point, v) ∈ S}

lemma selectedStartEvent_measurable (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H))
    (S : Set (Space p × Space p)) (hS : MeasurableSet S) :
    MeasurableSet (selectedStartEvent p c H S) := by
  have hs : MeasurableSet {z : State p × (ℕ → Aux p c × p.Ω) |
      detectorStart p z.1.phase = 1} := measurableSet_eq_fun
    ((measurable_detectorStart p).comp ((HeavyTailedSospMeasurable.measurable_phase p).comp
      measurable_fst)) measurable_const
  have hp : Measurable (fun z : State p × (ℕ → Aux p c × p.Ω) => (z.1.point, z.2)) :=
    ((HeavyTailedSospMeasurable.measurable_point p).comp measurable_fst).prodMk measurable_snd
  exact hs.inter ((detectorChoice_selected_measurable p c H hH (max 1 c.repeats) S hS).preimage hp)

lemma ncInit_owning_selected_event (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (S : Set (Space p × Space p)) (target n : ℕ)
    (ξ : ℕ → Aux p c × p.Ω) (v : Space p)
    (hnc : (trajectory (sampleStep p c g H) n (initial p target) ξ).phase = .ncInit v)
    (hS : ((trajectory (sampleStep p c g H) n (initial p target) ξ).point, v) ∈ S) :
    (trajectory (sampleStep p c g H) (n - detectorCalls c) (initial p target) ξ,
      fun k => ξ (n - detectorCalls c + k)) ∈ selectedStartEvent p c H S := by
  obtain ⟨_, hstart, hpoint⟩ := ncInit_detector_origin p c g H target n ξ v hnc
  refine ⟨?_, v, ncInit_detector_choice p c g H target n ξ v hnc, ?_⟩
  · simp only [hstart, detectorStart]
  · simpa only [hpoint] using hS

open Classical in
lemma ncInit_selected_event_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (S : Set (Space p × Space p)) (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    (∑ n ∈ Finset.range N, if ∃ v,
      (trajectory (sampleStep p c g H) n (initial p target) ξ).phase = .ncInit v ∧
      ((trajectory (sampleStep p c g H) n (initial p target) ξ).point, v) ∈ S
      then (1 : ℝ) else 0) ≤
    ∑ k ∈ Finset.range N, if
      (trajectory (sampleStep p c g H) k (initial p target) ξ, fun j => ξ (k + j)) ∈
        selectedStartEvent p c H S then (1 : ℝ) else 0 := by
  classical
  let X := fun n => trajectory (sampleStep p c g H) n (initial p target) ξ
  let E := fun n => ∃ v, (X n).phase = .ncInit v ∧ ((X n).point, v) ∈ S
  let A := (Finset.range N).filter E
  let B := fun k => if (X k, fun j => ξ (k + j)) ∈ selectedStartEvent p c H S then (1 : ℝ) else 0
  have howner (n : ℕ) (hn : n ∈ A) : detectorCalls c ≤ n ∧ B (n - detectorCalls c) = 1 := by
    obtain ⟨v, hv, hs⟩ := (Finset.mem_filter.mp hn).2
    refine ⟨(ncInit_detector_origin p c g H target n ξ v hv).1, ?_⟩
    have he := ncInit_owning_selected_event p c g H S target n ξ v hv hs
    exact ite_eq_left he
  have hh := finite_sum_injection_bound A (Finset.range N) (fun _ => (1 : ℝ)) B
    (fun n => n - detectorCalls c)
    (fun n hn => Finset.mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _)
      (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)))
    (by intro n hn m hm he; have hn' := (howner n hn).1; have hm' := (howner m hm).1; omega)
    (fun n hn => le_of_eq (howner n hn).2.symm)
    (fun k _ => by dsimp [B]; split <;> norm_num)
  simpa only [A, Finset.sum_filter, X, E, B] using hh

lemma selectedStartEvent_fiber_bound (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (S : Set (Space p × Space p))
    (P : Measure (ℕ → Aux p c × p.Ω)) (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x, P.real {ξ | ∃ v, detectorChoice p c H x ξ (max 1 c.repeats) = some v ∧
      (x, v) ∈ S} ≤ ν) (s : State p) :
    P.real (Prod.mk s ⁻¹' selectedStartEvent p c H S) ≤ ν * detectorStart p s.phase := by
  by_cases hs : detectorStart p s.phase = 1
  · simpa only [selectedStartEvent, Set.preimage, Set.mem_ofPred_eq, hs, true_and,
      Nat.cast_one, mul_one] using hb s.point
  · have he : Prod.mk s ⁻¹' selectedStartEvent p c H S = ∅ := by
      ext ξ
      simp only [selectedStartEvent, Set.mem_preimage, Set.mem_ofPred_eq, hs,
        false_and, Set.mem_empty_iff_false]
    rw [he, measureReal_empty]
    positivity

lemma selectedStartEvent_fiber_integral (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H))
    (S : Set (Space p × Space p)) (hS : MeasurableSet S)
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x, P.real {ξ | ∃ v, detectorChoice p c H x ξ (max 1 c.repeats) = some v ∧
      (x, v) ∈ S} ≤ ν) (s : State p) :
    Integrable (fun ξ => (selectedStartEvent p c H S).indicator (fun _ => (1 : ℝ)) (s, ξ)) P ∧
      (∫ ξ, (selectedStartEvent p c H S).indicator (fun _ => (1 : ℝ)) (s, ξ) ∂P) ≤
        ν * detectorStart p s.phase := by
  have he := (selectedStartEvent_measurable p c H hH S hS).preimage
    (measurable_prodMk_left (x := s))
  change Integrable ((Prod.mk s ⁻¹' selectedStartEvent p c H S).indicator 1) P ∧ _
  refine ⟨(integrable_const (1 : ℝ)).indicator he, ?_⟩
  change (∫ ξ, (Prod.mk s ⁻¹' selectedStartEvent p c H S).indicator 1 ξ ∂P) ≤ _
  rw [integral_indicator_one he]
  exact selectedStartEvent_fiber_bound p c H S P ν hν hb s

lemma detectorStart_le_one (p : Params) (ph : Phase p) : detectorStart p ph ≤ 1 := by
  cases ph with
  | probeInit k a => cases k <;> cases a <;> simp [detectorStart]
  | reset => simp [detectorStart]
  | transport => simp [detectorStart]
  | probe => simp [detectorStart]
  | validate => simp [detectorStart]
  | ncInit => simp [detectorStart]
  | done => simp [detectorStart]

lemma prefix_selected_event_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H))
    (S : Set (Space p × Space p)) (hS : MeasurableSet S)
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x, (Measure.infinitePi fun _ : ℕ => Q).real
      {ξ | ∃ v, detectorChoice p c H x ξ (max 1 c.repeats) = some v ∧ (x, v) ∈ S} ≤ ν)
    (n : ℕ) (s : State p) :
    Integrable (fun ξ => (selectedStartEvent p c H S).indicator (fun _ => (1 : ℝ))
      (trajectory (sampleStep p c g H) n s ξ, fun k => ξ (n + k)))
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ, (selectedStartEvent p c H S).indicator (fun _ => (1 : ℝ))
      (trajectory (sampleStep p c g H) n s ξ, fun k => ξ (n + k))
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
      ν * ∫ ξ, (detectorStart p (trajectory (sampleStep p c g H) n s ξ).phase : ℝ)
        ∂Measure.infinitePi (fun _ : ℕ => Q) := by
  classical
  let advance := sampleStep p c g H
  let F : State p × (ℕ → Aux p c × p.Ω) → ℝ :=
    (selectedStartEvent p c H S).indicator (fun _ => 1)
  have ha := HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH
  have hprefix : Measurable (fun η : Fin n → Aux p c × p.Ω =>
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η) :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable ha n).comp
      ((measurable_const (a := s)).prodMk measurable_id)
  let V := fun η : Fin n → Aux p c × p.Ω =>
    (detectorStart p (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η).phase : ℝ)
  have hV : Measurable V :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      ((measurable_detectorStart p).comp ((HeavyTailedSospMeasurable.measurable_phase p).comp hprefix))
  have hVi : Integrable V (Measure.pi fun _ : Fin n => Q) := by
    apply (integrable_const (1 : ℝ)).mono' hV.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro η
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [V]; positivity)]
    dsimp only [V]
    exact_mod_cast detectorStart_le_one p _
  have hF : Measurable F := measurable_const.indicator (selectedStartEvent_measurable p c H hH S hS)
  have hnon : ∀ z, 0 ≤ F z := by intro z; simp only [F, Set.indicator_apply]; split_ifs <;> norm_num
  have hf := fresh_continuation_bound Q advance ha n s F hF hnon (fun η => ν * V η)
    (hVi.const_mul ν)
    (fun η => (selectedStartEvent_fiber_integral p c H hH S hS _ ν hν hb _).1)
    (fun η => (selectedStartEvent_fiber_integral p c H hH S hS _ ν hν hb _).2)
  refine ⟨hf.1, ?_⟩
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving Q n
  have heq : (∫ η, V η ∂Measure.pi (fun _ : Fin n => Q)) =
      ∫ ξ, (detectorStart p (trajectory advance n s ξ).phase : ℝ)
        ∂Measure.infinitePi (fun _ : ℕ => Q) := by
    rw [← hpre.map_eq, integral_map hpre.measurable.aemeasurable hV.aestronglyMeasurable]
    simp only [V, trajectory_finite]
  simpa only [integral_const_mul, heq] using hf.2

def ncSelectedEvent (p : Params) (S : Set (Space p × Space p)) : Set (State p) :=
  {s | ∃ v, s.phase = .ncInit v ∧ (s.point, v) ∈ S}

lemma ncSelectedEvent_measurable (p : Params) (S : Set (Space p × Space p))
    (hS : MeasurableSet S) : MeasurableSet (ncSelectedEvent p S) := by
  classical
  have hm : Measurable (Function.uncurry (fun (ph : Phase p) (x : Space p) =>
      if ∃ v, ph = .ncInit v ∧ (x, v) ∈ S then (1 : ℕ) else 0)) := by
    apply HeavyTailedSospMeasurable.measurable_phase_uncurry p
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp only [Phase.ncInit.injEq, exists_eq_left']
      exact Measurable.ite (hS.preimage (measurable_snd.prodMk measurable_fst))
        measurable_const measurable_const
    · simp
  have hc := hm.comp ((HeavyTailedSospMeasurable.measurable_phase p).prodMk
    (HeavyTailedSospMeasurable.measurable_point p))
  have he := measurableSet_eq_fun hc (measurable_const (a := (1 : ℕ)))
  simpa [Function.comp_def, Function.uncurry, ncSelectedEvent] using he

lemma expected_ncSelected_count_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H))
    (S : Set (Space p × Space p)) (hS : MeasurableSet S)
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x, (Measure.infinitePi fun _ : ℕ => Q).real
      {ξ | ∃ v, detectorChoice p c H x ξ (max 1 c.repeats) = some v ∧ (x, v) ∈ S} ≤ ν)
    (target N : ℕ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    Integrable (fun ξ => ∑ n ∈ Finset.range N, (ncSelectedEvent p S).indicator (fun _ => (1 : ℝ))
      (trajectory (sampleStep p c g H) n (initial p target) ξ))
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ, ∑ n ∈ Finset.range N, (ncSelectedEvent p S).indicator (fun _ => (1 : ℝ))
      (trajectory (sampleStep p c g H) n (initial p target) ξ)
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ ν * c.cycles := by
  let P := Measure.infinitePi fun _ : ℕ => Q
  let X := fun n ξ => trajectory (sampleStep p c g H) n (initial p target) ξ
  let F := fun n ξ => (ncSelectedEvent p S).indicator (fun _ => (1 : ℝ)) (X n ξ)
  let D := fun n ξ => (selectedStartEvent p c H S).indicator (fun _ => (1 : ℝ))
    (X n ξ, fun k => ξ (n + k))
  let C := fun n ξ => (detectorStart p (X n ξ).phase : ℝ)
  have hX (n : ℕ) : Measurable (X n) :=
    (trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) n).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hFi (n : ℕ) : Integrable (F n) P :=
    (integrable_const (1 : ℝ)).indicator ((ncSelectedEvent_measurable p S hS).preimage (hX n))
  have hD (n : ℕ) : Integrable (D n) P ∧ (∫ ξ, D n ξ ∂P) ≤ ν * ∫ ξ, C n ξ ∂P :=
    prefix_selected_event_bound p c g hg H hH S hS Q ν hν hb n (initial p target)
  have hCi (n : ℕ) : Integrable (C n) P := by
    have hm : Measurable (C n) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
        ((measurable_detectorStart p).comp ((HeavyTailedSospMeasurable.measurable_phase p).comp (hX n)))
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [C]; positivity)]
    dsimp only [C]
    exact_mod_cast detectorStart_le_one p _
  have hsumF : Integrable (fun ξ => ∑ n ∈ Finset.range N, F n ξ) P :=
    integrable_finsetSum _ (fun n _ => hFi n)
  have hsumD : Integrable (fun ξ => ∑ n ∈ Finset.range N, D n ξ) P :=
    integrable_finsetSum _ (fun n _ => (hD n).1)
  have hpath (ξ : ℕ → Aux p c × p.Ω) :
      (∑ n ∈ Finset.range N, F n ξ) ≤ ∑ n ∈ Finset.range N, D n ξ := by
    convert ncInit_selected_event_count p c g H S target N ξ using 1 <;> rfl
  have hcount (ξ : ℕ → Aux p c × p.Ω) : (∑ n ∈ Finset.range N, C n ξ) = c.cycles := by
    have hc := completed_detector_start_count p c g H target N ξ (hdone ξ)
    dsimp only [C, X]
    exact_mod_cast hc
  refine ⟨hsumF, ?_⟩
  calc
    (∫ ξ, ∑ n ∈ Finset.range N, F n ξ ∂P) ≤
        ∫ ξ, ∑ n ∈ Finset.range N, D n ξ ∂P := integral_mono hsumF hsumD hpath
    _ = ∑ n ∈ Finset.range N, ∫ ξ, D n ξ ∂P := integral_finsetSum _ (fun n _ => (hD n).1)
    _ ≤ ∑ n ∈ Finset.range N, ν * ∫ ξ, C n ξ ∂P := Finset.sum_le_sum (fun n _ => (hD n).2)
    _ = ν * ∫ ξ, ∑ n ∈ Finset.range N, C n ξ ∂P := by
      rw [integral_finsetSum _ (fun n _ => hCi n), Finset.mul_sum]
    _ = ν * c.cycles := by simp only [hcount, integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma primitive_expected_bad_curvature_count (p : Params) (hd : 0 < p.d) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (A : Space p → Space p →L[ℝ] Space p) (hA : Measurable A)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hγ : 0 < c.γ)
    (hi : ∀ x v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ x v, (∫ ω, H x ω v ∂P0) = A x v)
    (hpi : ∀ x v, Integrable (fun ω => ‖H x ω v - A x v‖ ^ p.p) P0)
    (hb : ∀ x v, (∫ ω, ‖H x ω v - A x v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (htune : 6 * p.σh ^ p.p / ((max 1 c.meanBatch : ℕ) : ℝ) ^ (p.p - 1) ≤ (c.γ / 8) ^ p.p)
    (target N : ℕ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let S := {z : Space p × Space p | -3 * c.γ / 2 < inner ℝ z.2 (A z.1 z.2)}
    let P := Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0
    Integrable (fun ξ => ∑ n ∈ Finset.range N, (ncSelectedEvent p S).indicator (fun _ => (1 : ℝ))
      (trajectory (sampleStep p c g H) n (initial p target) ξ)) P ∧
    (∫ ξ, ∑ n ∈ Finset.range N, (ncSelectedEvent p S).indicator (fun _ => (1 : ℝ))
      (trajectory (sampleStep p c g H) n (initial p target) ξ) ∂P) ≤
        ((max 1 c.repeats : ℕ) : ℝ) * Real.exp (-((max 1 c.groups : ℕ) : ℝ) / 8) * c.cycles := by
  intro S P
  have hAv : Measurable (fun z : Space p × Space p => A z.1 z.2) :=
    isBoundedBilinearMap_apply.continuous.measurable.comp ((hA.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_snd.inner hAv)
  apply expected_ncSelected_count_bound p c g hg H hH S hS
    ((auxLaw p c : Measure (Aux p c)).prod P0)
    (((max 1 c.repeats : ℕ) : ℝ) * Real.exp (-((max 1 c.groups : ℕ) : ℝ) / 8))
    (by positivity) _ target N hdone
  intro x
  exact detector_false_acceptance_probability p c H hH x P0 (A x) (max 1 c.repeats) _
    (trial_validation_probability p hd c x H (A x) hH P0 hp hp2 hγ (hi x) (hm x) (hpi x) (hb x) htune)

def strictBadCurvature (p : Params) (A : Space p → Space p →L[ℝ] Space p) (κ : ℝ) : Set (Space p) :=
  {x | ∃ v, ‖v‖ = 1 ∧ inner ℝ v (A x v) < κ}

lemma strictBadCurvature_isOpen (p : Params) (A : Space p → Space p →L[ℝ] Space p)
    (hA : Continuous A) (κ : ℝ) : IsOpen (strictBadCurvature p A κ) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨v, hv, hx⟩ := hx
  refine ⟨{y | inner ℝ v (A y v) < κ}, ?_, ?_, hx⟩
  · intro y hy
    exact ⟨v, hv, hy⟩
  · have hAv : Continuous (fun y => A y v) :=
      isBoundedBilinearMap_apply.continuous.comp (hA.prodMk continuous_const)
    exact isOpen_lt (continuous_const.inner hAv) continuous_const

def missedStartEvent (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (B : Set (Space p)) :
    Set (State p × (ℕ → Aux p c × p.Ω)) :=
  {z | detectorStart p z.1.phase = 1 ∧ z.1.point ∈ B ∧
    detectorChoice p c H z.1.point z.2 (max 1 c.repeats) = none}

lemma missedStartEvent_measurable (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (B : Set (Space p)) (hB : MeasurableSet B) : MeasurableSet (missedStartEvent p c H B) := by
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun ((measurable_detectorStart p).comp
      ((HeavyTailedSospMeasurable.measurable_phase p).comp measurable_fst)) measurable_const
  · apply MeasurableSet.inter
    · exact hB.preimage ((HeavyTailedSospMeasurable.measurable_point p).comp measurable_fst)
    · exact (detectorChoice_none_measurable p c H hH (max 1 c.repeats)).preimage
        (((HeavyTailedSospMeasurable.measurable_point p).comp measurable_fst).prodMk measurable_snd)

lemma missedStartEvent_fiber_bound (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (B : Set (Space p))
    (P : Measure (ℕ → Aux p c × p.Ω)) (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x ∈ B, P.real {ξ | detectorChoice p c H x ξ (max 1 c.repeats) = none} ≤ ν)
    (s : State p) :
    P.real {ξ | (s, ξ) ∈ missedStartEvent p c H B} ≤ ν * detectorStart p s.phase := by
  by_cases hs : detectorStart p s.phase = 1
  · by_cases hx : s.point ∈ B
    · simpa only [missedStartEvent, Set.mem_ofPred_eq, hs, hx, true_and, Nat.cast_one, mul_one] using hb s.point hx
    · simp [missedStartEvent, hx, hs]
      exact hν
  · have he : {ξ | (s, ξ) ∈ missedStartEvent p c H B} = ∅ := by ext ξ; simp [missedStartEvent, hs]
    rw [he, measureReal_empty]
    positivity

lemma missedStartEvent_fiber_integral (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H))
    (B : Set (Space p)) (hB : MeasurableSet B)
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x ∈ B, P.real {ξ | detectorChoice p c H x ξ (max 1 c.repeats) = none} ≤ ν) (s : State p) :
    Integrable (fun ξ => (missedStartEvent p c H B).indicator (fun _ => (1 : ℝ)) (s, ξ)) P ∧
      (∫ ξ, (missedStartEvent p c H B).indicator (fun _ => (1 : ℝ)) (s, ξ) ∂P) ≤
        ν * detectorStart p s.phase := by
  have he := (missedStartEvent_measurable p c H hH B hB).preimage
    (measurable_prodMk_left (x := s))
  change Integrable ((Prod.mk s ⁻¹' missedStartEvent p c H B).indicator 1) P ∧ _
  refine ⟨(integrable_const (1 : ℝ)).indicator he, ?_⟩
  change (∫ ξ, (Prod.mk s ⁻¹' missedStartEvent p c H B).indicator 1 ξ ∂P) ≤ _
  rw [integral_indicator_one he]
  exact missedStartEvent_fiber_bound p c H B P ν hν hb s

lemma prefix_missed_event_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H))
    (B : Set (Space p)) (hB : MeasurableSet B)
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x ∈ B, (Measure.infinitePi fun _ : ℕ => Q).real
      {ξ | detectorChoice p c H x ξ (max 1 c.repeats) = none} ≤ ν)
    (n : ℕ) (s : State p) :
    Integrable (fun ξ => (missedStartEvent p c H B).indicator (fun _ => (1 : ℝ))
      (trajectory (sampleStep p c g H) n s ξ, fun k => ξ (n + k)))
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ, (missedStartEvent p c H B).indicator (fun _ => (1 : ℝ))
      (trajectory (sampleStep p c g H) n s ξ, fun k => ξ (n + k))
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
      ν * ∫ ξ, (detectorStart p (trajectory (sampleStep p c g H) n s ξ).phase : ℝ)
        ∂Measure.infinitePi (fun _ : ℕ => Q) := by
  classical
  let advance := sampleStep p c g H
  let F : State p × (ℕ → Aux p c × p.Ω) → ℝ :=
    (missedStartEvent p c H B).indicator (fun _ => 1)
  have ha := HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH
  have hprefix : Measurable (fun η : Fin n → Aux p c × p.Ω =>
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η) :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable ha n).comp
      ((measurable_const (a := s)).prodMk measurable_id)
  let V := fun η : Fin n → Aux p c × p.Ω =>
    (detectorStart p (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η).phase : ℝ)
  have hV : Measurable V :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      ((measurable_detectorStart p).comp ((HeavyTailedSospMeasurable.measurable_phase p).comp hprefix))
  have hVi : Integrable V (Measure.pi fun _ : Fin n => Q) := by
    apply (integrable_const (1 : ℝ)).mono' hV.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro η
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [V]; positivity)]
    dsimp only [V]
    exact_mod_cast detectorStart_le_one p _
  have hF : Measurable F := measurable_const.indicator (missedStartEvent_measurable p c H hH B hB)
  have hnon : ∀ z, 0 ≤ F z := by intro z; simp only [F, Set.indicator_apply]; split_ifs <;> norm_num
  have hf := fresh_continuation_bound Q advance ha n s F hF hnon (fun η => ν * V η)
    (hVi.const_mul ν)
    (fun η => (missedStartEvent_fiber_integral p c H hH B hB _ ν hν hb _).1)
    (fun η => (missedStartEvent_fiber_integral p c H hH B hB _ ν hν hb _).2)
  refine ⟨hf.1, ?_⟩
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving Q n
  have heq : (∫ η, V η ∂Measure.pi (fun _ : Fin n => Q)) =
      ∫ ξ, (detectorStart p (trajectory advance n s ξ).phase : ℝ)
        ∂Measure.infinitePi (fun _ : ℕ => Q) := by
    rw [← hpre.map_eq, integral_map hpre.measurable.aemeasurable hV.aestronglyMeasurable]
    simp only [V, trajectory_finite]
  simpa only [integral_const_mul, heq] using hf.2


lemma expected_missed_start_count_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (B : Set (Space p)) (hB : MeasurableSet B)
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x ∈ B, (Measure.infinitePi fun _ : ℕ => Q).real
      {ξ | detectorChoice p c H x ξ (max 1 c.repeats) = none} ≤ ν)
    (target N : ℕ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let P := Measure.infinitePi fun _ : ℕ => Q
    let X := fun n ξ => trajectory (sampleStep p c g H) n (initial p target) ξ
    Integrable (fun ξ => ∑ n ∈ Finset.range N, (missedStartEvent p c H B).indicator
      (fun _ => (1 : ℝ)) (X n ξ, fun k => ξ (n + k))) P ∧
    (∫ ξ, ∑ n ∈ Finset.range N, (missedStartEvent p c H B).indicator
      (fun _ => (1 : ℝ)) (X n ξ, fun k => ξ (n + k)) ∂P) ≤ ν * c.cycles := by
  intro P X
  let D := fun n ξ => (missedStartEvent p c H B).indicator (fun _ => (1 : ℝ))
    (X n ξ, fun k => ξ (n + k))
  let C := fun n ξ => (detectorStart p (X n ξ).phase : ℝ)
  have hD (n : ℕ) : Integrable (D n) P ∧ (∫ ξ, D n ξ ∂P) ≤ ν * ∫ ξ, C n ξ ∂P :=
    prefix_missed_event_bound p c g hg H hH B hB Q ν hν hb n (initial p target)
  have hX (n : ℕ) : Measurable (X n) :=
    (trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) n).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hCi (n : ℕ) : Integrable (C n) P := by
    have hm : Measurable (C n) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
        ((measurable_detectorStart p).comp ((HeavyTailedSospMeasurable.measurable_phase p).comp (hX n)))
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [C]; positivity)]
    dsimp only [C]
    exact_mod_cast detectorStart_le_one p _
  have hcount : (fun ξ => ∑ n ∈ Finset.range N, C n ξ) = fun _ => (c.cycles : ℝ) := by
    funext ξ
    have hc := completed_detector_start_count p c g H target N ξ (hdone ξ)
    dsimp only [C, X]
    exact_mod_cast hc
  refine ⟨integrable_finsetSum _ (fun n _ => (hD n).1), ?_⟩
  calc
    (∫ ξ, ∑ n ∈ Finset.range N, D n ξ ∂P) =
        ∑ n ∈ Finset.range N, ∫ ξ, D n ξ ∂P := integral_finsetSum _ (fun n _ => (hD n).1)
    _ ≤ ∑ n ∈ Finset.range N, ν * ∫ ξ, C n ξ ∂P := Finset.sum_le_sum (fun n _ => (hD n).2)
    _ = ν * ∫ ξ, ∑ n ∈ Finset.range N, C n ξ ∂P := by
      rw [integral_finsetSum _ (fun n _ => hCi n), Finset.mul_sum]
    _ = ν * c.cycles := by simp only [hcount, integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma detector_choice_ncInit (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target k : ℕ) (ξ : ℕ → Aux p c × p.Ω) (v : Space p)
    (hstart : (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = .probeInit 0 none)
    (hchoice : detectorChoice p c H (trajectory (sampleStep p c g H) k (initial p target) ξ).point
      (fun i => ξ (k + i)) (max 1 c.repeats) = some v) :
    (trajectory (sampleStep p c g H) (k + detectorCalls c) (initial p target) ξ).phase = .ncInit v := by
  let s := trajectory (sampleStep p c g H) k (initial p target) ξ
  have hs : {s with phase := .probeInit 0 none} = s := by rw [← hstart]
  have hc := detector_complete p c g H s (fun i => ξ (k + i))
  rw [hs, hchoice] at hc
  rw [trajectory_add]
  change (trajectory (sampleStep p c g H)
    (max 1 c.repeats * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups)) s _).phase = _
  rw [hc]

lemma accepted_start_before_completion (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target k N : ℕ) (ξ : ℕ → Aux p c × p.Ω) (v : Space p)
    (hstart : (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = .probeInit 0 none)
    (hchoice : detectorChoice p c H (trajectory (sampleStep p c g H) k (initial p target) ξ).point
      (fun i => ξ (k + i)) (max 1 c.repeats) = some v)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    k + detectorCalls c < N := by
  have hn := detector_choice_ncInit p c g H target k ξ v hstart hchoice
  by_contra hbad
  have hNk : N ≤ k + detectorCalls c := by omega
  have he := HeavyTailedSospExecution.completion_absorbing p c g H (initial p target) ξ N
    (k + detectorCalls c - N) hdone
  rw [Nat.add_sub_of_le hNk] at he
  rw [he, hdone] at hn
  contradiction

lemma detectorStart_eq_one_iff (p : Params) (ph : Phase p) :
    detectorStart p ph = 1 ↔ ph = .probeInit 0 none := by
  cases ph with
  | probeInit k a => cases k <;> cases a <;> simp [detectorStart]
  | reset => simp [detectorStart]
  | transport => simp [detectorStart]
  | probe => simp [detectorStart]
  | validate => simp [detectorStart]
  | ncInit => simp [detectorStart]
  | done => simp [detectorStart]

open Classical in
lemma selected_start_ncCharge_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (S : Set (Space p × Space p)) (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (∑ k ∈ Finset.range N, if
      (trajectory (sampleStep p c g H) k (initial p target) ξ, fun j => ξ (k + j)) ∈
        selectedStartEvent p c H S then (1 : ℝ) else 0) ≤
    ∑ n ∈ Finset.range N, (ncCharge p
      (trajectory (sampleStep p c g H) n (initial p target) ξ).phase : ℝ) := by
  classical
  let X := fun n => trajectory (sampleStep p c g H) n (initial p target) ξ
  let E := fun k => (X k, fun j => ξ (k + j)) ∈ selectedStartEvent p c H S
  let F := (Finset.range N).filter E
  let C := fun n => (ncCharge p (X n).phase : ℝ)
  have howner (k : ℕ) (hk : k ∈ F) : k + detectorCalls c < N ∧ C (k + detectorCalls c) = 1 := by
    obtain ⟨hs, v, hc, _⟩ := (Finset.mem_filter.mp hk).2
    have hp := (detectorStart_eq_one_iff p _).mp hs
    refine ⟨accepted_start_before_completion p c g H target k N ξ v hp hc hdone, ?_⟩
    have hn := detector_choice_ncInit p c g H target k ξ v hp hc
    simp only [C, X, hn, ncCharge, Nat.cast_one]
  have hh := finite_sum_injection_bound F (Finset.range N) (fun _ => (1 : ℝ)) C
    (fun k => k + detectorCalls c)
    (fun k hk => Finset.mem_range.mpr (howner k hk).1)
    (by intros; omega)
    (fun k hk => le_of_eq (howner k hk).2.symm)
    (fun k _ => Nat.cast_nonneg _)
  simpa only [F, Finset.sum_filter, E, X, C] using hh

def badStartEvent (p : Params) (B : Set (Space p)) : Set (State p) :=
  {s | detectorStart p s.phase = 1 ∧ s.point ∈ B}

lemma badStartEvent_measurable (p : Params) (B : Set (Space p)) (hB : MeasurableSet B) :
    MeasurableSet (badStartEvent p B) :=
  (measurableSet_eq_fun ((measurable_detectorStart p).comp
    (HeavyTailedSospMeasurable.measurable_phase p)) measurable_const).inter
      (hB.preimage (HeavyTailedSospMeasurable.measurable_point p))

lemma badStart_indicator_bound (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (B : Set (Space p))
    (s : State p) (ξ : ℕ → Aux p c × p.Ω) :
    (badStartEvent p B).indicator (fun _ => (1 : ℝ)) s ≤
      (selectedStartEvent p c H Set.univ).indicator (fun _ => (1 : ℝ)) (s, ξ) +
        (missedStartEvent p c H B).indicator (fun _ => (1 : ℝ)) (s, ξ) := by
  classical
  by_cases hs : detectorStart p s.phase = 1
  · by_cases hx : s.point ∈ B
    · cases hc : detectorChoice p c H s.point ξ (max 1 c.repeats) with
      | none => simp [badStartEvent, selectedStartEvent, missedStartEvent, hs, hx, hc]
      | some v => simp [badStartEvent, selectedStartEvent, missedStartEvent, hs, hx, hc]
    · simp only [badStartEvent, selectedStartEvent, missedStartEvent, Set.indicator_apply,
        Set.mem_ofPred_eq, hs, hx, true_and, false_and, ↓reduceIte, add_zero]
      split_ifs <;> norm_num
  · simp [badStartEvent, selectedStartEvent, missedStartEvent, hs]

lemma bad_start_count_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (B : Set (Space p)) (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let X := fun n => trajectory (sampleStep p c g H) n (initial p target) ξ
    (∑ n ∈ Finset.range N, (badStartEvent p B).indicator (fun _ => (1 : ℝ)) (X n)) ≤
      (∑ n ∈ Finset.range N, (ncCharge p (X n).phase : ℝ)) +
        ∑ n ∈ Finset.range N, (missedStartEvent p c H B).indicator
          (fun _ => (1 : ℝ)) (X n, fun k => ξ (n + k)) := by
  classical
  intro X
  have hb := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) =>
    badStart_indicator_bound p c H B (X n) (fun k => ξ (n + k)))
  rw [Finset.sum_add_distrib] at hb
  have hc := selected_start_ncCharge_count p c g H Set.univ target N ξ hdone
  have hc' : (∑ n ∈ Finset.range N, (selectedStartEvent p c H Set.univ).indicator
      (fun _ => (1 : ℝ)) (X n, fun k => ξ (n + k))) ≤
      ∑ n ∈ Finset.range N, (ncCharge p (X n).phase : ℝ) := by
    convert hc using 1
    rfl
  exact hb.trans (add_le_add hc' le_rfl)

lemma expected_bad_start_count_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (B : Set (Space p)) (hB : MeasurableSet B)
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∀ x ∈ B, (Measure.infinitePi fun _ : ℕ => Q).real
      {ξ | detectorChoice p c H x ξ (max 1 c.repeats) = none} ≤ ν)
    (target N : ℕ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let P := Measure.infinitePi fun _ : ℕ => Q
    let X := fun n ξ => trajectory (sampleStep p c g H) n (initial p target) ξ
    Integrable (fun ξ => ∑ n ∈ Finset.range N,
      (badStartEvent p B).indicator (fun _ => (1 : ℝ)) (X n ξ)) P ∧
    (∫ ξ, ∑ n ∈ Finset.range N, (badStartEvent p B).indicator (fun _ => (1 : ℝ)) (X n ξ) ∂P) ≤
      (∫ ξ, ∑ n ∈ Finset.range N, (ncCharge p (X n ξ).phase : ℝ) ∂P) + ν * c.cycles := by
  classical
  intro P X
  have hm := expected_missed_start_count_bound p c g hg H hH B hB Q ν hν hb target N hdone
  have hX (n : ℕ) : Measurable (X n) :=
    (trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) n).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hbi (n : ℕ) : Integrable (fun ξ => (badStartEvent p B).indicator (fun _ => (1 : ℝ)) (X n ξ)) P :=
    (integrable_const (1 : ℝ)).indicator ((badStartEvent_measurable p B hB).preimage (hX n))
  have hci (n : ℕ) : Integrable (fun ξ => (ncCharge p (X n ξ).phase : ℝ)) P := by
    have hi := (integrable_const (μ := P) (1 : ℝ)).indicator
      ((ncSelectedEvent_measurable p Set.univ MeasurableSet.univ).preimage (hX n))
    convert hi using 1
    funext ξ
    cases hp : (X n ξ).phase <;> simp [ncCharge, ncSelectedEvent, hp]
  have hBs := integrable_finsetSum (Finset.range N) (fun n _ => hbi n)
  have hCs := integrable_finsetSum (Finset.range N) (fun n _ => hci n)
  refine ⟨hBs, ?_⟩
  calc
    _ ≤ ∫ ξ, (∑ n ∈ Finset.range N, (ncCharge p (X n ξ).phase : ℝ)) +
        ∑ n ∈ Finset.range N, (missedStartEvent p c H B).indicator
          (fun _ => (1 : ℝ)) (X n ξ, fun k => ξ (n + k)) ∂P :=
      integral_mono hBs (hCs.add hm.1) (fun ξ => bad_start_count_bound p c g H B target N ξ (hdone ξ))
    _ = (∫ ξ, ∑ n ∈ Finset.range N, (ncCharge p (X n ξ).phase : ℝ) ∂P) +
        (∫ ξ, ∑ n ∈ Finset.range N, (missedStartEvent p c H B).indicator
          (fun _ => (1 : ℝ)) (X n ξ, fun k => ξ (n + k)) ∂P) := integral_add hCs hm.1
    _ ≤ _ := add_le_add le_rfl hm.2

lemma detector_none_probability (p : Params) (c : Config) (hγ : 0 ≤ c.γ)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) (x : Space p)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (A : Space p →L[ℝ] Space p) (R : ℕ) (a ν : ℝ)
    (hprobe : a ≤ (Measure.infinitePi fun _ : ℕ =>
      (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ)) ≤ -3 * c.γ})
    (hvalid : (Measure.infinitePi fun _ : ℕ =>
      (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | c.γ / 2 < |trialEstimate p c H x ξ -
        inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ))|} ≤ ν) :
    (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | detectorChoice p c H x ξ R = none} ≤ Real.exp (-a * R) + R * ν := by
  have hf := detector_failure_probability p c hγ H hH x P0 A R a ν hprobe hvalid
  apply le_trans (measureReal_mono ?_) hf
  intro ξ hn
  rintro ⟨v, hv, _⟩
  rw [hn] at hv
  contradiction

lemma primitive_detector_none_probability (p : Params) (hd : 0 < p.d) (c : Config)
    (x : Space p) (q : ℝ)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (Hmean : Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (hη : 0 < c.η) (hpq : p.p.HolderConjugate q) (hp2 : p.p ≤ 2)
    (hηM : c.η * (2 * p.L + c.γ) ≤ 1) (hγ : 0 < c.γ) (hσ : 0 ≤ p.σh)
    (hshift : c.shift = p.L + c.γ)
    (hsym : Hmean.toLinearMap.IsSymmetric) (hbound : ‖Hmean‖ ≤ p.L)
    (hi : ∀ v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ v, (∫ ω, H x ω v ∂P0) = Hmean v)
    (hpi : ∀ v, Integrable (fun ω => ‖H x ω v - Hmean v‖ ^ p.p) P0)
    (hb : ∀ v, (∫ ω, ‖H x ω v - Hmean v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (w : Space p) (hw : ‖w‖ = 1) (hbad : inner ℝ w (Hmean w) ≤ -4 * c.γ)
    (htune : 8 * (Real.log (2 * Real.sqrt (2 * p.d)) + 2) ≤ c.η * (max 1 c.probeSteps : ℕ) * c.γ)
    (hsmall : ∀ ell, 0 ≤ ell → ell ≤ 2 * p.L + c.γ →
      ((1 + c.η * ell) ^ p.p + 6 * c.η ^ p.p * p.σh ^ p.p) ^ max 1 c.probeSteps ≤
        (2 * (1 + c.η * ell) ^ max 1 c.probeSteps) ^ p.p)
    (hnoise : (max 1 c.probeSteps : ℕ) * (c.η ^ p.p * p.σh ^ p.p) ≤ (1 / 4 : ℝ) ^ q / 256)
    (hvalidation : 6 * p.σh ^ p.p / ((max 1 c.meanBatch : ℕ) : ℝ) ^ (p.p - 1) ≤ (c.γ / 8) ^ p.p) :
    (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | detectorChoice p c H x ξ (max 1 c.repeats) = none} ≤
        Real.exp (-((1 / 4 : ℝ) ^ q / 64) * (max 1 c.repeats : ℕ)) +
          (max 1 c.repeats : ℕ) * Real.exp (-((max 1 c.groups : ℕ) : ℝ) / 8) := by
  have hp := primitive_curvature_probe_probability p hd c x q H Hmean
    (hH.comp ((measurable_const (a := x)).prodMk measurable_id)) P0
    hη hpq hp2 hηM hγ hσ hshift hsym hbound hi hm hpi hb w hw hbad htune hsmall hnoise
  have hv := trial_validation_probability p hd c x H Hmean hH P0 hpq.lt.le hp2 hγ
    hi hm hpi hb hvalidation
  exact detector_none_probability p c hγ.le H hH x P0 Hmean (max 1 c.repeats)
    ((1 / 4 : ℝ) ^ q / 64) (Real.exp (-((max 1 c.groups : ℕ) : ℝ) / 8)) hp hv

lemma primitive_expected_bad_start_count (p : Params) (hd : 0 < p.d) (c : Config) (q : ℝ)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (A : Space p → Space p →L[ℝ] Space p) (hA : Continuous A)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (hη : 0 < c.η) (hpq : p.p.HolderConjugate q) (hp2 : p.p ≤ 2)
    (hηM : c.η * (2 * p.L + c.γ) ≤ 1) (hγ : 0 < c.γ) (hσ : 0 ≤ p.σh)
    (hshift : c.shift = p.L + c.γ)
    (hsym : ∀ x, (A x).toLinearMap.IsSymmetric) (hbound : ∀ x, ‖A x‖ ≤ p.L)
    (hi : ∀ x v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ x v, (∫ ω, H x ω v ∂P0) = A x v)
    (hpi : ∀ x v, Integrable (fun ω => ‖H x ω v - A x v‖ ^ p.p) P0)
    (hb : ∀ x v, (∫ ω, ‖H x ω v - A x v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (htune : 8 * (Real.log (2 * Real.sqrt (2 * p.d)) + 2) ≤ c.η * (max 1 c.probeSteps : ℕ) * c.γ)
    (hsmall : ∀ ell, 0 ≤ ell → ell ≤ 2 * p.L + c.γ →
      ((1 + c.η * ell) ^ p.p + 6 * c.η ^ p.p * p.σh ^ p.p) ^ max 1 c.probeSteps ≤
        (2 * (1 + c.η * ell) ^ max 1 c.probeSteps) ^ p.p)
    (hnoise : (max 1 c.probeSteps : ℕ) * (c.η ^ p.p * p.σh ^ p.p) ≤ (1 / 4 : ℝ) ^ q / 256)
    (hvalidation : 6 * p.σh ^ p.p / ((max 1 c.meanBatch : ℕ) : ℝ) ^ (p.p - 1) ≤ (c.γ / 8) ^ p.p)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hrisk : Real.exp (-((1 / 4 : ℝ) ^ q / 64) * (max 1 c.repeats : ℕ)) +
      (max 1 c.repeats : ℕ) * Real.exp (-((max 1 c.groups : ℕ) : ℝ) / 8) ≤ δ)
    (target N : ℕ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let P := Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0
    let X := fun n ξ => trajectory (sampleStep p c g H) n (initial p target) ξ
    let B := strictBadCurvature p A (-4 * c.γ)
    Integrable (fun ξ => ∑ n ∈ Finset.range N,
      (badStartEvent p B).indicator (fun _ => (1 : ℝ)) (X n ξ)) P ∧
    (∫ ξ, ∑ n ∈ Finset.range N, (badStartEvent p B).indicator (fun _ => (1 : ℝ)) (X n ξ) ∂P) ≤
      (∫ ξ, ∑ n ∈ Finset.range N, (ncCharge p (X n ξ).phase : ℝ) ∂P) + δ * c.cycles := by
  intro P X B
  apply expected_bad_start_count_bound p c g hg H hH B
    (strictBadCurvature_isOpen p A hA _).measurableSet
    ((auxLaw p c : Measure (Aux p c)).prod P0) δ hδ _ target N hdone
  intro x hx
  obtain ⟨w, hw, hbad⟩ := hx
  exact (primitive_detector_none_probability p hd c x q H (A x) hH P0 hη hpq hp2 hηM hγ hσ
    hshift (hsym x) (hbound x) (hi x) (hm x) (hpi x) (hb x) w hw hbad.le
    htune hsmall hnoise hvalidation).trans hrisk

end LongTails.Proofs.HeavyTailedSospDetectionIntegration
