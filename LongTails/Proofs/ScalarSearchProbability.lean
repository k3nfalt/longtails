import LongTails.Proofs.ScalarNoisySearch
import LongTails.Proofs.ScalarSearchMeasurable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory Classical
open scoped ENNReal

namespace OracleTemplate.ScalarSearchProbability

lemma no_hits {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    (Measure.pi fun _ : ι => P).real {ξ | ∀ i, ξ i ∉ A i} ≤
      Real.exp (-(∑ i, P.real (A i))) := by
  have he : {ξ : ι → Ω | ∀ i, ξ i ∉ A i} = Set.pi Set.univ (fun i => (A i)ᶜ) := by
    ext ξ
    simp
  rw [he, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  have hcomp (i : ι) : (P ((A i)ᶜ)).toReal = 1 - P.real (A i) := by
    exact probReal_compl_eq_one_sub (hA i)
  simp_rw [hcomp]
  calc
    _ ≤ ∏ i, Real.exp (-P.real (A i)) := Finset.prod_le_prod₀
      (fun i _ => sub_nonneg.mpr measureReal_le_one)
      (fun i _ => by have h := Real.add_one_le_exp (-P.real (A i)); linarith)
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

lemma repeated_no_hits {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (events : ι → Set Ω)
    (hm : ∀ i, MeasurableSet (events i)) (counts : ι → ℕ) (weights : ι → ℝ)
    {C mass : ℝ} (hC : 0 ≤ C)
    (hcounts : ∀ i, C * weights i ≤ counts i)
    (hmass : mass ≤ ∑ i, weights i * P.real (events i)) :
    (Measure.pi fun _ : (i : ι) × Fin (counts i) => P).real
      {ξ | ∀ k, ξ k ∉ events k.1} ≤ Real.exp (-C * mass) := by
  have h := no_hits P (fun k : (i : ι) × Fin (counts i) => events k.1) (fun k => hm k.1)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have hs : (∑ k : (i : ι) × Fin (counts i), P.real (events k.1)) =
      ∑ i, (counts i : ℝ) * P.real (events i) := by
    rw [Fintype.sum_sigma]
    simp
  rw [hs]
  have hl : C * mass ≤ ∑ i, (counts i : ℝ) * P.real (events i) := by
    calc
      C * mass ≤ C * ∑ i, weights i * P.real (events i) := mul_le_mul_of_nonneg_left hmass hC
      _ = ∑ i, (C * weights i) * P.real (events i) := by rw [Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hcounts i) (measureReal_nonneg))
  linarith

lemma probe_failure_sum (n : ℕ) :
    1024 * (1 / 2 : ℝ) ^ 16 +
      ∑ j ∈ Finset.range n, 1024 * (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (16 * (j + 1)) ≤ 1 / 16 := by
  have hterm (j : ℕ) : 1024 * (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (16 * (j + 1)) ≤
      (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ j := by
    have he : 1024 * (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (16 * (j + 1)) =
        (1024 * (1 / 2 : ℝ) ^ 16) * (2 * (1 / 2 : ℝ) ^ 16) ^ j := by
      simp only [Nat.mul_add, Nat.mul_one, pow_add, pow_mul, mul_pow]
      ring
    rw [he]
    have hp : (1 / 32768 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ j :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) j
    norm_num
    nlinarith
  have hsum (m : ℕ) : (∑ j ∈ Finset.range m,
      1024 * (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (16 * (j + 1))) ≤
      (1 / 32 : ℝ) * (1 - (1 / 2 : ℝ) ^ m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have ht := hterm m
      linarith
  have h := hsum n
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  norm_num
  linarith

lemma indicator_sum_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : ℕ) (bad : Fin N → Set Ω)
    (hm : ∀ i, MeasurableSet (bad i)) {D δ : ℝ} (hD : 0 < D)
    (hp : ∀ i, P.real (bad i) ≤ δ) :
    P.real {ω | D < ∑ i, (bad i).indicator (fun _ => (1 : ℝ)) ω} ≤ N * δ / D := by
  have hi (i : Fin N) : Integrable ((bad i).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hm i)
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have h := (hsum.div_const D).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg
      (Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => by positivity) _)) hD.le))
    (s := {ω | D < ∑ i, (bad i).indicator (fun _ => (1 : ℝ)) ω}) (by
      intro ω hω
      change D < ∑ i, (bad i).indicator (fun _ => (1 : ℝ)) ω at hω
      exact (one_le_div hD).mpr (le_of_lt hω))
  have hmean : (∫ ω, ∑ i, (bad i).indicator (fun _ => (1 : ℝ)) ω ∂P) ≤ N * δ := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    change (∑ i, ∫ ω, (bad i).indicator 1 ω ∂P) ≤ _
    simp_rw [integral_indicator_one (hm _)]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  have hb : P {ω | D < ∑ i, (bad i).indicator (fun _ => (1 : ℝ)) ω} ≤
      ENNReal.ofReal ((N : ℝ) * δ / D) := by
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    exact div_le_div_of_nonneg_right hmean hD.le
  have hδ : 0 ≤ (N : ℝ) * δ := (integral_nonneg
    (fun ω => Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => by positivity) _))).trans hmean
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal (div_nonneg hδ hD.le)] using ht

lemma bad_steps_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℝ → ℝ) (ε : ℝ) (N : ℕ) (paths : Fin N → Ω → List ScalarNoisySearch.Node)
    (replies : Fin N → Ω → Fin 3 → ℝ)
    (hm : ∀ i, MeasurableSet {ω | ¬ ScalarNoisySearch.Reliable g ε
      ((paths i ω).headD (.interval 0 0 0)) (replies i ω)}) {D δ : ℝ} (hD : 0 < D)
    (hp : ∀ i, P.real {ω | ¬ ScalarNoisySearch.Reliable g ε
      ((paths i ω).headD (.interval 0 0 0)) (replies i ω)} ≤ δ) :
    P.real {ω | D < ∑ i, (ScalarNoisySearch.badStep g ε (replies i ω) (paths i ω) : ℝ)} ≤ N * δ / D := by
  let bad : Fin N → Set Ω := fun i => {ω | ¬ ScalarNoisySearch.Reliable g ε
    ((paths i ω).headD (.interval 0 0 0)) (replies i ω)}
  have hstep (ω : Ω) (i : Fin N) :
      (ScalarNoisySearch.badStep g ε (replies i ω) (paths i ω) : ℝ) ≤
        (bad i).indicator (fun _ => (1 : ℝ)) ω := by
    cases he : paths i ω with
    | nil =>
      simp only [ScalarNoisySearch.badStep, Nat.cast_zero]
      exact Set.indicator_nonneg (fun _ _ => by norm_num) _
    | cons node rest =>
      by_cases hr : ScalarNoisySearch.Reliable g ε node (replies i ω)
      · simp [ScalarNoisySearch.badStep, bad, he, hr]
      · simp [ScalarNoisySearch.badStep, bad, he, hr]
  have ht := indicator_sum_tail P N bad hm hD hp
  apply (measureReal_mono ?_).trans ht
  intro ω hω
  exact lt_of_lt_of_le hω (Finset.sum_le_sum (fun i _ => hstep ω i))

lemma uniform_event (N : ℕ) [NeZero N] (A : Set (Fin N)) :
    (PMF.uniformOfFintype (Fin N)).toMeasure.real A =
      (Fintype.card A : ℝ) / N := by
  rw [measureReal_def, PMF.toMeasure_uniformOfFintype_apply A (Set.to_countable A).measurableSet,
    ENNReal.toReal_div]
  simp

lemma uniform_bad_le {N m : ℕ} [NeZero N] (good : Fin N → Prop) [DecidablePred good]
    (hm : m ≤ (Finset.univ.filter good).card) :
    (PMF.uniformOfFintype (Fin N)).toMeasure.real {i | ¬ good i} ≤ 1 - (m : ℝ) / N := by
  rw [uniform_event]
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (p := good)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hc : Fintype.card {i : Fin N | ¬ good i} = (Finset.univ.filter (fun i => ¬ good i)).card := by
    simp
  simp only [Fintype.card_subtype] at hc ⊢
  rw [hc]
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  apply (div_le_iff₀ hN).mpr
  have hr : ((Finset.univ.filter (fun i => ¬ good i)).card : ℝ) + m ≤ N := by
    exact_mod_cast (show (Finset.univ.filter (fun i => ¬ good i)).card + m ≤ N by omega)
  field_simp
  nlinarith

lemma acceptableStep_le_accuracy (g : ℝ → ℝ) (ε fallback : ℝ)
    (path : List ScalarNoisySearch.Node) :
    ScalarNoisySearch.acceptableStep g ε path ≤
      if |g (ScalarNoisySearch.recordedPoint fallback path)| ≤ 17 * ε / 32 then 1 else 0 := by
  cases path with
  | nil => simp [ScalarNoisySearch.acceptableStep]
  | cons node rest =>
    cases node <;> simp [ScalarNoisySearch.acceptableStep, ScalarNoisySearch.acceptable,
      ScalarNoisySearch.recordedPoint]; exact le_rfl

lemma occupation_uniform {N m : ℕ} [NeZero N] (g : ℝ → ℝ) (ε fallback : ℝ)
    (paths : ℕ → List ScalarNoisySearch.Node)
    (hm : m ≤ ∑ t ∈ Finset.range N, ScalarNoisySearch.acceptableStep g ε (paths t)) :
    (PMF.uniformOfFintype (Fin N)).toMeasure.real
      {i | 17 * ε / 32 < |g (ScalarNoisySearch.recordedPoint fallback (paths i))|} ≤
      1 - (m : ℝ) / N := by
  let good : Fin N → Prop := fun i => |g (ScalarNoisySearch.recordedPoint fallback (paths i))| ≤ 17 * ε / 32
  have hsum : m ≤ ∑ i : Fin N, if good i then (1 : ℕ) else 0 := by
    rw [← Fin.sum_univ_eq_sum_range] at hm
    exact hm.trans (Finset.sum_le_sum (fun i _ => acceptableStep_le_accuracy g ε fallback (paths i)))
  have hc : m ≤ (Finset.univ.filter good).card := by simpa using hsum
  have h := uniform_bad_le good hc
  simpa only [good, not_le] using h

lemma uniform_occupation_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N m : ℕ} [NeZero N] (hmN : m ≤ N) (g : ℝ → ℝ) (hg : Measurable g) (ε fallback : ℝ)
    (paths : Ω → ℕ → List ScalarNoisySearch.Node) (hpaths : ∀ t, Measurable (fun ω => paths ω t))
    (A : Set Ω) (hA : MeasurableSet A) {α : ℝ} (hPA : P.real A ≤ α)
    (hm : ∀ ω ∉ A, m ≤ ∑ t ∈ Finset.range N, ScalarNoisySearch.acceptableStep g ε (paths ω t)) :
    (P.prod (PMF.uniformOfFintype (Fin N)).toMeasure).real
      {w | 17 * ε / 32 < |g (ScalarNoisySearch.recordedPoint fallback (paths w.1 w.2))|} ≤
      α + (1 - (m : ℝ) / N) := by
  have houtput : Measurable (fun w : Ω × Fin N => ScalarNoisySearch.recordedPoint fallback (paths w.1 w.2)) := by
    apply ScalarNoisySearch.measurable_nat_selection _ (fun w => w.2.val) (by fun_prop)
      (fun t w => ScalarNoisySearch.recordedPoint fallback (paths w.1 t))
    · intro t
      exact (ScalarNoisySearch.measurable_recordedPoint fallback).comp ((hpaths t).comp measurable_fst)
    · intro w
      rfl
  have hB := measurableSet_lt (measurable_const (a := 17 * ε / 32))
    (continuous_abs.measurable.comp (hg.comp houtput))
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hδ : 0 ≤ 1 - (m : ℝ) / N := by
    apply sub_nonneg.mpr
    apply (div_le_one hN).mpr
    exact_mod_cast hmN
  have hpoint (ω : Ω) (hω : ω ∉ A) := occupation_uniform (N := N) g ε fallback (paths ω) (hm ω hω)
  have h := ScalarHeavyTailEstimator.conditional_failure hA hB hδ hPA hpoint
  simpa only [Function.comp_def] using h

lemma walk_point_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {oracle : ℝ → Ω → ℝ} {μ : ℝ → ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hμ : Measurable μ)
    {σ p ε x0 s : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) (hp2 : p ≤ 2)
    (hs : |s| = 1) (hi : ∀ x, Integrable (oracle x) P)
    (hm : ∀ x, (∫ ω, oracle x ω ∂P) = μ x)
    (hpi : ∀ x, Integrable (fun ω => |oracle x ω - μ x| ^ p) P)
    (hmoment : ∀ x, (∫ ω, |oracle x ω - μ x| ^ p ∂P) ≤ σ ^ p)
    (D call t : ℕ) (path : List ScalarNoisySearch.Node) (i : Fin 3) :
    (Measure.infinitePi fun _ : ℕ => P).real {ξ |
      let replies := ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call
      let state := ScalarNoisySearch.trace ε D (2 * D) replies path t
      ε / 32 < |replies t state i - s * μ (x0 + s * ScalarNoisySearch.queries
        (state.headD (.interval 0 0 0)) i)|} ≤ 1 / 4096 := by
  let c := ScalarHeavyTailEstimator.calls σ p (ε / 96) 6
  let cut := call + 3 * c * t + c * i.val
  let query : (Fin cut → Ω) → ℝ := fun ξ => x0 + s * ScalarNoisySearch.queries
    ((ScalarNoisySearch.trace ε D (2 * D)
      (ScalarSearchExecution.walkReplies
        (fun j x => if h : j < cut then oracle x (ξ ⟨j, h⟩) else 0)
        σ p ε x0 s call) path t).headD (.interval 0 0 0)) i
  have hq : Measurable query := ScalarNoisySearch.measurable_prefix_query ho σ p ε x0 s D call t cut path i
  have ht := ScalarHeavyTailEstimator.past_estimate_tail (P := P) cut ho hμ query hq
    hσ (by positivity : 0 < ε / 96) hp hp2 hi hm hpi hmoment 6
  have he (ξ : ℕ → Ω) :
      ScalarNoisySearch.trace ε D (2 * D)
        (ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call) path t =
      ScalarNoisySearch.trace ε D (2 * D)
        (ScalarSearchExecution.walkReplies
          (fun j x => if h : j < cut then oracle x (ξ j) else 0) σ p ε x0 s call) path t := by
    apply ScalarSearchExecution.walk_trace_reads
    intro j hj hj' x
    have hjcut : j < cut := by dsimp [cut, c]; omega
    simp only [hjcut, dite_true]
  have heq : 3 * (ε / 96) = ε / 32 := by ring
  rw [heq] at ht
  norm_num at ht
  convert ht using 2
  ext ξ
  simp only [Set.mem_ofPred_eq]
  simp only [ScalarSearchExecution.walkReplies, ScalarSearchExecution.triplePlan_evalOracle_apply]
  rw [← mul_sub, abs_mul, hs, one_mul]
  rw [he]

lemma walk_step_failure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {oracle : ℝ → Ω → ℝ} {μ : ℝ → ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hμ : Measurable μ)
    {σ p ε x0 s : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) (hp2 : p ≤ 2)
    (hs : |s| = 1) (hi : ∀ x, Integrable (oracle x) P)
    (hm : ∀ x, (∫ ω, oracle x ω ∂P) = μ x)
    (hpi : ∀ x, Integrable (fun ω => |oracle x ω - μ x| ^ p) P)
    (hmoment : ∀ x, (∫ ω, |oracle x ω - μ x| ^ p ∂P) ≤ σ ^ p)
    (D call t : ℕ) (path : List ScalarNoisySearch.Node) :
    (Measure.infinitePi fun _ : ℕ => P).real {ξ |
      let replies := ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call
      let state := ScalarNoisySearch.trace ε D (2 * D) replies path t
      ¬ ScalarNoisySearch.Reliable (fun x => s * μ (x0 + s * x)) ε
        (state.headD (.interval 0 0 0)) (replies t state)} ≤ 3 / 4096 := by
  let bad : Fin 3 → Set (ℕ → Ω) := fun i => {ξ |
    let replies := ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call
    let state := ScalarNoisySearch.trace ε D (2 * D) replies path t
    ε / 32 < |replies t state i - s * μ (x0 + s * ScalarNoisySearch.queries
      (state.headD (.interval 0 0 0)) i)|}
  have he : {ξ : ℕ → Ω |
      let replies := ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call
      let state := ScalarNoisySearch.trace ε D (2 * D) replies path t
      ¬ ScalarNoisySearch.Reliable (fun x => s * μ (x0 + s * x)) ε
        (state.headD (.interval 0 0 0)) (replies t state)} = ⋃ i, bad i := by
    ext ξ
    simp only [ScalarNoisySearch.Reliable, Set.mem_ofPred_eq, Set.mem_iUnion, not_forall, not_le, bad]
  rw [he]
  apply (measureReal_iUnion_fintype_le bad).trans
  have ht : ∑ i : Fin 3, (Measure.infinitePi fun _ : ℕ => P).real (bad i) ≤
      ∑ _ : Fin 3, (1 / 4096 : ℝ) := Finset.sum_le_sum (fun i _ =>
    walk_point_tail P ho hμ hσ hε hp hp2 hs hi hm hpi hmoment D call t path i)
  norm_num at ht ⊢
  exact ht

lemma walk_bad_steps {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {oracle : ℝ → Ω → ℝ} {μ : ℝ → ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hμ : Measurable μ)
    {σ p ε x0 s : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) (hp2 : p ≤ 2)
    (hs : |s| = 1) (hi : ∀ x, Integrable (oracle x) P)
    (hm : ∀ x, (∫ ω, oracle x ω ∂P) = μ x)
    (hpi : ∀ x, Integrable (fun ω => |oracle x ω - μ x| ^ p) P)
    (hmoment : ∀ x, (∫ ω, |oracle x ω - μ x| ^ p ∂P) ≤ σ ^ p)
    (D call : ℕ) (hD : 0 < D) (path : List ScalarNoisySearch.Node) :
    (Measure.infinitePi fun _ : ℕ => P).real {ξ |
      let replies := ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call
      (D : ℝ) < ∑ t : Fin (16 * D),
        (ScalarNoisySearch.badStep (fun x => s * μ (x0 + s * x)) ε
          (replies t (ScalarNoisySearch.trace ε D (2 * D) replies path t))
          (ScalarNoisySearch.trace ε D (2 * D) replies path t) : ℝ)} ≤ 1 / 16 := by
  let states : Fin (16 * D) → (ℕ → Ω) → List ScalarNoisySearch.Node := fun t ξ =>
    ScalarNoisySearch.trace ε D (2 * D)
      (ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call) path t
  let replies : Fin (16 * D) → (ℕ → Ω) → Fin 3 → ℝ := fun t ξ =>
    ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call t (states t ξ)
  let g : ℝ → ℝ := fun x => s * μ (x0 + s * x)
  have hA (t : Fin (16 * D)) : MeasurableSet {ξ | ¬ ScalarNoisySearch.Reliable g ε
      ((states t ξ).headD (.interval 0 0 0)) (replies t ξ)} := by
    have he : {ξ | ¬ ScalarNoisySearch.Reliable g ε
        ((states t ξ).headD (.interval 0 0 0)) (replies t ξ)} =
        ⋃ i : Fin 3, {ξ | ε / 32 < |replies t ξ i - g (ScalarNoisySearch.queries
          ((states t ξ).headD (.interval 0 0 0)) i)|} := by
      ext ξ
      simp [ScalarNoisySearch.Reliable]
    rw [he]
    apply MeasurableSet.iUnion
    intro i
    exact measurableSet_lt measurable_const (continuous_abs.measurable.comp
      (ScalarNoisySearch.measurable_walk_error ho hμ σ p ε x0 s D call t path i))
  have hDr : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have ht := bad_steps_tail (Measure.infinitePi fun _ : ℕ => P) g ε (16 * D) states replies hA hDr
    (fun t => walk_step_failure P ho hμ hσ hε hp hp2 hs hi hm hpi hmoment D call t path)
  have he : ((16 * D : ℕ) : ℝ) * (3 / 4096 : ℝ) / D = 3 / 256 := by
    push_cast
    field_simp
    norm_num
  rw [he] at ht
  exact ht.trans (by norm_num)

lemma root_validation_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {oracle : ℝ → Ω → ℝ} {μ : ℝ → ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hμ : Measurable μ)
    {σ p ε x0 s : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (oracle x) P)
    (hm : ∀ x, (∫ ω, oracle x ω ∂P) = μ x)
    (hpi : ∀ x, Integrable (fun ω => |oracle x ω - μ x| ^ p) P)
    (hmoment : ∀ x, (∫ ω, |oracle x ω - μ x| ^ p ∂P) ≤ σ ^ p)
    (D call : ℕ) [NeZero (16 * D)] (endpoint : ℝ) :
    ((PMF.uniformOfFintype (Fin (16 * D))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => P)).real {w |
      let pair := ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
        (ScalarSearchPlans.rootAttemptPlan σ p ε x0 s endpoint D w.1.val) call
      ε / 16 < |pair.2 - μ pair.1|} ≤ 1 / 4096 := by
  let c := ScalarHeavyTailEstimator.calls σ p (ε / 96) 6
  let cut := call + 3 * c * (16 * D)
  let query : Fin (16 * D) × (Fin cut → Ω) → ℝ := fun w => x0 + s *
    ScalarNoisySearch.recordedPoint 0 (ScalarNoisySearch.trace ε D (2 * D)
      (ScalarSearchExecution.walkReplies
        (fun j x => if h : j < cut then oracle x (w.2 ⟨j, h⟩) else 0)
        σ p ε x0 s call) [.interval 0 endpoint 0] w.1.val)
  have hrecord : Measurable (fun w : Fin (16 * D) × (Fin cut → Ω) =>
      ScalarNoisySearch.recordedPoint 0 (ScalarNoisySearch.trace ε D (2 * D)
        (ScalarSearchExecution.walkReplies
          (fun j x => if h : j < cut then oracle x (w.2 ⟨j, h⟩) else 0)
          σ p ε x0 s call) [.interval 0 endpoint 0] w.1.val)) := by
    apply ScalarNoisySearch.measurable_nat_selection _ (fun w => w.1.val) (by fun_prop)
      (fun t w => ScalarNoisySearch.recordedPoint 0 (ScalarNoisySearch.trace ε D (2 * D)
        (ScalarSearchExecution.walkReplies
          (fun j x => if h : j < cut then oracle x (w.2 ⟨j, h⟩) else 0)
          σ p ε x0 s call) [.interval 0 endpoint 0] t))
    · intro t
      exact (ScalarNoisySearch.measurable_recordedPoint 0).comp
        ((ScalarNoisySearch.measurable_prefix_trace ho σ p ε x0 s D call t cut
          [.interval 0 endpoint 0]).comp measurable_snd)
    · intro w
      rfl
  have hq : Measurable query := measurable_const.add (measurable_const.mul hrecord)
  have ht := ScalarHeavyTailEstimator.prefix_adaptive_estimate_tail (P := P)
    (PMF.uniformOfFintype (Fin (16 * D))).toMeasure cut ho hμ query hq
    hσ (by positivity : 0 < ε / 48) hp hp2 hi hm hpi hmoment 6
  have he (ξ : ℕ → Ω) (time : Fin (16 * D)) :
      ScalarNoisySearch.trace ε D (2 * D)
        (ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call)
        [.interval 0 endpoint 0] time.val =
      ScalarNoisySearch.trace ε D (2 * D)
        (ScalarSearchExecution.walkReplies
          (fun j x => if h : j < cut then oracle x (ξ j) else 0) σ p ε x0 s call)
        [.interval 0 endpoint 0] time.val := by
    apply ScalarSearchExecution.walk_trace_reads
    intro j hj hj' x
    have htime := Nat.mul_le_mul_left (3 * c) time.isLt.le
    have hjcut : j < cut := by dsimp [cut, c] at *; omega
    simp only [hjcut, dite_true]
  have heq : 3 * (ε / 48) = ε / 16 := by ring
  rw [heq] at ht
  norm_num at ht
  convert ht using 2
  ext w
  simp only [Set.mem_ofPred_eq, ScalarSearchExecution.rootAttemptPlan_evalOracle]
  rw [he]

lemma root_false_accept_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {oracle : ℝ → Ω → ℝ} {μ : ℝ → ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hμ : Measurable μ)
    {σ p ε x0 s : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (oracle x) P)
    (hm : ∀ x, (∫ ω, oracle x ω ∂P) = μ x)
    (hpi : ∀ x, Integrable (fun ω => |oracle x ω - μ x| ^ p) P)
    (hmoment : ∀ x, (∫ ω, |oracle x ω - μ x| ^ p ∂P) ≤ σ ^ p)
    (D call : ℕ) [NeZero (16 * D)] (endpoint : ℝ) :
    ((PMF.uniformOfFintype (Fin (16 * D))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => P)).real {w |
      let pair := ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
        (ScalarSearchPlans.rootAttemptPlan σ p ε x0 s endpoint D w.1.val) call
      |pair.2| ≤ 3 * ε / 4 ∧ ε < |μ pair.1|} ≤ 1 / 4096 := by
  apply (measureReal_mono _).trans (root_validation_tail P ho hμ (x0 := x0) (s := s) hσ hε hp hp2 hi hm hpi hmoment D call endpoint)
  intro w hw
  dsimp only at hw ⊢
  by_contra hn
  simp only [Set.mem_ofPred_eq] at hn
  have he := le_of_not_gt hn
  have ht := abs_sub_le (μ (ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
    (ScalarSearchPlans.rootAttemptPlan σ p ε x0 s endpoint D w.1.val) call).1)
    (ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
      (ScalarSearchPlans.rootAttemptPlan σ p ε x0 s endpoint D w.1.val) call).2 0
  simp only [sub_zero] at ht
  rw [abs_sub_comm] at he
  linarith [hw.1, hw.2]

lemma independent_trials_tail {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Z) [IsProbabilityMeasure Q]
    (b n offset call : ℕ) (hb : 0 < b) (E : Set (Z × (ℕ → Ω))) (hE : MeasurableSet E)
    (hreads : ∀ z (a c : ℕ → Ω), (∀ j < b, a j = c j) → ((z, a) ∈ E ↔ (z, c) ∈ E))
    {δ : ℝ}
    (htail : (Q.prod (Measure.infinitePi fun _ : ℕ => P)).real E ≤ δ) :
    ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | ∀ i : Fin n, (w.1 (offset + i.val), fun j => w.2 (call + i.val * b + j)) ∈ E} ≤ δ ^ n := by
  let extend : (Fin b → Ω) → ℕ → Ω := fun ξ j => if h : j < b then ξ ⟨j, h⟩ else ξ ⟨0, hb⟩
  have hmext : Measurable extend := by
    apply measurable_pi_iff.mpr
    intro j
    dsimp [extend]
    split_ifs <;> exact measurable_pi_apply _
  let B : Set (Z × (Fin b → Ω)) := {w | (w.1, extend w.2) ∈ E}
  have hB : MeasurableSet B := hE.preimage (measurable_fst.prodMk (hmext.comp measurable_snd))
  have he (z : Z) (ξ : ℕ → Ω) : (z, extend (fun j => ξ j)) ∈ E ↔ (z, ξ) ∈ E := by
    apply hreads
    intro j hj
    simp only [extend, hj, dite_true]
  have hpre := ((MeasurePreserving.id Q).prod
    (StochasticGeneralized.prefix_preserving P b)).measure_preimage hB.nullMeasurableSet
  have hPB : (Q.prod (Measure.pi fun _ : Fin b => P)).real B ≤ δ := by
    unfold Measure.real
    rw [← hpre]
    change (Q.prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | (w.1, extend (fun j => w.2 j)) ∈ E} ≤ δ
    simpa [he] using htail
  let A : Set (Fin n → Z × (Fin b → Ω)) := {w | ∀ i, w i ∈ B}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => hB.preimage (measurable_pi_apply i))
  have hPA : (Measure.pi fun _ : Fin n => Q.prod (Measure.pi fun _ : Fin b => P)).real A ≤ δ ^ n := by
    have heq : A = Set.pi Set.univ (fun _ => B) := by ext w; simp [A]
    rw [heq, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, measureReal_def] using
      Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin n)))
      (fun _ _ => measureReal_nonneg (μ := Q.prod (Measure.pi fun _ : Fin b => P)) (s := B))
      (fun _ _ => hPB)
  have hp := (ScalarHeavyTailEstimator.paired_blocks_preserving (P := P) Q b n offset call).measure_preimage
    hA.nullMeasurableSet
  unfold Measure.real at hPA ⊢
  rw [← hp] at hPA
  have heq : {w : (ℕ → Z) × (ℕ → Ω) | ∀ i : Fin n,
      (w.1 (offset + i.val), fun j => w.2 (call + i.val * b + j)) ∈ E} =
      (fun w : (ℕ → Z) × (ℕ → Ω) => fun i : Fin n =>
        (w.1 (offset + i.val), fun j : Fin b => w.2 (call + i.val * b + j.val))) ⁻¹' A := by
    ext w
    simp only [A, B, Set.mem_preimage, Set.mem_ofPred_eq]
    apply forall_congr'
    intro i
    exact (he (w.1 (offset + i.val)) (fun j => w.2 (call + i.val * b + j))).symm
  rw [heq]
  exact hPA

lemma indexed_samples_preserving {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (index : ι → ℕ) (hinj : Function.Injective index) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun i => ξ (index i))
      (Measure.infinitePi fun _ : ℕ => P) (Measure.pi fun _ : ι => P) := by
  have h := StochasticGeneralized.infinitePi_iid P
  refine ⟨measurable_pi_iff.mpr (fun i => measurable_pi_apply _), ?_⟩
  have hind := h.independent.precomp hinj
  have hlaw := hind.map_fun_eq_pi_map (fun i => (measurable_pi_apply (index i)).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using hlaw

lemma prefix_block_index_injective (counts : ℕ → ℕ) (n : ℕ) :
    Function.Injective (fun v : (i : Fin n) × Fin (counts i.val) =>
      (∑ k ∈ Finset.range v.1.val, counts k) + v.2.val) := by
  have hlt (i j a b : ℕ) (hij : i < j) (ha : a < counts i) :
      (∑ k ∈ Finset.range i, counts k) + a < (∑ k ∈ Finset.range j, counts k) + b := by
    calc
      _ < (∑ k ∈ Finset.range i, counts k) + counts i := Nat.add_lt_add_left ha _
      _ = ∑ k ∈ Finset.range (i + 1), counts k := (Finset.sum_range_succ counts i).symm
      _ ≤ ∑ k ∈ Finset.range j, counts k := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
      _ ≤ _ := Nat.le_add_right _ _
  intro a b hab
  dsimp only at hab
  have hi : a.1 = b.1 := by
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt' | hgt'
    · have h := hlt a.1.val b.1.val a.2.val b.2.val hlt' a.2.isLt
      omega
    · have h := hlt b.1.val a.1.val b.2.val a.2.val hgt' b.2.isLt
      omega
  cases a with
  | mk i a =>
    cases b with
    | mk j b =>
      dsimp only at hi hab
      subst j
      have hab' : a = b := Fin.ext (Nat.add_left_cancel hab)
      subst b
      rfl

lemma reverse_block_index_injective (counts : ℕ → ℕ) (n : ℕ) :
    Function.Injective (fun v : (i : Fin n) × Fin (counts i.val) =>
      (∑ k ∈ Finset.Ico (v.1.val + 1) n, counts k) + v.2.val) := by
  have hlt (i j a b : ℕ) (hij : i < j) (hjn : j < n) (hb : b < counts j) :
      (∑ k ∈ Finset.Ico (j + 1) n, counts k) + b <
        (∑ k ∈ Finset.Ico (i + 1) n, counts k) + a := by
    calc
      _ < counts j + ∑ k ∈ Finset.Ico (j + 1) n, counts k := by omega
      _ = ∑ k ∈ Finset.Ico j n, counts k := (Finset.sum_eq_sum_Ico_succ_bot hjn counts).symm
      _ ≤ ∑ k ∈ Finset.Ico (i + 1) n, counts k := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega) (fun _ _ _ => Nat.zero_le _)
      _ ≤ _ := Nat.le_add_right _ _
  intro a b hab
  dsimp only at hab
  have hi : a.1 = b.1 := by
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt' | hgt'
    · have h := hlt a.1.val b.1.val a.2.val b.2.val hlt' b.1.isLt b.2.isLt
      omega
    · have h := hlt b.1.val a.1.val b.2.val a.2.val hgt' a.1.isLt a.2.isLt
      omega
  cases a with
  | mk i a =>
    cases b with
    | mk j b =>
      dsimp only at hi hab
      subst j
      have hab' : a = b := Fin.ext (Nat.add_left_cancel hab)
      subst b
      rfl

end OracleTemplate.ScalarSearchProbability
