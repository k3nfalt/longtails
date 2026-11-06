import LongTails.Proofs.StochasticEqualitySampling
import LongTails.Proofs.StochasticEqualityMoments

namespace LongTails.Proofs.StochasticEqualityProcess

open MeasureTheory OracleTemplate
open LongTails.Algorithms.StochasticEquality
open LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Setups.StochasticRegularEqualities
open LongTails.Proofs.StochasticEqualityExecution
open LongTails.Proofs.StochasticEqualitySampling
open LongTails.Proofs.StochasticEqualityMoments

def active {X : Type*} (p : Public) (cfg : Config)
    (truth : Point p.d → Reply p) (path : ℕ → X → Point p.d) (good : X → Prop) : ℕ → X → Prop
  | 0, z => good z ∧ ‖(truth (path 0 z)).1‖ ≤ cfg.gradientCap ∧
      ‖(truth (path 0 z)).2.1‖ ≤ cfg.constraintCap
  | n + 1, z => active p cfg truth path good n z ∧
      ‖(truth (path (n + 1) z)).1‖ ≤ cfg.gradientCap ∧
      ‖(truth (path (n + 1) z)).2.1‖ ≤ cfg.constraintCap

lemma active_caps {X : Type*} (p : Public) (cfg : Config)
    (truth : Point p.d → Reply p) (path : ℕ → X → Point p.d) (good : X → Prop)
    (n : ℕ) (z : X) (h : active p cfg truth path good n z) :
    ‖(truth (path n z)).1‖ ≤ cfg.gradientCap ∧
      ‖(truth (path n z)).2.1‖ ≤ cfg.constraintCap := by
  cases n <;> exact h.2

lemma active_mono {X : Type*} (p : Public) (cfg : Config)
    (truth : Point p.d → Reply p) (path : ℕ → X → Point p.d) (good : X → Prop)
    {n k : ℕ} (hkn : k ≤ n) (z : X) (h : active p cfg truth path good n z) :
    active p cfg truth path good k z := by
  induction n with
  | zero => simpa only [Nat.eq_zero_of_le_zero hkn] using h
  | succ n ih =>
    rcases eq_or_lt_of_le hkn with he | he
    · simpa only [he] using h
    · exact ih (by omega) h.1

lemma active_good {X : Type*} (p : Public) (cfg : Config)
    (truth : Point p.d → Reply p) (path : ℕ → X → Point p.d) (good : X → Prop)
    (n : ℕ) (z : X) (h : active p cfg truth path good n z) : good z :=
  (active_mono p cfg truth path good (Nat.zero_le n) z h).1

lemma measurableSet_active {X : Type*} [MeasurableSpace X] (p : Public) (cfg : Config)
    (truth : Point p.d → Reply p) (ht : Measurable truth)
    (path : ℕ → X → Point p.d) (hp : ∀ n, Measurable (path n))
    (good : X → Prop) (hg : MeasurableSet {z | good z}) (n : ℕ) :
    MeasurableSet {z | active p cfg truth path good n z} := by
  have hc (k : ℕ) : MeasurableSet {z | ‖(truth (path k z)).1‖ ≤ cfg.gradientCap ∧
      ‖(truth (path k z)).2.1‖ ≤ cfg.constraintCap} :=
    (measurableSet_le (ht.comp (hp k)).fst.norm measurable_const).inter
      (measurableSet_le (ht.comp (hp k)).snd.fst.norm measurable_const)
  induction n with
  | zero => exact hg.inter (hc 0)
  | succ n ih => exact ih.inter (hc (n + 1))

lemma batch_offset_succ (cfg : Config) (offset n : ℕ) :
    batchOffset cfg offset (n + 1) = batchOffset cfg offset n + batchSize cfg n := by
  simp [batchOffset, Finset.sum_range_succ, Nat.add_assoc]

lemma batch_offset_mono (cfg : Config) (offset : ℕ) : Monotone (batchOffset cfg offset) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [batch_offset_succ]
  exact Nat.le_add_right _ _

lemma trace_zero {Ω : Type*} (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x : Point p.d) (offset : ℕ) :
    trainingTrace p cfg g ξ x offset 0 = ⟨x, x, 0, x⟩ := rfl

lemma trace_succ {Ω : Type*} (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x : Point p.d) (offset n : ℕ) :
    trainingTrace p cfg g ξ x offset (n + 1) =
      trainingUpdate p cfg n 0 (trainingTrace p cfg g ξ x offset n)
        (QueryPlan.sampledEval g (fun i => ξ (i / 2))
          (estimatorPlan p cfg n (trainingTrace p cfg g ξ x offset n))
          (2 * batchOffset cfg offset n)) := by
  have hc : 2 * offset + slotCalls (fun k => 2 * batchSize cfg k) n 0 =
      2 * batchOffset cfg offset n := by
    rw [slot_calls_even]
    simp only [Nat.zero_add, batchOffset]
    ring
  rw [trainingTrace, trainingPrefixPlan, sampled_slot_succ_end]
  have he := congrArg (fun k => QueryPlan.sampledEval g (fun i => ξ (i / 2))
    ((estimatorPlan p cfg k (trainingTrace p cfg g ξ x offset n)).map
      (trainingUpdate p cfg k 0 (trainingTrace p cfg g ξ x offset n)))
    (2 * offset + slotCalls (fun k => 2 * batchSize cfg k) n 0)) (Nat.zero_add n)
  exact he.trans (by rw [QueryPlan.sampledEval_map, hc])

lemma trace_previous {Ω : Type*} (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x : Point p.d) (offset n : ℕ) :
    (trainingTrace p cfg g ξ x offset (n + 1)).previous =
      (trainingTrace p cfg g ξ x offset n).point := by
  rw [trace_succ]
  rfl

lemma trace_movement {Ω : Type*} (p : Public) (cfg : Config)
    (hν : 0 < p.ν) (hL : 0 ≤ p.Lc) (hG : 0 ≤ cfg.gradientCap)
    (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (x : Point p.d) (offset n : ℕ) :
    ‖(trainingTrace p cfg g ξ x offset n).point -
      (trainingTrace p cfg g ξ x offset n).previous‖ ≤
      cfg.step * (cfg.gradientCap + p.Lc * cfg.constraintCap) := by
  cases n with
  | zero => simp only [trace_zero, sub_self, norm_zero]; positivity
  | succ n =>
    rw [trace_previous, trace_succ]
    exact training_displacement p cfg hν hL hG hM hη n 0 _ _

lemma trace_prefix_congr {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ ζ : ℕ → Ω) (x : Point p.d) (offset n : ℕ)
    (h : ∀ i, i < batchOffset cfg offset n → ξ i = ζ i) :
    trainingTrace p cfg g ξ x offset n = trainingTrace p cfg g ζ x offset n := by
  simp only [trainingTrace, StochasticQuasar.sampled_eval_eq_indexed]
  apply StochasticEnvelopeExecution.evalAt_prefix_congr
  intro j hj y
  have hc := slot_calls_even (batchSize cfg) n 0
  simp only [Nat.zero_add] at hc
  congr 1
  apply h
  change j < slotCalls (fun k => 2 * batchSize cfg k) n 0 at hj
  unfold batchOffset
  omega

lemma trace_random_start_prefix_congr {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (x : (ℕ → Ω) → Point p.d) (offset n : ℕ)
    (hx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (ξ ζ : ℕ → Ω) (h : ∀ i, i < batchOffset cfg offset n → ξ i = ζ i) :
    trainingTrace p cfg g ξ (x ξ) offset n = trainingTrace p cfg g ζ (x ζ) offset n := by
  have hoff : offset ≤ batchOffset cfg offset n := Nat.le_add_right _ _
  rw [hx ξ ζ (fun i hi => h i (lt_of_lt_of_le hi hoff))]
  exact trace_prefix_congr p cfg g ξ ζ (x ζ) offset n h

lemma active_prefix_congr {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset : ℕ)
    (hx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hg : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (n : ℕ) (ξ ζ : ℕ → Ω) (h : ∀ i, i < batchOffset cfg offset n → ξ i = ζ i) :
    active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ ↔
      active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ζ := by
  have hp (k : ℕ) (hk : k ≤ n) :
      trainingTrace p cfg g ξ (x ξ) offset k = trainingTrace p cfg g ζ (x ζ) offset k :=
    trace_random_start_prefix_congr p cfg g x offset k hx ξ ζ
      (fun i hi => h i (lt_of_lt_of_le hi (batch_offset_mono cfg offset hk)))
  have hg' := hg ξ ζ (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_add_right _ _)))
  have hc : ∀ k ≤ n,
      active p cfg truth (fun j z => (trainingTrace p cfg g z (x z) offset j).point) good k ξ ↔
        active p cfg truth (fun j z => (trainingTrace p cfg g z (x z) offset j).point) good k ζ := by
    intro k hk
    induction k with
    | zero => simp only [active, hp 0 hk, hg']
    | succ k ih => simp only [active, hp (k + 1) hk, ih (by omega)]
  exact hc n le_rfl

lemma trace_estimate {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (x : Point p.d) (offset n : ℕ) :
    (trainingTrace p cfg g ξ x offset (n + 1)).estimate =
      clipReply p cfg.gradientCap cfg.constraintCap
        (if n % cfg.epoch = 0 then
          (cfg.resetBatch : ℝ)⁻¹ • ∑ i : Fin cfg.resetBatch,
            g (trainingTrace p cfg g ξ x offset n).point (ξ (batchOffset cfg offset n + i.val))
        else (trainingTrace p cfg g ξ x offset n).estimate +
          (cfg.incrementBatch : ℝ)⁻¹ • ∑ i : Fin cfg.incrementBatch,
            (g (trainingTrace p cfg g ξ x offset n).point (ξ (batchOffset cfg offset n + i.val)) -
             g (trainingTrace p cfg g ξ x offset n).previous (ξ (batchOffset cfg offset n + i.val)))) := by
  rw [trace_succ]
  change clipReply p cfg.gradientCap cfg.constraintCap _ = _
  rw [sampled_estimator]

lemma estimator_increment_centered {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p) (ξ : ℕ → Ω)
    (k offset : ℕ) (s : TrainingState p) (hk : k % cfg.epoch ≠ 0) :
    pack p (QueryPlan.sampledEval g (fun i => ξ (i / 2)) (estimatorPlan p cfg k s) (2 * offset)) -
      pack p (truth s.point) = (pack p s.estimate - pack p (truth s.previous)) +
      (cfg.incrementBatch : ℝ)⁻¹ • ∑ i ∈ Finset.range cfg.incrementBatch,
        ((pack p (g s.point (ξ (offset + i))) - pack p (truth s.point)) -
          (pack p (g s.previous (ξ (offset + i))) - pack p (truth s.previous))) := by
  rw [sampled_estimator, ite_eq_right hk]
  rw [pack_increment_centered p cfg.incrementBatch cfg.incrementBatch.pos _ _
    s.estimate (truth s.point) (truth s.previous)]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    (pack p (g s.point (ξ (offset + i))) - pack p (truth s.point)) -
      (pack p (g s.previous (ξ (offset + i))) - pack p (truth s.previous))) ]

lemma estimator_reset_centered {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p) (ξ : ℕ → Ω)
    (k offset : ℕ) (s : TrainingState p) (hk : k % cfg.epoch = 0) :
    pack p (QueryPlan.sampledEval g (fun i => ξ (i / 2)) (estimatorPlan p cfg k s) (2 * offset)) -
      pack p (truth s.point) =
      (cfg.resetBatch : ℝ)⁻¹ • ∑ i ∈ Finset.range cfg.resetBatch,
        (pack p (g s.point (ξ (offset + i))) - pack p (truth s.point)) := by
  rw [sampled_estimator, ite_eq_left hk]
  rw [pack_reset_centered p cfg.resetBatch cfg.resetBatch.pos]
  rw [Fin.sum_univ_eq_sum_range (fun i => pack p (g s.point (ξ (offset + i))) - pack p (truth s.point))]

lemma trace_estimate_caps {Ω : Type*} (p : Public) (cfg : Config)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (x : Point p.d) (offset n : ℕ) :
    ‖(trainingTrace p cfg g ξ x offset n).estimate.1‖ ≤ cfg.gradientCap ∧
    ‖(trainingTrace p cfg g ξ x offset n).estimate.2.1‖ ≤ cfg.constraintCap ∧
    ‖(trainingTrace p cfg g ξ x offset n).estimate.2.2‖ ≤ p.Lc := by
  cases n with
  | zero => simpa [trace_zero] using And.intro hG (And.intro hM hL)
  | succ n =>
    rw [trace_succ]
    exact ⟨norm_clip_le hG _, norm_clip_le hM _, norm_clip_le hL _⟩

lemma active_previous_caps {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω)
    (ha : active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ) :
    ‖(truth (trainingTrace p cfg g ξ (x ξ) offset n).previous).1‖ ≤ cfg.gradientCap ∧
    ‖(truth (trainingTrace p cfg g ξ (x ξ) offset n).previous).2.1‖ ≤ cfg.constraintCap := by
  cases n with
  | zero =>
    have h := active_caps p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good 0 ξ ha
    exact h
  | succ n =>
    rw [trace_previous]
    exact active_caps p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ
      (active_mono p cfg truth
        (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good (Nat.le_succ n) ξ ha)

lemma active_prior_error_bound {Ω : Type*} (p : Public) (cfg : Config)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω)
    (ha : active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ) :
    ‖StochasticEqualityMoments.pack p (trainingTrace p cfg g ξ (x ξ) offset n).estimate -
      StochasticEqualityMoments.pack p (truth (trainingTrace p cfg g ξ (x ξ) offset n).previous)‖ ^ 2 ≤
      4 * (cfg.gradientCap ^ 2 + cfg.constraintCap ^ 2 + p.Lc ^ 2) := by
  obtain ⟨hg, hc⟩ := active_previous_caps p cfg g truth x good offset n ξ ha
  obtain ⟨hvg, hvc, hvj⟩ := trace_estimate_caps p cfg hG hM hL g ξ (x ξ) offset n
  exact StochasticEqualityMoments.pack_error_bound p _ _ hg hc (hJ _) hvg hvc hvj

lemma training_output_trace {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (x : Point p.d) (offset : ℕ)
    (index : Fin cfg.steps) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2)) (trainingPlan p cfg index x) (2 * offset) =
      (trainingTrace p cfg g ξ x offset index).point := by
  exact training_output_prefix p cfg g (fun i => ξ (i / 2)) index x (2 * offset)

lemma measurable_trace {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (x : X → Point p.d) (hx : Measurable x) (offset n : ℕ) :
    Measurable (fun z => (trainingTrace p cfg g (ξ z) (x z) offset n).point) ∧
    Measurable (fun z => (trainingTrace p cfg g (ξ z) (x z) offset n).previous) ∧
    Measurable (fun z => (trainingTrace p cfg g (ξ z) (x z) offset n).estimate) ∧
    Measurable (fun z => (trainingTrace p cfg g (ξ z) (x z) offset n).selected) := by
  exact measurable_training_segment p cfg g hg ξ hξ n 0 offset 0
    (fun z => ⟨x z, x z, 0, x z⟩) hx hx measurable_const hx

abbrev PredictableState (p : Public) := ℝ × (Point p.d × Point p.d × Reply p)

noncomputable def predictableState {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ)
    (ξ : ℕ → Ω) : PredictableState p := by
  classical
  exact (if active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ
      then 1 else 0,
    (trainingTrace p cfg g ξ (x ξ) offset n).point,
    (trainingTrace p cfg g ξ (x ξ) offset n).previous,
    (trainingTrace p cfg g ξ (x ξ) offset n).estimate)

lemma predictableState_active {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) :
    (predictableState p cfg g truth x good offset n ξ).1 = 1 ↔
      active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ := by
  classical
  simp only [predictableState]
  split_ifs <;> simp_all

lemma measurable_predictableState {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ) :
    Measurable (predictableState p cfg g truth x good offset n) := by
  classical
  have hm := measurable_trace p cfg g hg id measurable_id x hx offset n
  have ha := measurableSet_active p cfg truth ht
    (fun k z => (trainingTrace p cfg g z (x z) offset k).point)
    (fun k => (measurable_trace p cfg g hg id measurable_id x hx offset k).1) good hgood n
  exact ((measurable_const (a := (1 : ℝ))).ite ha measurable_const).prodMk
    (hm.1.prodMk (hm.2.1.prodMk hm.2.2.1))

lemma predictableState_prefix_congr {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset : ℕ)
    (hx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hg : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (n : ℕ) (ξ ζ : ℕ → Ω) (h : ∀ i, i < batchOffset cfg offset n → ξ i = ζ i) :
    predictableState p cfg g truth x good offset n ξ = predictableState p cfg g truth x good offset n ζ := by
  have ht := trace_random_start_prefix_congr p cfg g x offset n hx ξ ζ h
  have ha := active_prefix_congr p cfg g truth x good offset hx hg n ξ ζ h
  classical
  by_cases hξ : active p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ
  · simp only [predictableState, hξ, ha.mp hξ, ↓reduceIte, ht]
  · have hζ := mt ha.mpr hξ
    simp only [predictableState, hξ, hζ, ↓reduceIte, ht]

noncomputable def incrementKernel {Ω : Type*} (p : Public)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (s : PredictableState p) (ω : Ω) : HilbertReply p :=
  (pack p (g s.2.1 ω) - pack p (truth s.2.1)) -
    (pack p (g s.2.2.1 ω) - pack p (truth s.2.2.1))

set_option maxHeartbeats 1000000 in
lemma measurable_incrementKernel {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth) :
    Measurable (Function.uncurry (incrementKernel p g truth)) := by
  have hm := measurable_centered_oracle p g hg truth ht
  have hx : Measurable (fun z : PredictableState p × Ω => (z.1.2.1, z.2)) :=
    measurable_fst.snd.fst.prodMk measurable_snd
  have hy : Measurable (fun z : PredictableState p × Ω => (z.1.2.2.1, z.2)) :=
    measurable_fst.snd.snd.fst.prodMk measurable_snd
  have hh := (hm.comp hx).sub (hm.comp hy)
  convert hh using 1
  rfl

lemma integrable_incrementKernel {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (P : Measure Ω) [IsFiniteMeasure P] (g : Point p.d → Ω → Reply p)
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p) (s : PredictableState p) :
    Integrable (incrementKernel p g truth s) P :=
  (integrable_centered_oracle p P _ (hi _) _).sub
    (integrable_centered_oracle p P _ (hi _) _)

lemma mean_incrementKernel {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (P : Measure Ω) [IsProbabilityMeasure P] (g : Point p.d → Ω → Reply p)
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p)
    (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x) (s : PredictableState p) :
    (∫ ω, incrementKernel p g truth s ω ∂P) = 0 := by
  unfold incrementKernel
  rw [integral_sub (integrable_centered_oracle p P _ (hi _) _)
    (integrable_centered_oracle p P _ (hi _) _),
    mean_centered_oracle p P _ (hi _) _ (hmean _),
    mean_centered_oracle p P _ (hi _) _ (hmean _), sub_self]

lemma variance_incrementKernel {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (P : Measure Ω) [IsProbabilityMeasure P] (g : Point p.d → Ω → Reply p)
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p)
    (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x)
    (h2 : ∀ x y, Integrable (fun ω => ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2) P)
    (hv : ∀ x y, (∫ ω, ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖x - y‖ ^ 2) (s : PredictableState p) :
    Integrable (fun ω => ‖incrementKernel p g truth s ω‖ ^ 2) P ∧
    (∫ ω, ‖incrementKernel p g truth s ω‖ ^ 2 ∂P) ≤ p.Lnoise ^ 2 * ‖s.2.1 - s.2.2.1‖ ^ 2 := by
  have h := centered_difference p (g s.2.1) (g s.2.2.1) (hi _) (hi _)
    (truth s.2.1) (truth s.2.2.1) (hmean _) (hmean _) (h2 _ _)
  exact ⟨h.1, h.2.trans (hv _ _)⟩

noncomputable def resetKernel {Ω : Type*} (p : Public)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (s : PredictableState p) (ω : Ω) : HilbertReply p :=
  pack p (g s.2.1 ω) - pack p (truth s.2.1)

lemma measurable_resetKernel {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth) :
    Measurable (Function.uncurry (resetKernel p g truth)) := by
  have hx : Measurable (fun z : PredictableState p × Ω => (z.1.2.1, z.2)) :=
    measurable_fst.snd.fst.prodMk measurable_snd
  have hh := (measurable_centered_oracle p g hg truth ht).comp hx
  convert hh using 1
  rfl

lemma integrable_movement_sq {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x) (offset n : ℕ) :
    Integrable (fun z => ‖(trainingTrace p cfg g z (x z) offset n).point -
      (trainingTrace p cfg g z (x z) offset n).previous‖ ^ 2) P := by
  have hm := measurable_trace p cfg g hg id measurable_id x hx offset n
  have hi : Integrable (fun _ : ℕ → Ω =>
      (cfg.step * (cfg.gradientCap + p.Lc * cfg.constraintCap)) ^ 2) P := integrable_const _
  apply hi.mono' ((hm.1.sub hm.2.1).norm.pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (trace_movement p cfg hν hL hG hM hη g z (x z) offset n) 2

open scoped Classical in
lemma integrable_masked_prior {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P]
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth) (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ) :
    let a := active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n
    let B := fun z => StochasticEqualityMoments.pack p (trainingTrace p cfg g z (x z) offset n).estimate -
      StochasticEqualityMoments.pack p (truth (trainingTrace p cfg g z (x z) offset n).previous)
    Integrable (fun z => ‖if a z then B z else 0‖ ^ 2) P := by
  classical
  dsimp only
  have hm := measurable_trace p cfg g hg id measurable_id x hx offset n
  have ha := measurableSet_active p cfg truth ht
    (fun k z => (trainingTrace p cfg g z (x z) offset k).point)
    (fun k => (measurable_trace p cfg g hg id measurable_id x hx offset k).1) good hgood n
  have hb := ((StochasticEqualityMoments.pack p).continuous.measurable.comp hm.2.2.1).sub
    ((StochasticEqualityMoments.pack p).continuous.measurable.comp (ht.comp hm.2.1))
  have hb' : Measurable (fun z => ‖if
      active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n z then
      StochasticEqualityMoments.pack p (trainingTrace p cfg g z (x z) offset n).estimate -
        StochasticEqualityMoments.pack p (truth (trainingTrace p cfg g z (x z) offset n).previous)
      else 0‖ ^ 2) := (hb.ite ha measurable_const).norm.pow_const 2
  have hi : Integrable (fun _ : ℕ → Ω =>
      4 * (cfg.gradientCap ^ 2 + cfg.constraintCap ^ 2 + p.Lc ^ 2)) P := integrable_const _
  apply hi.mono' hb'.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  split_ifs with hz
  · exact active_prior_error_bound p cfg hG hM hL g truth hJ x good offset n z hz
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

noncomputable def stoppedError {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) : ℝ := by
  classical
  exact if active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ then
    ‖pack p (trainingTrace p cfg g ξ (x ξ) offset (n + 1)).estimate -
      pack p (truth (trainingTrace p cfg g ξ (x ξ) offset n).point)‖ ^ 2 else 0

lemma stoppedError_nonneg {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) :
    0 ≤ stoppedError p cfg g truth x good offset n ξ := by
  unfold stoppedError
  split_ifs <;> positivity

lemma integrable_stoppedError {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P]
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth) (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ) :
    Integrable (stoppedError p cfg g truth x good offset n) P := by
  classical
  have hm := measurable_trace p cfg g hg id measurable_id x hx offset n
  have hn := measurable_trace p cfg g hg id measurable_id x hx offset (n + 1)
  have ha := measurableSet_active p cfg truth ht
    (fun k z => (trainingTrace p cfg g z (x z) offset k).point)
    (fun k => (measurable_trace p cfg g hg id measurable_id x hx offset k).1) good hgood n
  have he : Measurable (stoppedError p cfg g truth x good offset n) :=
    ((((pack p).continuous.measurable.comp hn.2.2.1).sub
      ((pack p).continuous.measurable.comp (ht.comp hm.1))).norm.pow_const 2).ite ha measurable_const
  have hi : Integrable (fun _ : ℕ → Ω =>
      4 * (cfg.gradientCap ^ 2 + cfg.constraintCap ^ 2 + p.Lc ^ 2)) P := integrable_const _
  apply hi.mono' he.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (stoppedError_nonneg p cfg g truth x good offset n z)]
  unfold stoppedError
  split_ifs with hz
  · obtain ⟨hcg, hcc⟩ := active_caps p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n z hz
    obtain ⟨hvg, hvc, hvj⟩ := trace_estimate_caps p cfg hG hM hL g z (x z) offset (n + 1)
    exact pack_error_bound p _ _ hcg hcc (hJ _) hvg hvc hvj
  · positivity

open scoped Classical in
lemma prior_survival_le {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) :
    let S := predictableState p cfg g truth x good offset (n + 1) ξ
    ‖if S.1 = 1 then pack p S.2.2.2 - pack p (truth S.2.2.1) else 0‖ ^ 2 ≤
      stoppedError p cfg g truth x good offset n ξ := by
  classical
  by_cases ha : active p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good (n + 1) ξ
  · have hb := active_mono p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good (Nat.le_succ n) ξ ha
    simp only [predictableState, ha, ↓reduceIte, stoppedError, hb, trace_previous, le_refl]
  · simpa only [predictableState, ha, ↓reduceIte, zero_ne_one, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      stoppedError_nonneg p cfg g truth x good offset n ξ

open scoped Classical in
lemma stoppedError_le_increment {Ω : Type*} (p : Public) (cfg : Config)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ)
    (hn : n % cfg.epoch ≠ 0) (ξ : ℕ → Ω) :
    let S := predictableState p cfg g truth x good offset n ξ
    stoppedError p cfg g truth x good offset n ξ ≤
      ‖if S.1 = 1 then (pack p S.2.2.2 - pack p (truth S.2.2.1)) +
        (cfg.incrementBatch : ℝ)⁻¹ • ∑ i ∈ Finset.range cfg.incrementBatch,
          incrementKernel p g truth S (ξ (batchOffset cfg offset n + i)) else 0‖ ^ 2 := by
  classical
  by_cases ha : active p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ
  · obtain ⟨hg, hc⟩ := active_caps p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ ha
    let s := trainingTrace p cfg g ξ (x ξ) offset n
    let v := QueryPlan.sampledEval g (fun i => ξ (i / 2))
      (estimatorPlan p cfg n s) (2 * batchOffset cfg offset n)
    have hh := pack_clip_contraction p hG hM hL (truth s.point) v hg hc (hJ _)
    dsimp only [v] at hh
    rw [estimator_increment_centered p cfg g truth ξ n (batchOffset cfg offset n) s hn] at hh
    simpa only [stoppedError, predictableState, ha, ↓reduceIte, incrementKernel,
      trace_succ, trainingUpdate, s] using hh
  · simp only [stoppedError, ha, ↓reduceIte]
    positivity

open scoped Classical in
lemma actual_increment_batch_variance {Ω : Type} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc) (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x)
    (h2 : ∀ x y, Integrable (fun ω => ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2) P)
    (hv : ∀ x y, (∫ ω, ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖x - y‖ ^ 2)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (b : ℕ) (hb : 0 < b) :
    let S := predictableState p cfg g truth x good offset n
    let B := fun s : PredictableState p => pack p s.2.2.2 - pack p (truth s.2.2.1)
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    Integrable (fun ξ => ‖if (S ξ).1 = 1 then B (S ξ) + (b : ℝ)⁻¹ •
      ∑ i ∈ Finset.range b, incrementKernel p g truth (S ξ) (ξ (batchOffset cfg offset n + i)) else 0‖ ^ 2) Q ∧
    (∫ ξ, ‖if (S ξ).1 = 1 then B (S ξ) + (b : ℝ)⁻¹ •
      ∑ i ∈ Finset.range b, incrementKernel p g truth (S ξ) (ξ (batchOffset cfg offset n + i)) else 0‖ ^ 2 ∂Q) ≤
      (∫ ξ, ‖if (S ξ).1 = 1 then B (S ξ) else 0‖ ^ 2 ∂Q) +
      (∫ ξ, if (S ξ).1 = 1 then p.Lnoise ^ 2 * ‖(S ξ).2.1 - (S ξ).2.2.1‖ ^ 2 else 0 ∂Q) / b := by
  classical
  let S := predictableState p cfg g truth x good offset n
  let B := fun s : PredictableState p => pack p s.2.2.2 - pack p (truth s.2.2.1)
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  have hS : Measurable S := measurable_predictableState p cfg g hg truth ht x hx good hgood offset n
  have hdS : ∀ ξ ζ, (∀ i, i < batchOffset cfg offset n → ξ i = ζ i) → S ξ = S ζ :=
    predictableState_prefix_congr p cfg g truth x good offset hdx hdgood n
  have ha : MeasurableSet {s : PredictableState p | s.1 = 1} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hB : Measurable B :=
    ((pack p).continuous.measurable.comp measurable_snd.snd.snd).sub
      ((pack p).continuous.measurable.comp (ht.comp measurable_snd.snd.fst))
  have hB2 : Integrable (fun ξ => ‖if (S ξ).1 = 1 then B (S ξ) else 0‖ ^ 2) Q := by
    convert integrable_masked_prior p cfg Q hG hM hL g hg truth ht hJ x hx good hgood offset n using 1
    funext ξ
    by_cases hz : active p cfg truth
        (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ <;>
      simp [S, B, predictableState, hz]
  have hai := measurableSet_active p cfg truth ht
    (fun k z => (trainingTrace p cfg g z (x z) offset k).point)
    (fun k => (measurable_trace p cfg g hg id measurable_id x hx offset k).1) good hgood n
  have hwi : Integrable (fun ξ => if (S ξ).1 = 1 then
      p.Lnoise ^ 2 * ‖(S ξ).2.1 - (S ξ).2.2.1‖ ^ 2 else 0) Q := by
    have hh := ((integrable_movement_sq p cfg Q hν hL hG hM hη g hg x hx offset n).const_mul
      (p.Lnoise ^ 2)).indicator hai
    convert hh using 1
    funext ξ
    by_cases hz : active p cfg truth
        (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ <;>
      simp [S, predictableState, Set.indicator, hz]
  exact masked_batch_variance p P (batchOffset cfg offset n) S hS hdS
    (fun s => s.1 = 1) ha B hB hB2 (incrementKernel p g truth)
    (measurable_incrementKernel p g hg truth ht) (integrable_incrementKernel p P g hi truth)
    (mean_incrementKernel p P g hi truth hmean)
    (fun s => (variance_incrementKernel p P g hi truth hmean h2 hv s).1)
    (fun s => p.Lnoise ^ 2 * ‖s.2.1 - s.2.2.1‖ ^ 2)
    (fun s => (variance_incrementKernel p P g hi truth hmean h2 hv s).2) hwi b hb

open scoped Classical in
lemma increment_stopped_error_bound {Ω : Type} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc) (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x)
    (h2 : ∀ x y, Integrable (fun ω => ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2) P)
    (hv : ∀ x y, (∫ ω, ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖x - y‖ ^ 2)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (hn : n % cfg.epoch ≠ 0) :
    let S := predictableState p cfg g truth x good offset n
    let B := fun s : PredictableState p => pack p s.2.2.2 - pack p (truth s.2.2.1)
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    (∫ ξ, stoppedError p cfg g truth x good offset n ξ ∂Q) ≤
      (∫ ξ, ‖if (S ξ).1 = 1 then B (S ξ) else 0‖ ^ 2 ∂Q) +
      (∫ ξ, if (S ξ).1 = 1 then p.Lnoise ^ 2 * ‖(S ξ).2.1 - (S ξ).2.2.1‖ ^ 2 else 0 ∂Q) /
        (cfg.incrementBatch : ℝ) := by
  classical
  have h := actual_increment_batch_variance p cfg P hν hL hG hM hη g hg hi truth ht hJ hmean h2 hv
    x hx good hgood offset n hdx hdgood cfg.incrementBatch cfg.incrementBatch.pos
  have he := integrable_stoppedError p cfg (Measure.infinitePi (fun _ : ℕ => P))
    hG hM hL g hg truth ht hJ x hx good hgood offset n
  exact (integral_mono he h.1 (fun ξ =>
    stoppedError_le_increment p cfg hG hM hL g truth hJ x good offset n hn ξ)).trans h.2

open scoped Classical in
lemma actual_reset_batch_variance {Ω : Type} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x)
    (h2 : ∀ x, Integrable (fun ω => ‖pack p (g x ω) - pack p (truth x)‖ ^ 2) P)
    (hv : ∀ x, (∫ ω, ‖pack p (g x ω) - pack p (truth x)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (b : ℕ) (hb : 0 < b) :
    let S := predictableState p cfg g truth x good offset n
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    Integrable (fun ξ => ‖if (S ξ).1 = 1 then (b : ℝ)⁻¹ •
      ∑ i ∈ Finset.range b, resetKernel p g truth (S ξ) (ξ (batchOffset cfg offset n + i)) else 0‖ ^ 2) Q ∧
    (∫ ξ, ‖if (S ξ).1 = 1 then (b : ℝ)⁻¹ •
      ∑ i ∈ Finset.range b, resetKernel p g truth (S ξ) (ξ (batchOffset cfg offset n + i)) else 0‖ ^ 2 ∂Q) ≤
      p.σ ^ 2 / b := by
  classical
  let S := predictableState p cfg g truth x good offset n
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  have hS : Measurable S := measurable_predictableState p cfg g hg truth ht x hx good hgood offset n
  have hdS : ∀ ξ ζ, (∀ i, i < batchOffset cfg offset n → ξ i = ζ i) → S ξ = S ζ :=
    predictableState_prefix_congr p cfg g truth x good offset hdx hdgood n
  have ha : MeasurableSet {s : PredictableState p | s.1 = 1} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hwi : Integrable (fun ξ => if (S ξ).1 = 1 then p.σ ^ 2 else 0) Q := by
    exact (integrable_const (p.σ ^ 2)).indicator (ha.preimage hS)
  have hB2 : Integrable (fun ξ => ‖if (S ξ).1 = 1 then (0 : HilbertReply p) else 0‖ ^ 2) Q := by
    simp only [ite_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact integrable_const 0
  have h := masked_batch_variance p P (batchOffset cfg offset n) S hS hdS
    (fun s => s.1 = 1) ha (fun _ => 0) measurable_const hB2 (resetKernel p g truth)
    (measurable_resetKernel p g hg truth ht)
    (fun s => integrable_centered_oracle p P _ (hi s.2.1) _)
    (fun s => mean_centered_oracle p P _ (hi s.2.1) _ (hmean s.2.1))
    (fun s => h2 s.2.1) (fun _ => p.σ ^ 2) (fun s => hv s.2.1) hwi b hb
  simp only [zero_add, ite_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, integral_zero] at h
  have hbound : (∫ ξ, if (S ξ).1 = 1 then p.σ ^ 2 else 0 ∂Q) ≤ p.σ ^ 2 := by
    calc
      _ ≤ ∫ _ : ℕ → Ω, p.σ ^ 2 ∂Q := integral_mono hwi (integrable_const _) (fun ξ => by
        split_ifs <;> first | exact le_rfl | exact sq_nonneg _)
      _ = _ := by simp [Q]
  exact ⟨h.1, h.2.trans (div_le_div_of_nonneg_right hbound (Nat.cast_nonneg b))⟩

open scoped Classical in
lemma stoppedError_le_reset {Ω : Type*} (p : Public) (cfg : Config)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ)
    (hn : n % cfg.epoch = 0) (ξ : ℕ → Ω) :
    let S := predictableState p cfg g truth x good offset n ξ
    stoppedError p cfg g truth x good offset n ξ ≤
      ‖if S.1 = 1 then (cfg.resetBatch : ℝ)⁻¹ • ∑ i ∈ Finset.range cfg.resetBatch,
        resetKernel p g truth S (ξ (batchOffset cfg offset n + i)) else 0‖ ^ 2 := by
  classical
  by_cases ha : active p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ
  · obtain ⟨hg, hc⟩ := active_caps p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ ha
    let s := trainingTrace p cfg g ξ (x ξ) offset n
    let v := QueryPlan.sampledEval g (fun i => ξ (i / 2))
      (estimatorPlan p cfg n s) (2 * batchOffset cfg offset n)
    have hh := pack_clip_contraction p hG hM hL (truth s.point) v hg hc (hJ _)
    dsimp only [v] at hh
    rw [estimator_reset_centered p cfg g truth ξ n (batchOffset cfg offset n) s hn] at hh
    simpa only [stoppedError, predictableState, ha, ↓reduceIte, resetKernel,
      trace_succ, trainingUpdate, s] using hh
  · simp only [stoppedError, ha, ↓reduceIte]
    positivity

open scoped Classical in
lemma reset_stopped_error_bound {Ω : Type} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x)
    (h2 : ∀ x, Integrable (fun ω => ‖pack p (g x ω) - pack p (truth x)‖ ^ 2) P)
    (hv : ∀ x, (∫ ω, ‖pack p (g x ω) - pack p (truth x)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (hn : n % cfg.epoch = 0) :
    (∫ ξ, stoppedError p cfg g truth x good offset n ξ
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ p.σ ^ 2 / (cfg.resetBatch : ℝ) := by
  have h := actual_reset_batch_variance p cfg P g hg hi truth ht hmean h2 hv
    x hx good hgood offset n hdx hdgood cfg.resetBatch cfg.resetBatch.pos
  have he := integrable_stoppedError p cfg (Measure.infinitePi (fun _ : ℕ => P))
    hG hM hL g hg truth ht hJ x hx good hgood offset n
  exact (integral_mono he h.1 (fun ξ =>
    stoppedError_le_reset p cfg hG hM hL g truth hJ x good offset n hn ξ)).trans h.2

open scoped Classical in
lemma integral_prior_survival_le {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P]
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth) (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ) :
    let S := predictableState p cfg g truth x good offset (n + 1)
    (∫ ξ, ‖if (S ξ).1 = 1 then pack p (S ξ).2.2.2 - pack p (truth (S ξ).2.2.1) else 0‖ ^ 2 ∂P) ≤
      ∫ ξ, stoppedError p cfg g truth x good offset n ξ ∂P := by
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (integrable_stoppedError p cfg P hG hM hL g hg truth ht hJ x hx good hgood offset n)
    (Filter.Eventually.of_forall fun ξ => prior_survival_le p cfg g truth x good offset n ξ)

open scoped Classical in
lemma increment_error_recurrence {Ω : Type} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc) (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x)
    (h2 : ∀ x y, Integrable (fun ω => ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2) P)
    (hv : ∀ x y, (∫ ω, ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖x - y‖ ^ 2)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (hn : (n + 1) % cfg.epoch ≠ 0) :
    let S := predictableState p cfg g truth x good offset (n + 1)
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    (∫ ξ, stoppedError p cfg g truth x good offset (n + 1) ξ ∂Q) ≤
      (∫ ξ, stoppedError p cfg g truth x good offset n ξ ∂Q) +
      (∫ ξ, if (S ξ).1 = 1 then p.Lnoise ^ 2 * ‖(S ξ).2.1 - (S ξ).2.2.1‖ ^ 2 else 0 ∂Q) /
        (cfg.incrementBatch : ℝ) := by
  have h := increment_stopped_error_bound p cfg P hν hL hG hM hη g hg hi truth ht hJ hmean h2 hv
    x hx good hgood offset (n + 1) hdx hdgood hn
  have hp := integral_prior_survival_le p cfg (Measure.infinitePi (fun _ : ℕ => P))
    hG hM hL g hg truth ht hJ x hx good hgood offset n
  exact h.trans (add_le_add hp le_rfl)

open scoped Classical in
lemma estimator_error_sum_bound {Ω : Type} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc) (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x)
    (h2 : ∀ x y, Integrable (fun ω => ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2) P)
    (hv : ∀ x y, (∫ ω, ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖x - y‖ ^ 2)
    (hnoise2 : ∀ y, Integrable (fun ω => ‖pack p (g y ω) - pack p (truth y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ ω, ‖pack p (g y ω) - pack p (truth y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset T : ℕ)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    :
    let S := fun k => predictableState p cfg g truth x good offset k
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    (∑ k ∈ Finset.range T, ∫ ξ, stoppedError p cfg g truth x good offset k ξ ∂Q) ≤
      T * (p.σ ^ 2 / (cfg.resetBatch : ℝ)) + (cfg.epoch : ℝ) *
        ∑ k ∈ Finset.range T,
          (∫ ξ, if (S k ξ).1 = 1 then p.Lnoise ^ 2 * ‖(S k ξ).2.1 - (S k ξ).2.2.1‖ ^ 2 else 0 ∂Q) /
            (cfg.incrementBatch : ℝ) := by
  classical
  apply reset_sum_bound _ _ _ cfg.epoch T cfg.epoch.pos
  · intro k hk
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply integral_nonneg
    intro ξ
    dsimp only
    split_ifs <;> positivity
  · intro k hk hr
    exact reset_stopped_error_bound p cfg P hG hM hL g hg hi truth ht hJ hmean hnoise2 hnoise
      x hx good hgood offset k hdx hdgood hr
  · intro k hk hr
    exact increment_error_recurrence p cfg P hν hL hG hM hη g hg hi truth ht hJ hmean h2 hv
      x hx good hgood offset k hdx hdgood hr

noncomputable def stoppedMovement {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) : ℝ := by
  classical
  exact if active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ then
    ‖(trainingTrace p cfg g ξ (x ξ) offset (n + 1)).point -
      (trainingTrace p cfg g ξ (x ξ) offset n).point‖ ^ 2 else 0

lemma stoppedMovement_nonneg {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) :
    0 ≤ stoppedMovement p cfg g truth x good offset n ξ := by
  unfold stoppedMovement
  split_ifs <;> positivity

lemma integrable_stoppedMovement {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ) :
    Integrable (stoppedMovement p cfg g truth x good offset n) P := by
  classical
  have ha := measurableSet_active p cfg truth ht
    (fun k z => (trainingTrace p cfg g z (x z) offset k).point)
    (fun k => (measurable_trace p cfg g hg id measurable_id x hx offset k).1) good hgood n
  convert (integrable_movement_sq p cfg P hν hL hG hM hη g hg x hx offset (n + 1)).indicator ha using 1
  funext ξ
  simp only [stoppedMovement, trace_previous, Set.indicator, Set.mem_ofPred_eq]

open scoped Classical in
lemma destination_movement_le {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) :
    let S := predictableState p cfg g truth x good offset (n + 1) ξ
    (if S.1 = 1 then ‖S.2.1 - S.2.2.1‖ ^ 2 else 0) ≤
      stoppedMovement p cfg g truth x good offset n ξ := by
  classical
  by_cases ha : active p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good (n + 1) ξ
  · have hb := active_mono p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good (Nat.le_succ n) ξ ha
    simp only [predictableState, ha, ↓reduceIte, stoppedMovement, hb, trace_previous, le_refl]
  · simpa only [predictableState, ha, ↓reduceIte, zero_ne_one] using
      stoppedMovement_nonneg p cfg g truth x good offset n ξ

open scoped Classical in
lemma destination_movement_sum_le {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset T : ℕ) :
    let S := fun k => predictableState p cfg g truth x good offset k
    (∑ k ∈ Finset.range T, ∫ ξ, if (S k ξ).1 = 1 then ‖(S k ξ).2.1 - (S k ξ).2.2.1‖ ^ 2 else 0 ∂P) ≤
      ∑ k ∈ Finset.range T, ∫ ξ, stoppedMovement p cfg g truth x good offset k ξ ∂P := by
  classical
  apply shifted_sum_bound
  · simp only [predictableState, trace_zero, sub_self, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_self, integral_zero]
  · intro k
    exact integral_nonneg (stoppedMovement_nonneg p cfg g truth x good offset k)
  · intro k
    apply integral_mono_of_nonneg _
      (integrable_stoppedMovement p cfg P hν hL hG hM hη g hg truth ht x hx good hgood offset k)
      (Filter.Eventually.of_forall fun ξ => destination_movement_le p cfg g truth x good offset k ξ)
    apply Filter.Eventually.of_forall
    intro ξ
    dsimp only
    split_ifs <;> positivity

open scoped Classical in
lemma destination_variance_sum_le {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset T : ℕ) :
    let S := fun k => predictableState p cfg g truth x good offset k
    (∑ k ∈ Finset.range T,
      (∫ ξ, if (S k ξ).1 = 1 then p.Lnoise ^ 2 * ‖(S k ξ).2.1 - (S k ξ).2.2.1‖ ^ 2 else 0 ∂P) /
        (cfg.incrementBatch : ℝ)) ≤
      (p.Lnoise ^ 2 / (cfg.incrementBatch : ℝ)) *
        ∑ k ∈ Finset.range T, ∫ ξ, stoppedMovement p cfg g truth x good offset k ξ ∂P := by
  classical
  let S := fun k => predictableState p cfg g truth x good offset k
  have he (k : ℕ) :
      (∫ ξ, if (S k ξ).1 = 1 then p.Lnoise ^ 2 * ‖(S k ξ).2.1 - (S k ξ).2.2.1‖ ^ 2 else 0 ∂P) /
        (cfg.incrementBatch : ℝ) =
      (p.Lnoise ^ 2 / (cfg.incrementBatch : ℝ)) *
        (∫ ξ, if (S k ξ).1 = 1 then ‖(S k ξ).2.1 - (S k ξ).2.2.1‖ ^ 2 else 0 ∂P) := by
    have hpoint (ξ : ℕ → Ω) :
        (if (S k ξ).1 = 1 then p.Lnoise ^ 2 * ‖(S k ξ).2.1 - (S k ξ).2.2.1‖ ^ 2 else 0) =
        p.Lnoise ^ 2 * (if (S k ξ).1 = 1 then ‖(S k ξ).2.1 - (S k ξ).2.2.1‖ ^ 2 else 0) := by
      split_ifs <;> simp
    simp_rw [hpoint]
    rw [integral_const_mul]
    ring
  change (∑ k ∈ Finset.range T,
    (∫ ξ, if (S k ξ).1 = 1 then p.Lnoise ^ 2 * ‖(S k ξ).2.1 - (S k ξ).2.2.1‖ ^ 2 else 0 ∂P) /
      (cfg.incrementBatch : ℝ)) ≤ _
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (destination_movement_sum_le p cfg P hν hL hG hM hη g hg truth ht x hx good hgood offset T)
    (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

open scoped Classical in
lemma estimator_error_energy {Ω : Type} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P] (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc) (hmean : ∀ x, ∫ ω, g x ω ∂P = truth x)
    (h2 : ∀ x y, Integrable (fun ω => ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2) P)
    (hv : ∀ x y, (∫ ω, ‖pack p (g x ω) - pack p (g y ω)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖x - y‖ ^ 2)
    (hnoise2 : ∀ y, Integrable (fun ω => ‖pack p (g y ω) - pack p (truth y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ ω, ‖pack p (g y ω) - pack p (truth y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset T : ℕ)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    :
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    (∑ k ∈ Finset.range T, ∫ ξ, stoppedError p cfg g truth x good offset k ξ ∂Q) ≤
      T * (p.σ ^ 2 / (cfg.resetBatch : ℝ)) +
        ((cfg.epoch : ℝ) * p.Lnoise ^ 2 / (cfg.incrementBatch : ℝ)) *
          ∑ k ∈ Finset.range T, ∫ ξ, stoppedMovement p cfg g truth x good offset k ξ ∂Q := by
  have h := estimator_error_sum_bound p cfg P hν hL hG hM hη g hg hi truth ht hJ hmean h2 hv
    hnoise2 hnoise x hx good hgood offset T hdx hdgood
  have hm := destination_variance_sum_le p cfg (Measure.infinitePi (fun _ : ℕ => P))
    hν hL hG hM hη g hg truth ht x hx good hgood offset T
  have hh := add_le_add (le_refl ((T : ℝ) * (p.σ ^ 2 / (cfg.resetBatch : ℝ))))
    (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (cfg.epoch : ℕ)))
  convert h.trans hh using 1
  ring

end LongTails.Proofs.StochasticEqualityProcess
