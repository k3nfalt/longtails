import LongTails.Proofs.AffineResidualExecution
import LongTails.Proofs.AffineSoftmaxSampling
import LongTails.Proofs.TwoSidedPLSampling

namespace LongTails.Proofs.AffineResidualSampling

open MeasureTheory

noncomputable def adaptiveHistory {ι S : Type*}
    (select : (k : ℕ) → (Fin k → ι) → S → ι) (seeds : ℕ → S) : (k : ℕ) → Fin k → ι
  | 0 => Fin.elim0
  | k + 1 => Fin.snoc (adaptiveHistory select seeds k)
      (select k (adaptiveHistory select seeds k) (seeds k))

noncomputable def historyState {ι X : Type*} (initial : X) (update : ℕ → X → ι → X) :
    (k : ℕ) → (Fin k → ι) → X
  | 0, _ => initial
  | k + 1, h => update k (historyState initial update k (Fin.init h)) (h (Fin.last k))

lemma historyState_snoc {ι X : Type*} (initial : X) (update : ℕ → X → ι → X)
    (k : ℕ) (h : Fin k → ι) (i : ι) :
    historyState initial update (k + 1) (Fin.snoc h i) = update k (historyState initial update k h) i := by
  simp [historyState]

lemma historyState_adaptive {ι S X : Type*} (initial : X) (update : ℕ → X → ι → X)
    (select : ℕ → X → S → ι) (states : (ℕ → S) → ℕ → X)
    (hzero : ∀ seeds, states seeds 0 = initial)
    (hstep : ∀ seeds k, states seeds (k + 1) =
      update k (states seeds k) (select k (states seeds k) (seeds k)))
    (seeds : ℕ → S) (k : ℕ) :
    states seeds k = historyState initial update k
      (adaptiveHistory (fun j h => select j (historyState initial update j h)) seeds k) := by
  induction k with
  | zero => exact hzero seeds
  | succ k ih => rw [hstep, adaptiveHistory, historyState_snoc, ih]

lemma adaptiveHistory_measurable {ι S : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ) :
    Measurable (fun seeds : ℕ → S => adaptiveHistory select seeds k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hs : Measurable (Function.uncurry (select k)) :=
        measurable_from_prod_countable_right (hselect k)
      have hn : Measurable (fun seeds : ℕ → S =>
          select k (adaptiveHistory select seeds k) (seeds k)) :=
        hs.comp (ih.prodMk (measurable_pi_apply k))
      exact (measurable_of_finite (fun p : (Fin k → ι) × ι => (Fin.snoc p.1 p.2 : Fin (k + 1) → ι))).comp
        (ih.prodMk hn)

lemma adaptiveHistory_prefix {ι S : Type*}
    (select : (k : ℕ) → (Fin k → ι) → S → ι) (seeds other : ℕ → S)
    (k : ℕ) (heq : ∀ j < k, seeds j = other j) :
    adaptiveHistory select seeds k = adaptiveHistory select other k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hh := ih (fun j hj => heq j (by omega))
      simp only [adaptiveHistory, hh, heq k (Nat.lt_succ_self k)]

lemma adaptiveHistory_restrict {ι S : Type*}
    (select : (k : ℕ) → (Fin k → ι) → S → ι) (seeds : ℕ → S)
    (j k : ℕ) (hjk : j ≤ k) :
    (fun i : Fin j => adaptiveHistory select seeds k (Fin.castLE hjk i)) =
      adaptiveHistory select seeds j := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
      funext i
      have he : Fin.castLE (Nat.le_succ_of_le h) i = (Fin.castLE h i).castSucc := rfl
      rw [he, adaptiveHistory, Fin.snoc_castSucc]
      exact congrFun ih i

lemma decoded_history_measurable {ι S X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S] [MeasurableSpace X]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ) (decode : (Fin k → ι) → X) :
    Measurable (fun seeds : ℕ → S => decode (adaptiveHistory select seeds k)) :=
  (measurable_of_finite decode).comp (adaptiveHistory_measurable select hselect k)

lemma decoded_history_finite_range {ι S X : Type*} [Fintype ι]
    (select : (k : ℕ) → (Fin k → ι) → S → ι) (k : ℕ) (decode : (Fin k → ι) → X) :
    (Set.range (fun seeds : ℕ → S => decode (adaptiveHistory select seeds k))).Finite :=
  (Set.finite_range decode).subset (by rintro _ ⟨seeds, rfl⟩; exact ⟨_, rfl⟩)

lemma decoded_history_stronglyMeasurable {ι S X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S] [TopologicalSpace X]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ) (decode : (Fin k → ι) → X) :
    StronglyMeasurable (fun seeds : ℕ → S => decode (adaptiveHistory select seeds k)) :=
  StronglyMeasurable.of_discrete.comp_measurable (adaptiveHistory_measurable select hselect k)

lemma decoded_history_integrable {ι S X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S] [NormedAddCommGroup X]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ) (decode : (Fin k → ι) → X)
    (P : Measure (ℕ → S)) [IsFiniteMeasure P] :
    Integrable (fun seeds : ℕ → S => decode (adaptiveHistory select seeds k)) P := by
  have hm := adaptiveHistory_measurable select hselect k
  have hi : Integrable decode (P.map (fun seeds => adaptiveHistory select seeds k)) :=
    Integrable.of_finite
  exact (integrable_map_measure StronglyMeasurable.of_discrete.aestronglyMeasurable hm.aemeasurable).1 hi

lemma history_observable_factor {ι S X : Type*}
    (select : (k : ℕ) → (Fin k → ι) → S → ι) (k : ℕ)
    (observe : (ℕ → S) → X) (fallback : X)
    (hcongr : ∀ seeds other, adaptiveHistory select seeds k = adaptiveHistory select other k →
      observe seeds = observe other) :
    ∃ decode : (Fin k → ι) → X, ∀ seeds, observe seeds = decode (adaptiveHistory select seeds k) := by
  classical
  let decode := fun h : Fin k → ι => if hex : ∃ seeds, adaptiveHistory select seeds k = h then
    observe (Classical.choose hex) else fallback
  refine ⟨decode, fun seeds => ?_⟩
  have hex : ∃ other, adaptiveHistory select other k = adaptiveHistory select seeds k := ⟨seeds, rfl⟩
  dsimp only [decode]
  rw [dite_eq_left hex]
  exact hcongr seeds (Classical.choose hex) (Classical.choose_spec hex).symm

lemma history_observable_measurable {ι S X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S] [MeasurableSpace X]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ)
    (observe : (ℕ → S) → X) (fallback : X)
    (hcongr : ∀ seeds other, adaptiveHistory select seeds k = adaptiveHistory select other k →
      observe seeds = observe other) : Measurable observe := by
  obtain ⟨decode, hd⟩ := history_observable_factor select k observe fallback hcongr
  have he : observe = fun seeds => decode (adaptiveHistory select seeds k) := funext hd
  rw [he]
  exact decoded_history_measurable select hselect k decode

lemma history_observable_integrable {ι S X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S] [NormedAddCommGroup X]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ)
    (observe : (ℕ → S) → X)
    (hcongr : ∀ seeds other, adaptiveHistory select seeds k = adaptiveHistory select other k →
      observe seeds = observe other) (P : Measure (ℕ → S)) [IsFiniteMeasure P] :
    Integrable observe P := by
  obtain ⟨decode, hd⟩ := history_observable_factor select k observe 0 hcongr
  have he : observe = fun seeds => decode (adaptiveHistory select seeds k) := funext hd
  rw [he]
  exact decoded_history_integrable select hselect k decode P

lemma adaptive_payoff_integrable {ι S : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ) (payoff : (Fin k → ι) → ι → ℝ)
    (P : Measure (ℕ → S)) [IsFiniteMeasure P] :
    Integrable (fun seeds : ℕ → S => payoff (adaptiveHistory select seeds k)
      (select k (adaptiveHistory select seeds k) (seeds k))) P := by
  have hi := decoded_history_integrable select hselect (k + 1)
    (fun h => payoff (Fin.init h) (h (Fin.last k))) P
  simpa [adaptiveHistory] using hi

lemma adaptive_payoff_integral {ι S : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ) (payoff : (Fin k → ι) → ι → ℝ)
    (p : Measure S) [IsProbabilityMeasure p] :
    (∫ seeds, payoff (adaptiveHistory select seeds k)
      (select k (adaptiveHistory select seeds k) (seeds k))
        ∂(Measure.infinitePi fun _ : ℕ => p)) =
      ∫ seeds, (∫ seed, payoff (adaptiveHistory select seeds k)
        (select k (adaptiveHistory select seeds k) seed) ∂p)
          ∂(Measure.infinitePi fun _ : ℕ => p) := by
  apply OracleTemplate.TwoSidedPL.integral_prefix_dep p k
    (fun seeds => adaptiveHistory select seeds k) (adaptiveHistory_measurable select hselect k)
    (fun seeds other heq => adaptiveHistory_prefix select seeds other k heq)
    (fun h seed => payoff h (select k h seed))
  · exact measurable_from_prod_countable_right fun h =>
      (measurable_of_finite (payoff h)).comp (hselect k h)
  · exact adaptive_payoff_integrable select hselect k payoff _

lemma adaptive_payoff_bound {ι S : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ) (payoff : (Fin k → ι) → ι → ℝ)
    (p : Measure S) [IsProbabilityMeasure p] {B : ℝ}
    (hbound : ∀ h, ∫ seed, payoff h (select k h seed) ∂p ≤ B) :
    Integrable (fun seeds => payoff (adaptiveHistory select seeds k)
      (select k (adaptiveHistory select seeds k) (seeds k))) (Measure.infinitePi fun _ : ℕ => p) ∧
      (∫ seeds, payoff (adaptiveHistory select seeds k)
        (select k (adaptiveHistory select seeds k) (seeds k))
          ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ B := by
  refine ⟨adaptive_payoff_integrable select hselect k payoff _, ?_⟩
  rw [adaptive_payoff_integral select hselect k payoff p]
  have hi := decoded_history_integrable select hselect k
    (fun h => ∫ seed, payoff h (select k h seed) ∂p) (Measure.infinitePi fun _ : ℕ => p)
  calc
    _ ≤ ∫ _seeds : ℕ → S, B ∂(Measure.infinitePi fun _ : ℕ => p) :=
      integral_mono hi (integrable_const B) (fun seeds => hbound (adaptiveHistory select seeds k))
    _ = B := by simp

lemma adaptive_payoff_zero {ι S : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace S]
    (select : (k : ℕ) → (Fin k → ι) → S → ι)
    (hselect : ∀ k h, Measurable (select k h)) (k : ℕ) (payoff : (Fin k → ι) → ι → ℝ)
    (p : Measure S) [IsProbabilityMeasure p]
    (hzero : ∀ h, ∫ seed, payoff h (select k h seed) ∂p = 0) :
    (∫ seeds, payoff (adaptiveHistory select seeds k)
      (select k (adaptiveHistory select seeds k) (seeds k))
        ∂(Measure.infinitePi fun _ : ℕ => p)) = 0 := by
  rw [adaptive_payoff_integral select hselect k payoff p]
  simp only [hzero, integral_zero]

section ComponentHistory

open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot affine)
open LongTails.Algorithms.AffineSoftmaxQueries (gibbsWeights)
open LongTails.Algorithms.FiniteCategoricalSampler (draw)
open LongTails.Proofs.AffineSoftmaxSampling (categorical_draw_measurable)

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [StandardBorelSpace ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def chosenIndices (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (seed : StepSeed) : ι × ι :=
  let v := predictor C s τ μ η state
  (draw ι (gibbsWeights (τ * (1 + 1 / η)) (predictorScores s τ η state v.point)) seed.1,
    draw ι (gibbsWeights 1 (fun _ => 0)) seed.2)

noncomputable def indexedStep (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ η D : ℝ) (reply : ι × E → ℝ × E) (state : State ι E) (indices : ι × ι) : State ι E × E :=
  let v := predictor C s τ μ η state
  (correction project s τ μ η state v ((reply (indices.1, v.point)).2 - s.field indices.1)
    (coordinateReply indices.2 (D - ((reply (indices.2, v.point)).1 - affine s indices.2 v.point))),
    v.point)

lemma stepPlan_eval_indices (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ η D : ℝ) (reply : ι × E → ℝ × E) (state : State ι E) (seed : StepSeed) :
    OracleTemplate.ComponentEnvelope.Program.eval reply (stepPlan C project s τ μ η D state seed) =
      indexedStep C project s τ μ η D reply state (chosenIndices C s τ μ η state seed) := by
  rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι] in
lemma indexedStep_valid {C : Set E} (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) (τ μ η D : ℝ) (reply : ι × E → ℝ × E)
    (state : State ι E) (indices : ι × ι) :
    let n := (indexedStep C (OracleTemplate.SaddlePoint.project C) s τ μ η D reply state indices).1
    n.point ∈ C ∧ (∀ i, 0 < n.probability i) ∧ ∑ i, n.probability i = 1 := by
  dsimp only [indexedStep]
  refine ⟨?_, fun i => LongTails.Proofs.AffineResidualSaddle.correction_probability_pos _ _ _ _ _ _ _ _ _ i,
    LongTails.Proofs.AffineResidualSaddle.correction_probability_sum _ _ _ _ _ _ _ _ _⟩
  change OracleTemplate.SaddlePoint.project C _ ∈ C
  exact (OracleTemplate.SaddlePoint.project_spec hne hC hconv _).1

lemma solverState_valid {C : Set E} (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) (τ μ β D : ℝ) (reply : ι × E → ℝ × E)
    (initial : State ι E) (hi : initial.point ∈ C)
    (hip : ∀ i, 0 < initial.probability i) (hisum : ∑ i, initial.probability i = 1)
    (seeds : ℕ → StepSeed) (N : ℕ) :
    let n := (solverState β initial (fun k state seed => OracleTemplate.ComponentEnvelope.Program.eval reply
      (stepPlan C (OracleTemplate.SaddlePoint.project C) s τ μ (stepSize β k) D state seed)) seeds N).1
    n.point ∈ C ∧ (∀ i, 0 < n.probability i) ∧ ∑ i, n.probability i = 1 := by
  cases N with
  | zero => exact ⟨hi, hip, hisum⟩
  | succ N =>
      simp only [solverState, stepPlan_eval_indices]
      exact indexedStep_valid hC hne hconv s τ μ (stepSize β N) D reply _ _

lemma chosenIndices_measurable (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ) (state : State ι E) :
    Measurable (chosenIndices C s τ μ η state) := by
  exact ((categorical_draw_measurable ι).comp (measurable_const.prodMk measurable_fst)).prodMk
    ((categorical_draw_measurable ι).comp (measurable_const.prodMk measurable_snd))

lemma chosenIndices_integrable {X : Type*} [NormedAddCommGroup X]
    (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ) (state : State ι E)
    (F : ι × ι → X) :
    Integrable (fun seed => F (chosenIndices C s τ μ η state seed))
      ((volume : Measure unitInterval).prod volume) := by
  have hm := chosenIndices_measurable C s τ μ η state
  have hi : Integrable F (((volume : Measure unitInterval).prod volume).map
      (chosenIndices C s τ μ η state)) := Integrable.of_finite
  exact (integrable_map_measure StronglyMeasurable.of_discrete.aestronglyMeasurable hm.aemeasurable).1 hi

lemma chosenIndices_integral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ) (state : State ι E) (F : ι × ι → X) :
    (∫ seed, F (chosenIndices C s τ μ η state seed)
      ∂((volume : Measure unitInterval).prod volume)) =
        ∑ i, (predictor C s τ μ η state).probability i •
          (∑ j, ((Fintype.card ι : ℝ)⁻¹) • F (i, j)) := by
  let T := τ * (1 + 1 / η)
  let scores := predictorScores s τ η state (predictor C s τ μ η state).point
  have hg (i : ι) : LongTails.Algorithms.AffineSoftmaxEstimator.gibbsWeight 1 (fun _ : ι => 0) i =
      (Fintype.card ι : ℝ)⁻¹ := by
    simp [LongTails.Algorithms.AffineSoftmaxEstimator.gibbsWeight]
  rw [integral_prod _ (chosenIndices_integrable C s τ μ η state F)]
  calc
    _ = ∫ u : unitInterval, ∑ j,
        LongTails.Algorithms.AffineSoftmaxEstimator.gibbsWeight 1 (fun _ : ι => 0) j •
          F (draw ι (gibbsWeights T scores) u, j) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u =>
        LongTails.Proofs.AffineSoftmaxSampling.gibbs_draw_integral ι 1 (fun _ => 0)
          (fun j => F (draw ι (gibbsWeights T scores) u, j))
    _ = _ := by
      rw [LongTails.Proofs.AffineSoftmaxSampling.gibbs_draw_integral ι T scores
        (fun i => ∑ j, LongTails.Algorithms.AffineSoftmaxEstimator.gibbsWeight 1 (fun _ : ι => 0) j • F (i, j))]
      simp_rw [hg]
      rfl

lemma chosenIndices_primal_integral {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X]
    (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ) (state : State ι E) (F : ι → X) :
    (∫ seed, F (chosenIndices C s τ μ η state seed).1
      ∂((volume : Measure unitInterval).prod volume)) =
        ∑ i, (predictor C s τ μ η state).probability i • F i := by
  have h := chosenIndices_integral C s τ μ η state (fun ij => F ij.1)
  have hi (i : ι) : (∑ _j : ι, ((Fintype.card ι : ℝ)⁻¹) • F i) = F i := by
    rw [← Finset.sum_smul]
    simp [nsmul_eq_mul, (show (Fintype.card ι : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)]
  simpa only [hi] using h

lemma chosenIndices_dual_integral {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X]
    (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ) (state : State ι E) (F : ι → X) :
    (∫ seed, F (chosenIndices C s τ μ η state seed).2
      ∂((volume : Measure unitInterval).prod volume)) =
        ((Fintype.card ι : ℝ)⁻¹) • ∑ j, F j := by
  have h := chosenIndices_integral C s τ μ η state (fun ij => F ij.2)
  simp only at h
  rw [← Finset.sum_smul, LongTails.Proofs.AffineResidualSaddle.predictor_probability_sum,
    one_smul, ← Finset.smul_sum] at h
  exact h

lemma dual_coordinate_mean (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (r : ι → ℝ) (i : ι) :
    (∫ seed, coordinateReply (chosenIndices C s τ μ η state seed).2
      (r (chosenIndices C s τ μ η state seed).2) i
        ∂((volume : Measure unitInterval).prod volume)) = r i := by
  rw [chosenIndices_dual_integral C s τ μ η state (fun j => coordinateReply j (r j) i)]
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    LongTails.Proofs.AffineResidualSaddle.coordinateReply_mean r i

lemma dual_centered_moment (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (p r : ι → ℝ) {D : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ D) :
    (∫ seed, ∑ i, p i *
      (coordinateReply (chosenIndices C s τ μ η state seed).2
        (r (chosenIndices C s τ μ η state seed).2) i - r i) ^ 2
          ∂((volume : Measure unitInterval).prod volume)) ≤ (Fintype.card ι : ℝ) * D ^ 2 := by
  rw [chosenIndices_dual_integral C s τ μ η state
    (fun j => ∑ i, p i * (coordinateReply j (r j) i - r i) ^ 2)]
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    LongTails.Proofs.AffineResidualSaddle.coordinateReply_variance_bound hp hpsum hr

lemma dual_second_moment (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (p r : ι → ℝ) {D : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ D) :
    (∫ seed, ∑ i, p i *
      (coordinateReply (chosenIndices C s τ μ η state seed).2
        (r (chosenIndices C s τ μ η state seed).2) i) ^ 2
          ∂((volume : Measure unitInterval).prod volume)) ≤ (Fintype.card ι : ℝ) * D ^ 2 := by
  rw [chosenIndices_dual_integral C s τ μ η state
    (fun j => ∑ i, p i * (coordinateReply j (r j) i) ^ 2)]
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    LongTails.Proofs.AffineResidualSaddle.coordinateReply_second_bound hp hpsum hr

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι] in
lemma primal_weighted_square_bound (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (g : ι → E) {M : ℝ} (hbound : ∀ i, ‖g i‖ ≤ M) :
    (∑ i, (predictor C s τ μ η state).probability i * ‖g i‖ ^ 2) ≤ M ^ 2 := by
  calc
    _ ≤ ∑ i, (predictor C s τ μ η state).probability i * M ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (by nlinarith [hbound i, norm_nonneg (g i)])
        (LongTails.Proofs.AffineResidualSaddle.predictor_probability_pos C s τ μ η state i).le
    _ = _ := by
      rw [← Finset.sum_mul, LongTails.Proofs.AffineResidualSaddle.predictor_probability_sum, one_mul]

lemma primal_second_moment (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (g : ι → E) {M : ℝ} (hbound : ∀ i, ‖g i‖ ≤ M) :
    (∫ seed, ‖g (chosenIndices C s τ μ η state seed).1‖ ^ 2
      ∂((volume : Measure unitInterval).prod volume)) ≤ M ^ 2 := by
  rw [chosenIndices_primal_integral C s τ μ η state (fun i => ‖g i‖ ^ 2)]
  simpa only [smul_eq_mul] using primal_weighted_square_bound C s τ μ η state g hbound

lemma primal_centered_moment [CompleteSpace E] (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (g : ι → E) :
    (∫ seed, ‖g (chosenIndices C s τ μ η state seed).1 -
      (∑ i, (predictor C s τ μ η state).probability i • g i)‖ ^ 2
        ∂((volume : Measure unitInterval).prod volume)) ≤
          ∑ i, (predictor C s τ μ η state).probability i * ‖g i‖ ^ 2 := by
  have hi := chosenIndices_integrable C s τ μ η state (fun ij => g ij.1)
  have hi2 := chosenIndices_integrable C s τ μ η state (fun ij => ‖g ij.1‖ ^ 2)
  have hh := LongTails.Proofs.AffineSoftmaxSampling.centered_second_moment
    (⟨(volume : Measure unitInterval).prod volume, inferInstance⟩ : ProbabilityMeasure StepSeed)
    (fun seed => g (chosenIndices C s τ μ η state seed).1) hi hi2
  change (∫ seed, ‖g (chosenIndices C s τ μ η state seed).1 -
    (∫ seed, g (chosenIndices C s τ μ η state seed).1
      ∂((volume : Measure unitInterval).prod volume))‖ ^ 2
        ∂((volume : Measure unitInterval).prod volume)) ≤
    ∫ seed, ‖g (chosenIndices C s τ μ η state seed).1‖ ^ 2
      ∂((volume : Measure unitInterval).prod volume) at hh
  rw [chosenIndices_primal_integral C s τ μ η state g,
    chosenIndices_primal_integral C s τ μ η state (fun i => ‖g i‖ ^ 2)] at hh
  simpa only [smul_eq_mul] using hh

lemma noise_pairing_mean [CompleteSpace E] (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state u v : State ι E) (g : ι → E) (r : ι → ℝ) :
    (∫ seed, LongTails.Proofs.AffineResidualSaddle.pairing
      ((∑ i, (predictor C s τ μ η state).probability i • g i) -
        g (chosenIndices C s τ μ η state seed).1)
      (fun i => r i - coordinateReply (chosenIndices C s τ μ η state seed).2
        (r (chosenIndices C s τ μ η state seed).2) i) v u
          ∂((volume : Measure unitInterval).prod volume)) = 0 := by
  let P : Measure StepSeed := (volume : Measure unitInterval).prod volume
  let mean := ∑ i, (predictor C s τ μ η state).probability i • g i
  let e := fun seed => mean - g (chosenIndices C s τ μ η state seed).1
  let d := fun seed i => r i - coordinateReply (chosenIndices C s τ μ η state seed).2
    (r (chosenIndices C s τ μ η state seed).2) i
  have hgi := chosenIndices_integrable C s τ μ η state (fun ij => g ij.1)
  have hei : Integrable e P := (integrable_const mean).sub hgi
  have hdi (i : ι) : Integrable (fun seed => d seed i) P :=
    (integrable_const (r i)).sub
      (chosenIndices_integrable C s τ μ η state (fun ij => coordinateReply ij.2 (r ij.2) i))
  have he : (∫ seed, e seed ∂P) = 0 := by
    dsimp only [e, P]
    rw [integral_sub (integrable_const mean) hgi,
      chosenIndices_primal_integral C s τ μ η state g]
    simp only [integral_const, probReal_univ, one_smul, mean, sub_self]
  have hd (i : ι) : (∫ seed, d seed i ∂P) = 0 := by
    dsimp only [d, P]
    rw [integral_sub (integrable_const (r i))
      (chosenIndices_integrable C s τ μ η state (fun ij => coordinateReply ij.2 (r ij.2) i)),
      dual_coordinate_mean]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
  have hinner : (∫ seed, inner (𝕜 := ℝ) (e seed) (v.point - u.point) ∂P) = 0 := by
    calc
      _ = ∫ seed, inner (𝕜 := ℝ) (v.point - u.point) (e seed) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun seed => real_inner_comm _ _
      _ = 0 := by rw [integral_inner hei, he, inner_zero_right]
  have hdual (i : ι) :
      (∫ seed, d seed i * (v.probability i - u.probability i) ∂P) = 0 := by
    rw [integral_mul_const, hd, zero_mul]
  change (∫ seed, inner (𝕜 := ℝ) (e seed) (v.point - u.point) +
    ∑ i, d seed i * (v.probability i - u.probability i) ∂P) = 0
  rw [integral_add (hei.inner_const _) (integrable_finsetSum _ fun i _ => (hdi i).mul_const _),
    integral_finsetSum _ (fun i _ => (hdi i).mul_const _), hinner]
  simp only [hdual, Finset.sum_const_zero, add_zero]

noncomputable def solverHistoryUpdate (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ β D : ℝ) (reply : ι × E → ℝ × E) (k : ℕ) (state : State ι E × E)
    (indices : ι × ι) : State ι E × E :=
  let next := indexedStep C project s τ μ (stepSize β k) D reply state.1 indices
  (next.1, state.2 + iterationWeight β k • next.2)

lemma solverState_history (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ β D : ℝ) (reply : ι × E → ℝ × E) (initial : State ι E)
    (seeds : ℕ → StepSeed) (k : ℕ) :
    let update := solverHistoryUpdate C project s τ μ β D reply
    let select := fun j (h : Fin j → ι × ι) =>
      chosenIndices C s τ μ (stepSize β j) (historyState (initial, 0) update j h).1
    solverState β initial (fun j state seed => OracleTemplate.ComponentEnvelope.Program.eval reply
      (stepPlan C project s τ μ (stepSize β j) D state seed)) seeds k =
      historyState (initial, 0) update k (adaptiveHistory select seeds k) := by
  apply historyState_adaptive (initial, 0) (solverHistoryUpdate C project s τ μ β D reply)
    (fun j state => chosenIndices C s τ μ (stepSize β j) state.1)
  · intro _
    rfl
  · intro seeds j
    simp only [solverState, stepPlan_eval_indices, solverHistoryUpdate]

lemma solverState_observable_finite_range {X : Type*}
    (C : Set E) (project : E → E) (s : Snapshot ι E) (τ μ β D : ℝ)
    (reply : ι × E → ℝ × E) (initial : State ι E) (k : ℕ) (observe : State ι E × E → X) :
    (Set.range (fun seeds : ℕ → StepSeed => observe (solverState β initial
      (fun j state seed => OracleTemplate.ComponentEnvelope.Program.eval reply
        (stepPlan C project s τ μ (stepSize β j) D state seed)) seeds k))).Finite := by
  simp_rw [solverState_history]
  exact decoded_history_finite_range (ι := ι × ι)
    (fun j h => chosenIndices C s τ μ (stepSize β j)
      (historyState (initial, 0) (solverHistoryUpdate C project s τ μ β D reply) j h).1) k
    (fun h => observe (historyState (initial, 0) (solverHistoryUpdate C project s τ μ β D reply) k h))

lemma solverState_observable_measurable {X : Type*} [MeasurableSpace X]
    (C : Set E) (project : E → E) (s : Snapshot ι E) (τ μ β D : ℝ)
    (reply : ι × E → ℝ × E) (initial : State ι E) (k : ℕ) (observe : State ι E × E → X) :
    Measurable (fun seeds : ℕ → StepSeed => observe (solverState β initial
      (fun j state seed => OracleTemplate.ComponentEnvelope.Program.eval reply
        (stepPlan C project s τ μ (stepSize β j) D state seed)) seeds k)) := by
  simp_rw [solverState_history]
  exact decoded_history_measurable (ι := ι × ι)
    (fun j h => chosenIndices C s τ μ (stepSize β j)
      (historyState (initial, 0) (solverHistoryUpdate C project s τ μ β D reply) j h).1)
    (fun j h => chosenIndices_measurable _ _ _ _ _ _) k
    (fun h => observe (historyState (initial, 0) (solverHistoryUpdate C project s τ μ β D reply) k h))

lemma solverState_observable_integrable {X : Type*} [NormedAddCommGroup X]
    (C : Set E) (project : E → E) (s : Snapshot ι E) (τ μ β D : ℝ)
    (reply : ι × E → ℝ × E) (initial : State ι E) (k : ℕ) (observe : State ι E × E → X)
    (P : Measure (ℕ → StepSeed)) [IsFiniteMeasure P] :
    Integrable (fun seeds : ℕ → StepSeed => observe (solverState β initial
      (fun j state seed => OracleTemplate.ComponentEnvelope.Program.eval reply
        (stepPlan C project s τ μ (stepSize β j) D state seed)) seeds k)) P := by
  simp_rw [solverState_history]
  exact decoded_history_integrable (ι := ι × ι)
    (fun j h => chosenIndices C s τ μ (stepSize β j)
      (historyState (initial, 0) (solverHistoryUpdate C project s τ μ β D reply) j h).1)
    (fun j h => chosenIndices_measurable _ _ _ _ _ _) k
    (fun h => observe (historyState (initial, 0) (solverHistoryUpdate C project s τ μ β D reply) k h)) P

end ComponentHistory

end LongTails.Proofs.AffineResidualSampling
