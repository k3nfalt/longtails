import LongTails.Proofs.AffineResidualSampling
import LongTails.Proofs.AffineResidualWeighted
import LongTails.Proofs.AffineResidualOutput

namespace LongTails.Proofs.AffineResidualTrajectory

open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot affine)
open LongTails.Proofs.AffineResidualSaddle
open LongTails.Proofs.AffineResidualSampling
open LongTails.Proofs.AffineResidualRegret
open LongTails.Proofs.AffineResidualWeighted

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [StandardBorelSpace ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (C : Set E) (s : Snapshot ι E) (τ μ β D : ℝ)
  (f : ι → E → ℝ) (field : ι → E → E) (initial : State ι E) (seeds : ℕ → StepSeed)

noncomputable def runState (k : ℕ) : State ι E :=
  (solverState β initial (fun j state seed => OracleTemplate.ComponentEnvelope.Program.eval
    (fun q => (f q.1 q.2, field q.1 q.2))
    (stepPlan C (OracleTemplate.SaddlePoint.project C) s τ μ (stepSize β j) D state seed)) seeds k).1

noncomputable def predicted (k : ℕ) : State ι E :=
  predictor C s τ μ (stepSize β k) (runState C s τ μ β D f field initial seeds k)

noncomputable def indices (k : ℕ) : ι × ι :=
  chosenIndices C s τ μ (stepSize β k) (runState C s τ μ β D f field initial seeds k) (seeds k)

noncomputable def primalSample (k : ℕ) : E :=
  field (indices C s τ μ β D f field initial seeds k).1 (predicted C s τ μ β D f field initial seeds k).point -
    s.field (indices C s τ μ β D f field initial seeds k).1

noncomputable def dualMean (k : ℕ) (i : ι) : ℝ :=
  D - (f i (predicted C s τ μ β D f field initial seeds k).point -
    affine s i (predicted C s τ μ β D f field initial seeds k).point)

noncomputable def dualSample (k : ℕ) : ι → ℝ :=
  coordinateReply (indices C s τ μ β D f field initial seeds k).2
    (dualMean C s τ μ β D f field initial seeds k (indices C s τ μ β D f field initial seeds k).2)

noncomputable def primalMean (k : ℕ) : E :=
  ∑ i, (predicted C s τ μ β D f field initial seeds k).probability i •
    (field i (predicted C s τ μ β D f field initial seeds k).point - s.field i)

noncomputable def primalError (k : ℕ) : E :=
  primalMean C s τ μ β D f field initial seeds k - primalSample C s τ μ β D f field initial seeds k

noncomputable def dualError (k : ℕ) (i : ι) : ℝ :=
  dualMean C s τ μ β D f field initial seeds k i - dualSample C s τ μ β D f field initial seeds k i

noncomputable def ghost (k : ℕ) : State ι E :=
  weightedAuxiliary C μ τ β initial (predicted C s τ μ β D f field initial seeds)
    (primalError C s τ μ β D f field initial seeds) (dualError C s τ μ β D f field initial seeds) k

lemma ghost_probability_pos (k : ℕ) (i : ι) :
    0 < (ghost C s τ μ β D f field initial seeds k).probability i := by
  unfold ghost weightedAuxiliary auxiliaryPredictor
  exact linearMinimizer_probability_pos _ _ _ _ _ _ _

lemma ghost_probability_sum (k : ℕ) :
    (∑ i, (ghost C s τ μ β D f field initial seeds k).probability i) = 1 := by
  unfold ghost weightedAuxiliary auxiliaryPredictor
  exact linearMinimizer_probability_sum _ _ _ _ _ _

lemma runState_prefix (other : ℕ → StepSeed) (k : ℕ)
    (hprefix : ∀ j < k, seeds j = other j) :
    runState C s τ μ β D f field initial seeds k = runState C s τ μ β D f field initial other k := by
  unfold runState
  rw [AffineResidualExecution.solverState_prefix β initial _ seeds other k hprefix]

lemma predicted_prefix (other : ℕ → StepSeed) (k : ℕ)
    (hprefix : ∀ j < k, seeds j = other j) :
    predicted C s τ μ β D f field initial seeds k = predicted C s τ μ β D f field initial other k := by
  unfold predicted
  rw [runState_prefix C s τ μ β D f field initial seeds other k hprefix]

lemma errors_prefix (other : ℕ → StepSeed) (k : ℕ)
    (hprefix : ∀ j ≤ k, seeds j = other j) :
    primalError C s τ μ β D f field initial seeds k = primalError C s τ μ β D f field initial other k ∧
      dualError C s τ μ β D f field initial seeds k = dualError C s τ μ β D f field initial other k := by
  have hs := runState_prefix C s τ μ β D f field initial seeds other k (fun j hj => hprefix j hj.le)
  have hv := predicted_prefix C s τ μ β D f field initial seeds other k (fun j hj => hprefix j hj.le)
  have hi : indices C s τ μ β D f field initial seeds k = indices C s τ μ β D f field initial other k := by
    unfold indices
    rw [hs, hprefix k le_rfl]
  constructor
  · unfold primalError primalMean primalSample
    rw [hv, hi]
  · funext i
    unfold dualError dualSample dualMean
    rw [hv, hi]

lemma ghost_prefix (other : ℕ → StepSeed) (k : ℕ)
    (hprefix : ∀ j < k, seeds j = other j) :
    ghost C s τ μ β D f field initial seeds k = ghost C s τ μ β D f field initial other k := by
  apply weightedAuxiliary_prefix
  · intro j hj
    exact predicted_prefix C s τ μ β D f field initial seeds other j
      (fun n hn => hprefix n (lt_of_lt_of_le hn hj))
  · intro j hj
    exact (errors_prefix C s τ μ β D f field initial seeds other j
      (fun n hn => hprefix n (lt_of_le_of_lt hn hj))).1
  · intro j hj
    exact (errors_prefix C s τ μ β D f field initial seeds other j
      (fun n hn => hprefix n (lt_of_le_of_lt hn hj))).2

noncomputable def selection (k : ℕ) (h : Fin k → ι × ι) : StepSeed → ι × ι :=
  chosenIndices C s τ μ (stepSize β k)
    (historyState (initial, 0)
      (solverHistoryUpdate C (OracleTemplate.SaddlePoint.project C) s τ μ β D
        (fun q => (f q.1 q.2, field q.1 q.2))) k h).1

noncomputable def history (k : ℕ) : Fin k → ι × ι :=
  adaptiveHistory (selection C s τ μ β D f field initial) seeds k

lemma runState_of_history (k : ℕ) : runState C s τ μ β D f field initial seeds k =
    (historyState (initial, 0)
      (solverHistoryUpdate C (OracleTemplate.SaddlePoint.project C) s τ μ β D
        (fun q => (f q.1 q.2, field q.1 q.2))) k (history C s τ μ β D f field initial seeds k)).1 :=
  congrArg Prod.fst (solverState_history C (OracleTemplate.SaddlePoint.project C) s τ μ β D
    (fun q => (f q.1 q.2, field q.1 q.2)) initial seeds k)

lemma history_last (k : ℕ) : history C s τ μ β D f field initial seeds (k + 1) (Fin.last k) =
    indices C s τ μ β D f field initial seeds k := by
  unfold history
  rw [adaptiveHistory, Fin.snoc_last]
  unfold selection indices
  rw [runState_of_history]
  rfl

lemma history_restrict (j k : ℕ) (hjk : j ≤ k) :
    (fun i : Fin j => history C s τ μ β D f field initial seeds k (Fin.castLE hjk i)) =
      history C s τ μ β D f field initial seeds j :=
  adaptiveHistory_restrict _ seeds j k hjk

lemma history_eq_earlier (other : ℕ → StepSeed) (k : ℕ)
    (heq : history C s τ μ β D f field initial seeds k = history C s τ μ β D f field initial other k)
    (j : ℕ) (hjk : j ≤ k) :
    history C s τ μ β D f field initial seeds j = history C s τ μ β D f field initial other j := by
  have hh := congrArg (fun h : Fin k → ι × ι => fun i : Fin j => h (Fin.castLE hjk i)) heq
  simpa only [history_restrict] using hh

lemma runState_history_congr (other : ℕ → StepSeed) (k : ℕ)
    (heq : history C s τ μ β D f field initial seeds k = history C s τ μ β D f field initial other k) :
    runState C s τ μ β D f field initial seeds k = runState C s τ μ β D f field initial other k := by
  rw [runState_of_history, runState_of_history, heq]

lemma ghost_history_congr (other : ℕ → StepSeed) (k : ℕ)
    (heq : history C s τ μ β D f field initial seeds k = history C s τ μ β D f field initial other k) :
    ghost C s τ μ β D f field initial seeds k = ghost C s τ μ β D f field initial other k := by
  have hv (j : ℕ) (hj : j ≤ k) : predicted C s τ μ β D f field initial seeds j =
      predicted C s τ μ β D f field initial other j := by
    unfold predicted
    rw [runState_history_congr C s τ μ β D f field initial seeds other j
      (history_eq_earlier C s τ μ β D f field initial seeds other k heq j hj)]
  have hi (j : ℕ) (hj : j < k) : indices C s τ μ β D f field initial seeds j =
      indices C s τ μ β D f field initial other j := by
    have hh := congrFun (history_eq_earlier C s τ μ β D f field initial seeds other k heq
      (j + 1) (by omega)) (Fin.last j)
    simpa only [history_last] using hh
  apply weightedAuxiliary_prefix
  · exact hv
  · intro j hj
    unfold primalError primalMean primalSample
    rw [hv j hj.le, hi j hj]
  · intro j hj
    funext i
    unfold dualError dualSample dualMean
    rw [hv j hj.le, hi j hj]

lemma selection_measurable (k : ℕ) (h : Fin k → ι × ι) :
    Measurable (selection C s τ μ β D f field initial k h) :=
  chosenIndices_measurable _ _ _ _ _ _

open MeasureTheory in
lemma ghost_noise_integrable_zero [CompleteSpace E] (k : ℕ) :
    Integrable (fun ω => pairing (primalError C s τ μ β D f field initial ω k)
      (dualError C s τ μ β D f field initial ω k) (predicted C s τ μ β D f field initial ω k)
      (ghost C s τ μ β D f field initial ω k))
        (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume) ∧
    (∫ ω, pairing (primalError C s τ μ β D f field initial ω k)
      (dualError C s τ μ β D f field initial ω k) (predicted C s τ μ β D f field initial ω k)
      (ghost C s τ μ β D f field initial ω k)
        ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) = 0 := by
  let select := selection C s τ μ β D f field initial
  obtain ⟨decode, hd⟩ := history_observable_factor select k
    (fun ω => ghost C s τ μ β D f field initial ω k) initial
    (fun ω other heq => ghost_history_congr C s τ μ β D f field initial ω other k heq)
  let state := fun h : Fin k → ι × ι => (historyState (initial, 0)
    (solverHistoryUpdate C (OracleTemplate.SaddlePoint.project C) s τ μ β D
      (fun q => (f q.1 q.2, field q.1 q.2))) k h).1
  let v := fun h => predictor C s τ μ (stepSize β k) (state h)
  let g := fun h i => field i (v h).point - s.field i
  let r := fun h i => D - (f i (v h).point - affine s i (v h).point)
  let payoff := fun h (ij : ι × ι) => pairing
    ((∑ i, (v h).probability i • g h i) - g h ij.1)
    (fun i => r h i - coordinateReply ij.2 (r h ij.2) i) (v h) (decode h)
  have hz := adaptive_payoff_zero select (selection_measurable C s τ μ β D f field initial) k payoff
    ((volume : Measure unitInterval).prod volume)
    (fun h => noise_pairing_mean C s τ μ (stepSize β k) (state h) (decode h) (v h) (g h) (r h))
  have he (ω : ℕ → StepSeed) : pairing (primalError C s τ μ β D f field initial ω k)
      (dualError C s τ μ β D f field initial ω k) (predicted C s τ μ β D f field initial ω k)
      (ghost C s τ μ β D f field initial ω k) =
      payoff (adaptiveHistory select ω k) (select k (adaptiveHistory select ω k) (ω k)) := by
    unfold primalError primalMean primalSample dualError dualSample dualMean indices predicted
    rw [runState_of_history, hd ω]
    rfl
  constructor
  · simpa only [he] using adaptive_payoff_integrable select
      (selection_measurable C s τ μ β D f field initial) k payoff
      (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)
  · simpa only [he] using hz

lemma outputPlan_eq_average (N : ℕ) :
    OracleTemplate.ComponentEnvelope.Program.eval (fun q => (f q.1 q.2, field q.1 q.2))
      (outputPlan C (OracleTemplate.SaddlePoint.project C) s τ μ β D initial seeds N) =
      averageOutput β initial.point N (∑ k ∈ Finset.range N,
        iterationWeight β k • (predicted C s τ μ β D f field initial seeds k).point) := by
  rw [AffineResidualExecution.outputPlan_eval, AffineResidualExecution.solverState_sum]
  congr 1

lemma runState_zero : runState C s τ μ β D f field initial seeds 0 = initial := rfl

lemma runState_succ (k : ℕ) :
    runState C s τ μ β D f field initial seeds (k + 1) =
      correction (OracleTemplate.SaddlePoint.project C) s τ μ (stepSize β k)
        (runState C s τ μ β D f field initial seeds k) (predicted C s τ μ β D f field initial seeds k)
        (primalSample C s τ μ β D f field initial seeds k) (dualSample C s τ μ β D f field initial seeds k) := by
  rfl

lemma runState_valid (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hi : initial.point ∈ C) (hip : ∀ i, 0 < initial.probability i)
    (hisum : ∑ i, initial.probability i = 1) (k : ℕ) :
    let v := runState C s τ μ β D f field initial seeds k
    v.point ∈ C ∧ (∀ i, 0 < v.probability i) ∧ ∑ i, v.probability i = 1 :=
  solverState_valid hC hne hconv s τ μ β D (fun q => (f q.1 q.2, field q.1 q.2))
    initial hi hip hisum seeds k

lemma predicted_mem (hC : IsCompact C) (hne : C.Nonempty) (k : ℕ) :
    (predicted C s τ μ β D f field initial seeds k).point ∈ C :=
  (predictor_mem_min hC hne s τ μ (stepSize β k) _).1

lemma predicted_probability_pos (k : ℕ) (i : ι) :
    0 < (predicted C s τ μ β D f field initial seeds k).probability i :=
  predictor_probability_pos _ _ _ _ _ _ _

lemma predicted_probability_sum (k : ℕ) :
    (∑ i, (predicted C s τ μ β D f field initial seeds k).probability i) = 1 :=
  predictor_probability_sum _ _ _ _ _ _

lemma residual_bounds [CompleteSpace E] (hC : IsCompact C) (hne : C.Nonempty)
    {L r : ℝ} (hL : 0 ≤ L) (hD : D = L * r ^ 2 / 2)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖field i x - field i y‖ ≤ L * ‖x - y‖)
    (ha : s.anchor ∈ C) (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = field i s.anchor)
    (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r) (k : ℕ) :
    (∀ i, 0 ≤ dualMean C s τ μ β D f field initial seeds k i ∧
      dualMean C s τ μ β D f field initial seeds k i ≤ D) ∧
      ‖primalSample C s τ μ β D f field initial seeds k‖ ≤ L * r := by
  have hx := predicted_mem C s τ μ β D f field initial seeds hC hne k
  have hr (i : ι) := AffineResidualGap.snapshot_residual_bounds s f field hL hf hg hlip ha
    hvalue hfield hx (hradius _ hx) i
  refine ⟨?_, ?_⟩
  · intro i
    dsimp only [dualMean]
    constructor <;> linarith [(hr i).1.1, (hr i).1.2]
  · exact (hr (indices C s τ μ β D f field initial seeds k).1).2

lemma pathwise_gap [CompleteSpace E] (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hμ : 0 < μ) (hτ : 0 < τ) (hβ : 1 ≤ β) (hD : 0 ≤ D)
    (hcap : 4 * ((Fintype.card ι : ℝ) * D) ≤ β * τ)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hfield : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    (hi : initial.point ∈ C) (hip : ∀ i, 0 < initial.probability i)
    (hisum : ∑ i, initial.probability i = 1)
    (hres : ∀ k i, 0 ≤ dualMean C s τ μ β D f field initial seeds k i ∧
      dualMean C s τ μ β D f field initial seeds k i ≤ D)
    (N : ℕ) (u : State ι E) (hu : u ∈ kernelDomain C) :
    let v := predicted C s τ μ β D f field initial seeds
    let g := primalError C s τ μ β D f field initial seeds
    let b := dualError C s τ μ β D f field initial seeds
    let y := weightedAuxiliary C μ τ β initial v g b
    (∑ k ∈ Finset.range N, iterationWeight β k * AffineResidualGap.saddleGap f s.anchor μ τ (v k) u) ≤
      3 * β ^ 2 / 2 * potential μ τ u initial + ∑ k ∈ Finset.range N,
        ((4 / μ * ‖primalSample C s τ μ β D f field initial seeds k‖ ^ 2 +
          8 / τ * ∑ i, (v k).probability i * (dualSample C s τ μ β D f field initial seeds k i) ^ 2) +
          2 / μ * ‖g k‖ ^ 2 + 4 / τ * ∑ i, (y k).probability i * (b k i) ^ 2 +
            iterationWeight β k * pairing (g k) (b k) (v k) (y k)) := by
  have hs := runState_valid C s τ μ β D f field initial seeds hC hne hconv hi hip hisum
  have hβ' : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have ht := remove_noise_comparator hC hne hconv hμ hτ hβ
    (mul_nonneg (Nat.cast_nonneg _) hD) hcap
    (runState C s τ μ β D f field initial seeds) (predicted C s τ μ β D f field initial seeds)
    (fun k => (hs k).2.1) (fun k => (hs k).2.2)
    (predicted_probability_pos C s τ μ β D f field initial seeds)
    (predicted_probability_sum C s τ μ β D f field initial seeds)
    (primalError C s τ μ β D f field initial seeds) (dualError C s τ μ β D f field initial seeds)
    (fun k => AffineResidualGap.saddleGap f s.anchor μ τ (predicted C s τ μ β D f field initial seeds k) u)
    (fun k => 4 / μ * ‖primalSample C s τ μ β D f field initial seeds k‖ ^ 2 +
      8 / τ * ∑ i, (predicted C s τ μ β D f field initial seeds k).probability i *
        (dualSample C s τ μ β D f field initial seeds k i) ^ 2) N
    (fun k _ i => coordinateReply_centered_bound (hres k) hD
      (indices C s τ μ β D f field initial seeds k).2 i) hu
    (fun k _ => weighted_step_gap hC hne hconv s f field hf hfield hμ hτ hβ' D k
      (runState C s τ μ β D f field initial seeds k) (hs k).2.1 (hs k).2.2
      (primalSample C s τ μ β D f field initial seeds k)
      (dualSample C s τ μ β D f field initial seeds k)
      (fun i => (coordinateReply_bounds (hres k) hD
        (indices C s τ μ β D f field initial seeds k).2 i).1) u hu)
  exact ht

end LongTails.Proofs.AffineResidualTrajectory
