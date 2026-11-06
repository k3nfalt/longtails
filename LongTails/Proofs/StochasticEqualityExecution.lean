import LongTails.Algorithms.StochasticEquality
import LongTails.Proofs.StochasticEqualityGeometry
import LongTails.Proofs.MomentumSeparationInstance
import LongTails.Proofs.SampledQueryPlan
import LongTails.Proofs.StochasticQuasarCleanupExecution

namespace LongTails.Proofs.StochasticEqualityExecution

open OracleTemplate
open LongTails.Setups.StochasticRegularEqualities
open LongTails.Algorithms.StochasticEquality

lemma sampled_pair {Ω : Type*} (p : Public) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x : Point p.d) (offset : ℕ) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2)) (pairedSample p x) (2 * offset) =
      g x (ξ offset) := by
  simp only [pairedSample, QueryPlan.sampledEval]
  congr 2
  omega

lemma sampled_difference {Ω : Type*} (p : Public) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x y : Point p.d) (offset : ℕ) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2)) (pairedDifference p x y) (2 * offset) =
      g x (ξ offset) - g y (ξ offset) := by
  simp only [pairedDifference, QueryPlan.sampledEval]
  have h₀ : 2 * offset / 2 = offset := by omega
  have h₁ : (2 * offset + 1) / 2 = offset := by omega
  rw [h₀, h₁]

lemma sampled_mean {Ω : Type*} (p : Public) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x : Point p.d) (n offset : ℕ) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2))
      (meanPlan p n (pairedSample p x)) (2 * offset) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, g x (ξ (offset + i.val)) := by
  rw [meanPlan, QueryPlan.sampledEval_map, StochasticQuasar.sampled_collect_plans]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [show 2 * offset + 2 * i.val = 2 * (offset + i.val) by omega]
  exact sampled_pair p g ξ x (offset + i.val)

lemma sampled_mean_difference {Ω : Type*} (p : Public) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x y : Point p.d) (n offset : ℕ) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2))
      (meanPlan p n (pairedDifference p x y)) (2 * offset) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, (g x (ξ (offset + i.val)) - g y (ξ (offset + i.val))) := by
  rw [meanPlan, QueryPlan.sampledEval_map, StochasticQuasar.sampled_collect_plans]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [show 2 * offset + 2 * i.val = 2 * (offset + i.val) by omega]
  exact sampled_difference p g ξ x y (offset + i.val)

open LongTails.Algorithms.StochasticEnvelopeProgram

lemma restore_calls (cfg : Config) :
    restoreCalls cfg = 2 * cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps := by
  simp [restoreCalls, StochasticEnvelopeExecution.slotCalls_sum, restoreUnitCalls, Nat.mul_comm]

lemma training_calls (cfg : Config) :
    trainingCalls cfg = 2 * ∑ k ∈ Finset.range cfg.steps, batchSize cfg k := by
  simp [trainingCalls, StochasticEnvelopeExecution.slotCalls_sum, Finset.mul_sum]

lemma slot_calls_even (batch : ℕ → ℕ) (n slot : ℕ) :
    slotCalls (fun k => 2 * batch k) n slot =
      2 * ∑ i ∈ Finset.range n, batch (slot + i) := by
  simp [StochasticEnvelopeExecution.slotCalls_sum, Finset.mul_sum]

lemma total_calls (cfg : Config) :
    calls cfg = 2 * cfg.trials * (cfg.validationBatch * cfg.validationGroups +
      ∑ k ∈ Finset.range cfg.steps, batchSize cfg k +
      cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps) := by
  rw [calls, trialCalls, restore_calls, training_calls, validationCalls]
  ring

lemma sampled_robust {Ω : Type*} (p : Public) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x : Point p.d) (t : ℝ) (n k offset : ℕ) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2))
      (robustPlan p t n k x) (2 * offset) =
      let values := fun j : Fin k => (n : ℝ)⁻¹ •
        ∑ i : Fin n, g x (ξ (offset + n * j.val + i.val))
      (RobustGradient.pilotCenter (2 * t) (fun j => (values j).1),
        RobustGradient.pilotCenter (2 * t) (fun j => (values j).2.1),
        RobustGradient.pilotCenter (2 * t) (fun j => (values j).2.2)) := by
  rw [LongTails.Algorithms.StochasticEquality.robustPlan, QueryPlan.sampledEval_map, StochasticQuasar.sampled_collect_plans]
  have h (j : Fin k) : QueryPlan.sampledEval g (fun i => ξ (i / 2))
      (meanPlan p n (pairedSample p x)) (2 * offset + 2 * n * j.val) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, g x (ξ (offset + n * j.val + i.val)) := by
    rw [show 2 * offset + 2 * n * j.val = 2 * (offset + n * j.val) by ring]
    exact sampled_mean p g ξ x n _
  simp_rw [h]

lemma sampled_cast {Q R U Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)
    {n m : ℕ} (h : n = m) (q : QueryPlan Q R U n) (offset : ℕ) :
    QueryPlan.sampledEval g ξ (castPlan h q) offset = QueryPlan.sampledEval g ξ q offset := by
  subst m
  rfl

lemma sampled_estimator {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω)
    (k offset : ℕ) (s : TrainingState p) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2)) (estimatorPlan p cfg k s) (2 * offset) =
      if k % cfg.epoch = 0 then
        (cfg.resetBatch : ℝ)⁻¹ • ∑ i : Fin cfg.resetBatch, g s.point (ξ (offset + i.val))
      else s.estimate + (cfg.incrementBatch : ℝ)⁻¹ • ∑ i : Fin cfg.incrementBatch,
        (g s.point (ξ (offset + i.val)) - g s.previous (ξ (offset + i.val))) := by
  by_cases h : k % cfg.epoch = 0
  · simp only [estimatorPlan, h, ↓reduceDIte, ↓reduceIte, sampled_cast, sampled_mean]
  · simp only [estimatorPlan, h, ↓reduceDIte, ↓reduceIte, sampled_cast,
      QueryPlan.sampledEval_map, sampled_mean_difference]

lemma sampled_trials {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (seed : Seed cfg) (offset : ℕ) :
    QueryPlan.sampledEval g ξ (plan p cfg seed) offset =
      firstAccepted (p.x0, 0) (List.ofFn fun i : Fin cfg.trials =>
        QueryPlan.sampledEval g ξ (trialPlan p cfg (seed i)) (offset + trialCalls cfg * i.val)) := by
  simp only [plan, calls, QueryPlan.sampledEval_map, QueryPlan.sampledEval_traverse]

def trainingCore {p : Public} (s : TrainingState p) := (s.point, s.previous, s.estimate)

lemma estimator_core_congr (p : Public) (cfg : Config) (k : ℕ)
    (s t : TrainingState p) (h : trainingCore s = trainingCore t) :
    estimatorPlan p cfg k s = estimatorPlan p cfg k t := by
  obtain ⟨x, y, v, a⟩ := s
  obtain ⟨x', y', v', b⟩ := t
  simp only [trainingCore, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

lemma update_core_congr (p : Public) (cfg : Config) (k i j : ℕ)
    (s t : TrainingState p) (v : Reply p) (h : trainingCore s = trainingCore t) :
    trainingCore (trainingUpdate p cfg k i s v) =
      trainingCore (trainingUpdate p cfg k j t v) := by
  obtain ⟨x, y, w, a⟩ := s
  obtain ⟨x', y', w', b⟩ := t
  simp only [trainingCore, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

lemma training_core_independent {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (n slot call i j : ℕ)
    (s t : TrainingState p) (h : trainingCore s = trainingCore t) :
    trainingCore (QueryPlan.sampledEval g ξ
      (slotPlan (fun k => 2 * batchSize cfg k)
        (fun k u => (estimatorPlan p cfg k u).map (trainingUpdate p cfg k i u)) n slot s) call) =
    trainingCore (QueryPlan.sampledEval g ξ
      (slotPlan (fun k => 2 * batchSize cfg k)
        (fun k u => (estimatorPlan p cfg k u).map (trainingUpdate p cfg k j u)) n slot t) call) := by
  induction n generalizing slot call s t with
  | zero => exact h
  | succ n ih =>
    simp only [slotPlan, slotCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
    apply ih
    rw [estimator_core_congr p cfg slot s t h]
    exact update_core_congr p cfg slot i j s t _ h

lemma training_selected_preserved {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (n slot call index : ℕ)
    (s : TrainingState p) (hindex : index < slot) :
    (QueryPlan.sampledEval g ξ
      (slotPlan (fun k => 2 * batchSize cfg k)
        (fun k u => (estimatorPlan p cfg k u).map (trainingUpdate p cfg k index u))
          n slot s) call).selected = s.selected := by
  induction n generalizing slot call s with
  | zero => rfl
  | succ n ih =>
    simp only [slotPlan, slotCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
    rw [ih (slot + 1) _ _ (by omega)]
    simp [trainingUpdate, show slot ≠ index by omega]

lemma sampled_slot_zero {Q R U Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)
    (cost : ℕ → ℕ) (step : (k : ℕ) → U → QueryPlan Q R U (cost k))
    (n slot call : ℕ) (s : U) (hn : n = 0) :
    QueryPlan.sampledEval g ξ (slotPlan cost step n slot s) call = s := by
  subst n
  rfl

lemma training_selected_prefix {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (n slot call index : ℕ)
    (s : TrainingState p) (hlo : slot ≤ index) (hhi : index < slot + n) :
    (QueryPlan.sampledEval g ξ
      (slotPlan (fun k => 2 * batchSize cfg k)
        (fun k u => (estimatorPlan p cfg k u).map (trainingUpdate p cfg k index u))
          n slot s) call).selected =
    (QueryPlan.sampledEval g ξ
      (slotPlan (fun k => 2 * batchSize cfg k)
        (fun k u => (estimatorPlan p cfg k u).map (trainingUpdate p cfg k index u))
          (index - slot) slot s) call).point := by
  induction n generalizing slot call s with
  | zero => omega
  | succ n ih =>
    by_cases he : index = slot
    · subst index
      simp only [slotPlan, slotCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
      rw [training_selected_preserved p cfg g ξ n (slot + 1) _ slot _ (by omega)]
      rw [sampled_slot_zero g ξ _ _ _ slot call s (Nat.sub_self slot)]
      simp [trainingUpdate]
    · have hsub : index - slot = (index - (slot + 1)) + 1 := by omega
      conv_rhs => rw [hsub]
      simp only [slotPlan, slotCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
      exact ih (slot + 1) _ _ (by omega) (by omega)

lemma training_output_prefix {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (index : Fin cfg.steps)
    (x : Point p.d) (call : ℕ) :
    QueryPlan.sampledEval g ξ (trainingPlan p cfg index x) call =
    (QueryPlan.sampledEval g ξ
      (slotPlan (fun k => 2 * batchSize cfg k)
        (fun k u => (estimatorPlan p cfg k u).map (trainingUpdate p cfg k 0 u))
          index 0 { point := x, previous := x, estimate := 0, selected := x }) call).point := by
  simp only [trainingPlan, trainingPrefixPlan, trainingCalls, QueryPlan.sampledEval_map]
  rw [training_selected_prefix p cfg g ξ cfg.steps 0 call index _ (by omega)
    (by simp)]
  simp only [Nat.sub_zero]
  exact congrArg Prod.fst (training_core_independent p cfg g ξ index 0 call index 0 _ _ rfl)

lemma paired_prefix_congr {Q R U Ω : Type*} (g : Q → Ω → R)
    (ξ ζ : ℕ → Ω) {n : ℕ} (q : QueryPlan Q R U (2 * n)) (offset : ℕ)
    (h : ∀ i, i < offset + n → ξ i = ζ i) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2)) q (2 * offset) =
      QueryPlan.sampledEval g (fun i => ζ (i / 2)) q (2 * offset) := by
  simp_rw [StochasticQuasar.sampled_eval_eq_indexed]
  apply StochasticEnvelopeExecution.evalAt_prefix_congr
  intro j hj x
  congr 1
  exact h _ (by omega)

lemma clipped_jacobian_norm (p : Public) (hL : 0 ≤ p.Lc) (v : Reply p) :
    ‖LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc v.2.2)‖ ≤ p.Lc := by
  exact (MomentumSeparationInstance.spectralNorm_le_norm _).trans (norm_clip_le hL _)

lemma restore_displacement (p : Public) (cfg : Config) (hL : 0 ≤ p.Lc)
    (hM : 0 ≤ cfg.restoreCap) (hη : 0 ≤ cfg.restoreStep) (x : Point p.d) (v : Reply p) :
    ‖restoreUpdate p cfg x v - x‖ ≤ cfg.restoreStep * p.Lc * cfg.restoreCap := by
  unfold restoreUpdate
  rw [show x - cfg.restoreStep • (LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m
      (clip p.Lc v.2.2) (clip cfg.restoreCap v.2.1)) - x =
      -(cfg.restoreStep • (LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m
      (clip p.Lc v.2.2) (clip cfg.restoreCap v.2.1))) by abel]
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hη
  exact ((LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc v.2.2)).le_opNorm _).trans
    (mul_le_mul (clipped_jacobian_norm p hL v) (norm_clip_le hM _) (norm_nonneg _) hL)

lemma training_displacement (p : Public) (cfg : Config) (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (k index : ℕ) (s : TrainingState p) (v : Reply p) :
    ‖(trainingUpdate p cfg k index s v).point - s.point‖ ≤
      cfg.step * (cfg.gradientCap + p.Lc * cfg.constraintCap) := by
  simp only [trainingUpdate, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
  apply mul_le_mul_of_nonneg_left _ hη
  exact (StochasticEqualityGeometry.norm_direction_le p.ν hν _ _ _).trans
    (add_le_add (norm_clip_le hG _) (mul_le_mul (clipped_jacobian_norm p hL v)
      (norm_clip_le hM _) (norm_nonneg _) hL))

lemma sampled_slot_displacement {E Q R U Ω : Type*} [NormedAddCommGroup E]
    (g : Q → Ω → R) (ξ : ℕ → Ω) (cost : ℕ → ℕ)
    (step : (k : ℕ) → U → QueryPlan Q R U (cost k)) (view : U → E) (D : ℝ)
    (hstep : ∀ k x call, ‖view (QueryPlan.sampledEval g ξ (step k x) call) - view x‖ ≤ D)
    (n slot call : ℕ) (x : U) :
    ‖view (QueryPlan.sampledEval g ξ (slotPlan cost step n slot x) call) - view x‖ ≤ n * D := by
  induction n generalizing slot call x with
  | zero => simp [slotPlan, QueryPlan.sampledEval]
  | succ n ih =>
    simp only [slotPlan, slotCalls, QueryPlan.sampledEval_bind]
    set y := QueryPlan.sampledEval g ξ (step slot x) call
    have ht := dist_triangle
      (view (QueryPlan.sampledEval g ξ (slotPlan cost step n (slot + 1) y) (call + cost slot)))
      (view y) (view x)
    simp only [dist_eq_norm] at ht
    have hb := ih (slot + 1) (call + cost slot) y
    have hs := hstep slot x call
    change ‖view y - view x‖ ≤ D at hs
    push_cast
    linarith

lemma restoration_path_bound {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (call : ℕ)
    (hL : 0 ≤ p.Lc) (hM : 0 ≤ cfg.restoreCap) (hη : 0 ≤ cfg.restoreStep) :
    ‖QueryPlan.sampledEval g ξ (restorePlan p cfg) call - p.x0‖ ≤
      (cfg.restoreSteps : ℝ) * (cfg.restoreStep * p.Lc * cfg.restoreCap) := by
  apply sampled_slot_displacement g ξ (fun _ => restoreUnitCalls cfg) _ id _ _ cfg.restoreSteps 0 call p.x0
  intro k x offset
  change ‖QueryPlan.sampledEval g ξ
    ((LongTails.Algorithms.StochasticEquality.robustPlan p cfg.restoreTolerance
      cfg.restoreBatch cfg.restoreGroups x).map (restoreUpdate p cfg x)) offset - x‖ ≤ _
  rw [QueryPlan.sampledEval_map]
  exact restore_displacement p cfg hL hM hη x _

lemma training_path_bound {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (index : Fin cfg.steps)
    (x : Point p.d) (call : ℕ) (hν : 0 < p.ν) (hL : 0 ≤ p.Lc)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step) :
    ‖QueryPlan.sampledEval g ξ (trainingPlan p cfg index x) call - x‖ ≤
      (index : ℝ) * (cfg.step * (cfg.gradientCap + p.Lc * cfg.constraintCap)) := by
  rw [training_output_prefix]
  apply sampled_slot_displacement g ξ (fun k => 2 * batchSize cfg k) _ TrainingState.point _ _
    index 0 call ⟨x, x, 0, x⟩
  intro k s offset
  rw [QueryPlan.sampledEval_map]
  exact training_displacement p cfg hν hL hG hM hη k 0 s _

lemma validate_properties (p : Public) (cfg : Config) (hν : 0 < p.ν)
    (hG : 0 ≤ cfg.gradientCap) (x : Point p.d) (v : Reply p) (y : Point p.d × Point p.m)
    (hy : validate p cfg x v = some y) : y.1 = x ∧ ‖y.2‖ ≤ 2 * cfg.gradientCap / p.ν := by
  classical
  unfold validate at hy
  dsimp only at hy
  split_ifs at hy with h
  · cases Option.some.inj hy
    refine ⟨rfl, ?_⟩
    exact (StochasticEqualityGeometry.norm_thresholdedMultiplier_le p.ν hν _ _).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_clip_le hG _) (by norm_num)) hν.le)

lemma firstAccepted_mem_or_fallback (p : Public) (fallback : Point p.d × Point p.m)
    (values : List (Option (Point p.d × Point p.m))) :
    firstAccepted fallback values = fallback ∨ some (firstAccepted fallback values) ∈ values := by
  induction values with
  | nil => exact Or.inl rfl
  | cons value values ih =>
    cases value with
    | none =>
      rcases ih with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    | some value => exact Or.inr List.mem_cons_self

lemma firstAccepted_mem (p : Public) (fallback : Point p.d × Point p.m)
    (values : List (Option (Point p.d × Point p.m)))
    (h : ∃ y, some y ∈ values) : some (firstAccepted fallback values) ∈ values := by
  induction values with
  | nil => simp at h
  | cons value values ih =>
    cases value with
    | none =>
      apply List.mem_cons_of_mem
      apply ih
      simpa using h
    | some value => exact List.mem_cons_self

lemma sampled_selected_trial {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (seed : Seed cfg)
    (h : ¬ ∀ i : Fin cfg.trials,
      QueryPlan.sampledEval g ξ (trialPlan p cfg (seed i)) (trialCalls cfg * i.val) = none) :
    ∃ i : Fin cfg.trials,
      QueryPlan.sampledEval g ξ (trialPlan p cfg (seed i)) (trialCalls cfg * i.val) =
        some (QueryPlan.sampledEval g ξ (plan p cfg seed) 0) := by
  classical
  push Not at h
  obtain ⟨i, hi⟩ := h
  have hex : ∃ y, some y ∈ List.ofFn (fun i : Fin cfg.trials =>
      QueryPlan.sampledEval g ξ (trialPlan p cfg (seed i)) (trialCalls cfg * i.val)) := by
    cases he : QueryPlan.sampledEval g ξ (trialPlan p cfg (seed i)) (trialCalls cfg * i.val) with
    | none => exact (hi he).elim
    | some y => exact ⟨y, List.mem_ofFn.mpr ⟨i, he⟩⟩
  have hm := firstAccepted_mem p (p.x0, 0) _ hex
  rw [sampled_trials]
  simpa only [Nat.zero_add, List.mem_ofFn] using hm

lemma sampled_slot_succ_end {Q R U Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)
    (cost : ℕ → ℕ) (step : (k : ℕ) → U → QueryPlan Q R U (cost k))
    (n slot call : ℕ) (s : U) :
    QueryPlan.sampledEval g ξ (slotPlan cost step (n + 1) slot s) call =
      QueryPlan.sampledEval g ξ
        (step (slot + n) (QueryPlan.sampledEval g ξ (slotPlan cost step n slot s) call))
        (call + slotCalls cost n slot) := by
  have hstart (n slot call : ℕ) (s : U) :
      QueryPlan.sampledEval g ξ (slotPlan cost step (n + 1) slot s) call =
        QueryPlan.sampledEval g ξ (slotPlan cost step n (slot + 1)
          (QueryPlan.sampledEval g ξ (step slot s) call)) (call + cost slot) :=
    QueryPlan.sampledEval_bind g ξ (step slot s) (slotPlan cost step n (slot + 1)) call
  induction n generalizing slot call s with
  | zero => simp [slotPlan, slotCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval]
  | succ n ih =>
    rw [hstart (n + 1), ih, hstart n]
    simp only [slotCalls]
    simp only [Nat.add_assoc, Nat.add_comm]
    exact congrArg (fun k => QueryPlan.sampledEval g ξ
      (step k (QueryPlan.sampledEval g ξ
        (slotPlan cost step n (slot + 1) (QueryPlan.sampledEval g ξ (step slot s) call))
        (call + cost slot))) (call + (cost slot + slotCalls cost n (slot + 1))))
      (by omega : slot + 1 + n = slot + (n + 1))

lemma execute_eq {Ω : Type} [MeasurableSpace Ω] (p : Public)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Reply p)
    (seed : Seed (tuning p)) (ξ : ℕ → Ω) (K : ℕ) (hK : calls (tuning p) ≤ K) :
    output p { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) w => g x w } K seed ξ =
      QueryPlan.sampledEval g ξ (plan p (tuning p) seed) 0 := by
  exact QueryPlan.execute_sampledPlan_of_le _ P p.x0 (p.x0, 0) _ K _ g seed ξ hK

lemma paired_sampled_shift {Q R U Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)
    {k : ℕ} (q : QueryPlan Q R U k) (offset : ℕ) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2)) q (2 * offset) =
      QueryPlan.sampledEval g (fun i => ξ (offset + i / 2)) q 0 := by
  simp only [StochasticQuasar.sampled_eval_eq_indexed]
  have hh := StochasticEnvelopeExecution.evalAt_shift (fun j x => g x (ξ (j / 2))) q (2 * offset) 0
  rw [Nat.add_zero] at hh
  have he (j : ℕ) : (2 * offset + j) / 2 = offset + j / 2 := by omega
  simpa only [he] using hh.symm

lemma paired_interval_congr {Q R U Ω : Type*} (g : Q → Ω → R)
    (ξ ζ : ℕ → Ω) {n : ℕ} (q : QueryPlan Q R U (2 * n)) (offset : ℕ)
    (h : ∀ i, offset ≤ i → i < offset + n → ξ i = ζ i) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2)) q (2 * offset) =
      QueryPlan.sampledEval g (fun i => ζ (i / 2)) q (2 * offset) := by
  rw [paired_sampled_shift, paired_sampled_shift]
  apply paired_prefix_congr g (fun i => ξ (offset + i)) (fun i => ζ (offset + i)) q 0
  intro i hi
  apply h
  · omega
  · omega


lemma trial_calls (cfg : Config) : trialCalls cfg = 2 * trialSamples cfg := by
  rw [trialCalls, restore_calls, training_calls, validationCalls]
  unfold trialSamples
  ring

lemma trial_samples_pos (cfg : Config) : 0 < trialSamples cfg := by
  have hh := Nat.mul_pos cfg.validationBatch.pos cfg.validationGroups.pos
  unfold trialSamples
  omega


end LongTails.Proofs.StochasticEqualityExecution
