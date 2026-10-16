import LongTails.Algorithms.ClippedTwoPointWork
import LongTails.Proofs.SampledQueryPlan
import LongTails.Proofs.ClippedTwoPointExecution

namespace LongTails.Proofs.ClippedTwoPointWork

open LongTails.Algorithms.ClippedTwoPointWork

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma clipped_scalar_value (τ x : ℝ) : (clippedScalar τ x).value = OracleTemplate.clip τ x := by
  by_cases hx : |x| ≤ τ
  · simp [clippedScalar, Bind.bind, Pure.pure, bindWork, realNorm, realLe,
      pureWork, OracleTemplate.clip, Real.norm_eq_abs, hx]
  · simp [clippedScalar, Bind.bind, bindWork, realNorm, realLe, realDiv, realMul,
      OracleTemplate.clip, Real.norm_eq_abs, hx, smul_eq_mul]

lemma clipped_scalar_cost (τ x : ℝ) :
    (clippedScalar τ x).cost.operations ≤ 4 ∧ (clippedScalar τ x).cost.projections = 0 ∧
      (clippedScalar τ x).cost.queries = 0 ∧ (clippedScalar τ x).cost.directions = 0 := by
  by_cases hx : |x| ≤ τ <;>
    simp [clippedScalar, Bind.bind, Pure.pure, bindWork, realNorm, realLe, realDiv, realMul,
      pureWork, Cost.add, Real.norm_eq_abs, hx]

lemma mix_value (t : ℕ) (x z : E) :
    (mix t x z).value = LongTails.Algorithms.ClippedTwoPoint.acceleratedMix t x z := rfl

lemma mix_cost (t : ℕ) (x z : E) : (mix t x z).cost = ⟨7, 0, 0, 0⟩ := rfl

lemma update_value (project : E → E) (h : ℝ) (t : ℕ) (state : E × E) (g : E) :
    (update project h t state g).value =
      LongTails.Algorithms.ClippedTwoPoint.acceleratedUpdate project h t state g := rfl

lemma update_cost (project : E → E) (h : ℝ) (t : ℕ) (state : E × E) (g : E) :
    (update project h t state g).cost = ⟨13, 1, 0, 0⟩ := rfl

lemma estimator_value (d : ℕ) (τ γ : ℝ) (u : E) (plus minus : ℝ) :
    (estimator d τ γ u plus minus).value =
      LongTails.Algorithms.ClippedTwoPoint.estimate d τ γ u plus minus := by
  change ((d : ℝ) * (clippedScalar τ ((plus - minus) / (2 * γ))).value) • u = _
  rw [clipped_scalar_value]
  rfl

lemma estimator_cost (d : ℕ) (τ γ : ℝ) (u : E) (plus minus : ℝ) :
    (estimator d τ γ u plus minus).cost.operations ≤ 10 ∧
      (estimator d τ γ u plus minus).cost.projections = 0 ∧
      (estimator d τ γ u plus minus).cost.queries = 0 ∧
      (estimator d τ γ u plus minus).cost.directions = 0 := by
  obtain ⟨ho, hp, hq, hd⟩ := clipped_scalar_cost τ ((plus - minus) / (2 * γ))
  change (1 + (1 + (1 + ((clippedScalar τ ((plus - minus) / (2 * γ))).cost.operations + 3)))) ≤ 10 ∧ _
  constructor
  · omega
  · simp only [estimator, Bind.bind, bindWork, realSub, realMul, realDiv, natReal, vectorScale, Cost.add, hp, hq, hd,
      Nat.add_zero, and_self]

lemma paired_call_value (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) (index call : ℕ) :
    (pairedCall d τ γ x seed reply index call).value =
      LongTails.Algorithms.ClippedTwoPoint.estimate d τ γ (seed index)
        (reply call (x + γ • seed index)) (reply (call + 1) (x - γ • seed index)) := by
  dsimp only [pairedCall, Bind.bind, bindWork, direction, vectorScale, vectorAdd, vectorSub, query, natAdd]
  exact estimator_value d τ γ (seed index) _ _

lemma paired_call_cost (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) (index call : ℕ) :
    (pairedCall d τ γ x seed reply index call).cost.operations ≤ 17 ∧
      (pairedCall d τ γ x seed reply index call).cost.projections = 0 ∧
      (pairedCall d τ γ x seed reply index call).cost.queries = 2 ∧
      (pairedCall d τ γ x seed reply index call).cost.directions = 1 := by
  obtain ⟨ho, hp, hq, hd⟩ := estimator_cost d τ γ (seed index)
    (reply call (x + γ • seed index)) (reply (call + 1) (x - γ • seed index))
  dsimp only [pairedCall, Bind.bind, bindWork, direction, vectorScale, vectorAdd, vectorSub, query, natAdd, Cost.add]
  constructor
  · omega
  · simp only [hp, hq, hd, Nat.zero_add, Nat.add_zero, and_self]

lemma sum_pairs_cost (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) (B index call : ℕ) :
    (sumPairs d τ γ x seed reply B index call).cost.operations ≤ 20 * B ∧
      (sumPairs d τ γ x seed reply B index call).cost.projections = 0 ∧
      (sumPairs d τ γ x seed reply B index call).cost.queries = 2 * B ∧
      (sumPairs d τ γ x seed reply B index call).cost.directions = B := by
  induction B generalizing index call with
  | zero => simp [sumPairs, Pure.pure, pureWork]
  | succ B ih =>
    obtain ⟨ho, hp, hq, hd⟩ := paired_call_cost d τ γ x seed reply index call
    obtain ⟨io, ip, iq, id⟩ := ih (index + 1) (call + 2)
    dsimp only [sumPairs, Bind.bind, bindWork, natAdd, vectorAdd, Cost.add]
    constructor
    · omega
    · simp only [hp, hq, hd, ip, iq, id, Nat.zero_add, Nat.add_zero, true_and]
      constructor <;> omega

lemma sum_pairs_value (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) (B index call : ℕ) :
    (sumPairs d τ γ x seed reply B index call).value =
      ∑ i : Fin B, LongTails.Algorithms.ClippedTwoPoint.estimate d τ γ (seed (index + i))
        (reply (call + 2 * i) (x + γ • seed (index + i)))
        (reply (call + 2 * i + 1) (x - γ • seed (index + i))) := by
  induction B generalizing index call with
  | zero => simp [sumPairs, Pure.pure, pureWork]
  | succ B ih =>
    dsimp only [sumPairs, Bind.bind, bindWork, natAdd, vectorAdd]
    rw [paired_call_value, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Nat.mul_zero, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma averaged_batch_cost (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) (B index call : ℕ) :
    (averagedBatch d τ γ x seed reply B index call).cost.operations ≤ 20 * B + 3 ∧
      (averagedBatch d τ γ x seed reply B index call).cost.projections = 0 ∧
      (averagedBatch d τ γ x seed reply B index call).cost.queries = 2 * B ∧
      (averagedBatch d τ γ x seed reply B index call).cost.directions = B := by
  obtain ⟨ho, hp, hq, hd⟩ := sum_pairs_cost d τ γ x seed reply B index call
  dsimp only [averagedBatch, Bind.bind, bindWork, natReal, realDiv, vectorScale, Cost.add]
  constructor
  · omega
  · simp [hp, hq, hd]

lemma averaged_batch_value (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) (B index call : ℕ) :
    (averagedBatch d τ γ x seed reply B index call).value =
      OracleTemplate.QueryPlan.sampledEval (fun x k => reply k x) id
        (LongTails.Algorithms.ClippedTwoPoint.batchPlan d τ γ x
          (fun i : Fin B => seed (index + i))) call := by
  dsimp only [averagedBatch, Bind.bind, bindWork, natReal, realDiv, vectorScale]
  rw [sum_pairs_value]
  simp only [LongTails.Algorithms.ClippedTwoPoint.batchPlan,
    OracleTemplate.QueryPlan.sampledEval_map, OracleTemplate.QueryPlan.sampledEval_traverse,
    List.sum_ofFn, LongTails.Algorithms.ClippedTwoPoint.pairPlan,
    OracleTemplate.QueryPlan.sampledEval, id_eq, one_div]

lemma round_cost (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (t : ℕ) (state : E × E) (seed : ℕ → E) (reply : ℕ → E → ℝ)
    (B index call : ℕ) :
    (round d τ γ h project t state seed reply B index call).cost.operations ≤ 20 * B + 23 ∧
      (round d τ γ h project t state seed reply B index call).cost.projections = 1 ∧
      (round d τ γ h project t state seed reply B index call).cost.queries = 2 * B ∧
      (round d τ γ h project t state seed reply B index call).cost.directions = B := by
  obtain ⟨ho, hp, hq, hd⟩ := averaged_batch_cost d τ γ (mix t state.1 state.2).value
    seed reply B index call
  dsimp only [LongTails.Algorithms.ClippedTwoPointWork.round, Bind.bind, bindWork]
  rw [mix_cost, update_cost]
  dsimp only [Cost.add]
  constructor
  · omega
  · simp [hp, hq, hd]

lemma round_value (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (t : ℕ) (state : E × E) (seed : ℕ → E) (reply : ℕ → E → ℝ)
    (B index call : ℕ) :
    (round d τ γ h project t state seed reply B index call).value =
      OracleTemplate.QueryPlan.sampledEval (fun x k => reply k x) id
        (LongTails.Algorithms.ClippedTwoPoint.roundPlan d τ γ h project t state
          (fun i : Fin B => seed (index + i))) call := by
  dsimp only [LongTails.Algorithms.ClippedTwoPointWork.round, Bind.bind, bindWork]
  rw [update_value, averaged_batch_value, mix_value]
  exact (OracleTemplate.QueryPlan.sampledEval_map _ _ _ _ _).symm

lemma batch_count_value (T : ℕ) (A : ℝ) (t : ℕ) :
    (batchCount T A t).value =
      LongTails.Algorithms.ClippedTwoPoint.batchSize T A (t + 1) := rfl

lemma batch_count_cost (T : ℕ) (A : ℝ) (t : ℕ) :
    (batchCount T A t).cost = ⟨6, 0, 0, 0⟩ := rfl

lemma dual_round_cost (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (t B : ℕ) (old : Registers E) (seed : ℕ → E) (reply : ℕ → E → ℝ) :
    (dualRound d τ₁ τ₂ γ₁ γ₂ h project t B old seed reply).cost.operations ≤ 40 * B + 51 ∧
      (dualRound d τ₁ τ₂ γ₁ γ₂ h project t B old seed reply).cost.projections = 2 ∧
      (dualRound d τ₁ τ₂ γ₁ γ₂ h project t B old seed reply).cost.queries = 4 * B ∧
      (dualRound d τ₁ τ₂ γ₁ γ₂ h project t B old seed reply).cost.directions = 2 * B := by
  obtain ⟨ho, hp, hq, hd⟩ := round_cost d τ₁ γ₁ h project t old.states.1 seed reply
    B old.index old.call
  obtain ⟨io, ip, iq, id⟩ := round_cost d τ₂ γ₂ h project t old.states.2 seed reply
    B (old.index + B) (old.call + 2 * B)
  dsimp only [dualRound, Bind.bind, Pure.pure, bindWork, pureWork, natAdd, natMul, Cost.add]
  constructor
  · omega
  · simp only [hp, hq, hd, ip, iq, id, Nat.add_zero, Nat.zero_add, true_and]
    constructor <;> omega

lemma dual_round_offsets (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (t B : ℕ) (old : Registers E) (seed : ℕ → E) (reply : ℕ → E → ℝ) :
    (dualRound d τ₁ τ₂ γ₁ γ₂ h project t B old seed reply).value.index = old.index + 2 * B ∧
      (dualRound d τ₁ τ₂ γ₁ γ₂ h project t B old seed reply).value.call = old.call + 4 * B := by
  dsimp only [dualRound, Bind.bind, Pure.pure, bindWork, pureWork, natAdd, natMul]
  constructor <;> omega

lemma dual_round_value (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (t B : ℕ) (old : Registers E) (seed : ℕ → E) (reply : ℕ → E → ℝ) :
    (dualRound d τ₁ τ₂ γ₁ γ₂ h project t B old seed reply).value.states =
      (OracleTemplate.QueryPlan.sampledEval (fun x k => reply k x) id
        (LongTails.Algorithms.ClippedTwoPoint.roundPlan d τ₁ γ₁ h project t old.states.1
          (fun i : Fin B => seed (old.index + i))) old.call,
       OracleTemplate.QueryPlan.sampledEval (fun x k => reply k x) id
        (LongTails.Algorithms.ClippedTwoPoint.roundPlan d τ₂ γ₂ h project t old.states.2
          (fun i : Fin B => seed (old.index + B + i))) (old.call + 2 * B)) := by
  dsimp only [dualRound, Bind.bind, Pure.pure, bindWork, pureWork, natAdd, natMul]
  rw [round_value, round_value]

lemma dual_run_cost (d T : ℕ) (A τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (initial : Registers E) (seed : ℕ → E) (reply : ℕ → E → ℝ) (n : ℕ) :
    (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n).cost.operations ≤
        40 * (∑ j ∈ Finset.range n, (batchCount T A j).value) + 57 * n ∧
      (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n).cost.projections = 2 * n ∧
      (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n).cost.queries =
        4 * ∑ j ∈ Finset.range n, (batchCount T A j).value ∧
      (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n).cost.directions =
        2 * ∑ j ∈ Finset.range n, (batchCount T A j).value := by
  induction n with
  | zero => simp [dualRun, Pure.pure, pureWork]
  | succ n ih =>
    obtain ⟨io, ip, iq, id⟩ := ih
    obtain ⟨ho, hp, hq, hd⟩ := dual_round_cost d τ₁ τ₂ γ₁ γ₂ h project n
      (batchCount T A n).value
      (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n).value seed reply
    dsimp only [dualRun, Bind.bind, bindWork]
    rw [batch_count_cost]
    dsimp only [Cost.add]
    simp only [Finset.sum_range_succ]
    constructor
    · omega
    · simp only [ip, iq, id, hp, hq, hd, Nat.zero_add]
      constructor
      · omega
      · constructor <;> omega

lemma dual_run_offsets (d T : ℕ) (A τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (initial : Registers E) (seed : ℕ → E) (reply : ℕ → E → ℝ) (n : ℕ) :
    (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n).value.index =
        initial.index + 2 * ∑ j ∈ Finset.range n, (batchCount T A j).value ∧
      (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n).value.call =
        initial.call + 4 * ∑ j ∈ Finset.range n, (batchCount T A j).value := by
  induction n with
  | zero => simp [dualRun, Pure.pure, pureWork]
  | succ n ih =>
    obtain ⟨hi, hc⟩ := dual_round_offsets d τ₁ τ₂ γ₁ γ₂ h project n
      (batchCount T A n).value
      (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n).value seed reply
    dsimp only [dualRun, Bind.bind, bindWork]
    rw [hi, hc, ih.1, ih.2]
    simp only [Finset.sum_range_succ]
    constructor <;> omega

lemma dual_run_value (d T : ℕ) (A τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (initial : E × E) (seed : ℕ → E) (reply : ℕ → E → ℝ) (index call n : ℕ)
    (B : ℕ → ℕ) (hB : ∀ t, B t = (batchCount T A t).value) :
    (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project ⟨(initial, initial), index, call⟩ seed reply n).value.states =
      OracleTemplate.QueryPlan.sampledEval (fun x k => reply k x) id
        (LongTails.Algorithms.ClippedTwoPoint.dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B
          (fun t i => seed (index + 2 * (∑ j ∈ Finset.range t, B j) + i))
          (fun t i => seed (index + 2 * (∑ j ∈ Finset.range t, B j) + B t + i)) n) call := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hi, hc⟩ := dual_run_offsets d T A τ₁ τ₂ γ₁ γ₂ h project
      ⟨(initial, initial), index, call⟩ seed reply n
    simp only [← hB] at hi hc
    change (dualRound d τ₁ τ₂ γ₁ γ₂ h project n (batchCount T A n).value
      (dualRun d T A τ₁ τ₂ γ₁ γ₂ h project ⟨(initial, initial), index, call⟩ seed reply n).value
      seed reply).value.states =
      OracleTemplate.QueryPlan.sampledEval (fun x k => reply k x) id
        ((LongTails.Algorithms.ClippedTwoPoint.dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B
          (fun t i => seed (index + 2 * (∑ j ∈ Finset.range t, B j) + i))
          (fun t i => seed (index + 2 * (∑ j ∈ Finset.range t, B j) + B t + i)) n).bind
          (fun states => (LongTails.Algorithms.ClippedTwoPoint.roundPlan d τ₁ γ₁ h project n states.1
            (fun i : Fin (B n) => seed (index + 2 * (∑ j ∈ Finset.range n, B j) + i))).bind
            (fun first => (LongTails.Algorithms.ClippedTwoPoint.roundPlan d τ₂ γ₂ h project n states.2
              (fun i : Fin (B n) => seed (index + 2 * (∑ j ∈ Finset.range n, B j) + B n + i))).map
              (fun second => (first, second))))) call
    rw [dual_round_value, ← hB n, hi, hc, ih,
      OracleTemplate.QueryPlan.sampledEval_bind,
      OracleTemplate.QueryPlan.sampledEval_bind, OracleTemplate.QueryPlan.sampledEval_map]
    rw [show call + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls B n =
      call + 4 * (∑ j ∈ Finset.range n, B j) by
        rw [LongTails.Proofs.ClippedTwoPointExecution.dual_solver_calls_sum]]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma comparison_pair_cost (s : ℝ) (a b : E) (reply : ℕ → E → ℝ) (call : ℕ) :
    (comparisonPair s a b reply call).cost.operations ≤ 8 ∧
      (comparisonPair s a b reply call).cost.projections = 0 ∧
      (comparisonPair s a b reply call).cost.queries = 2 ∧
      (comparisonPair s a b reply call).cost.directions = 0 := by
  obtain ⟨ho, hp, hq, hd⟩ := clipped_scalar_cost s (reply call a - reply (call + 1) b)
  dsimp only [comparisonPair, Bind.bind, bindWork, query, natAdd, realSub, Cost.add]
  constructor
  · omega
  · simp [hp, hq, hd]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma comparison_pair_value (s : ℝ) (a b : E) (reply : ℕ → E → ℝ) (call : ℕ) :
    (comparisonPair s a b reply call).value =
      OracleTemplate.clip s (reply call a - reply (call + 1) b) := by
  dsimp only [comparisonPair, Bind.bind, bindWork, query, natAdd, realSub]
  exact clipped_scalar_value _ _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma comparison_sum_cost (s : ℝ) (a b : E) (reply : ℕ → E → ℝ) (T call : ℕ) :
    (comparisonSum s a b reply T call).cost.operations ≤ 10 * T ∧
      (comparisonSum s a b reply T call).cost.projections = 0 ∧
      (comparisonSum s a b reply T call).cost.queries = 2 * T ∧
      (comparisonSum s a b reply T call).cost.directions = 0 := by
  induction T generalizing call with
  | zero => simp [comparisonSum, Pure.pure, pureWork]
  | succ T ih =>
    obtain ⟨ho, hp, hq, hd⟩ := comparison_pair_cost s a b reply call
    obtain ⟨io, ip, iq, id⟩ := ih (call + 2)
    dsimp only [comparisonSum, Bind.bind, bindWork, natAdd, realAdd, Cost.add]
    constructor
    · omega
    · simp only [hp, hq, hd, ip, iq, id, Nat.zero_add, Nat.add_zero, true_and, and_true]
      omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma comparison_sum_value (s : ℝ) (a b : E) (reply : ℕ → E → ℝ) (T call : ℕ) :
    (comparisonSum s a b reply T call).value =
      ∑ i : Fin T, OracleTemplate.clip s (reply (call + 2 * i) a - reply (call + 2 * i + 1) b) := by
  induction T generalizing call with
  | zero => simp [comparisonSum, Pure.pure, pureWork]
  | succ T ih =>
    dsimp only [comparisonSum, Bind.bind, bindWork, natAdd, realAdd]
    rw [comparison_pair_value, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selection_cost (s : ℝ) (a b : E) (reply : ℕ → E → ℝ) (T call : ℕ) :
    (selection s a b reply T call).cost.operations ≤ 10 * T + 4 ∧
      (selection s a b reply T call).cost.projections = 0 ∧
      (selection s a b reply T call).cost.queries = 2 * T ∧
      (selection s a b reply T call).cost.directions = 0 := by
  obtain ⟨ho, hp, hq, hd⟩ := comparison_sum_cost s a b reply T call
  dsimp only [selection, Bind.bind, Pure.pure, bindWork, natReal, realDiv, realMul, realLe]
  split <;> dsimp only [pureWork, Cost.add]
  all_goals
    constructor
    · omega
    · simp [hp, hq, hd]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selection_value (s : ℝ) (a b : E) (reply : ℕ → E → ℝ) (T call : ℕ) :
    (selection s a b reply T call).value =
      OracleTemplate.QueryPlan.sampledEval (fun x k => reply k x) id
        (LongTails.Algorithms.ClippedTwoPoint.selectionPlan s a b T) call := by
  dsimp only [selection, Bind.bind, Pure.pure, bindWork, natReal, realDiv, realMul, realLe]
  simp only [comparison_sum_value, one_div,
    LongTails.Algorithms.ClippedTwoPoint.selectionPlan,
    OracleTemplate.QueryPlan.sampledEval_map, OracleTemplate.QueryPlan.sampledEval_traverse,
    List.sum_ofFn, LongTails.Algorithms.ClippedTwoPoint.comparisonPairPlan,
    OracleTemplate.QueryPlan.sampledEval, id_eq,
    LongTails.Algorithms.ClippedTwoPoint.selectByDifference]
  split <;> simp_all [pureWork]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma padding_cost (q0 : E) (reply : ℕ → E → ℝ) (output : E) (K call : ℕ) :
    (padding q0 reply output K call).cost = ⟨2 * K, 0, K, 0⟩ := by
  induction K generalizing call with
  | zero => rfl
  | succ K ih =>
    dsimp only [padding, Bind.bind, bindWork, query, natAdd]
    rw [ih]
    simp only [Cost.add]
    congr 1 <;> omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma padding_value (q0 : E) (reply : ℕ → E → ℝ) (output : E) (K call : ℕ) :
    (padding q0 reply output K call).value = output := by
  induction K generalizing call with
  | zero => rfl
  | succ K ih =>
    dsimp only [padding, Bind.bind, bindWork, query, natAdd]
    exact ih (call + 1)

end LongTails.Proofs.ClippedTwoPointWork
