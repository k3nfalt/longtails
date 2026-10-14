import LongTails.Proofs.QueryPlan
import LongTails.Algorithms.ScalarSearchPlans
import Mathlib.Data.List.OfFn

namespace OracleTemplate.ScalarSearchExecution

open QueryPlan

variable {Q R U V : Type*}

def evalOracle (g : ℕ → Q → R) : {k : ℕ} → QueryPlan Q R U k → ℕ → U
  | _, .done value, _ => value
  | _, .ask query next, call => evalOracle g (next (g call query)) (call + 1)

lemma evalOracle_bind (g : ℕ → Q → R) {k m : ℕ} (plan : QueryPlan Q R U k)
    (next : U → QueryPlan Q R V m) (call : ℕ) :
    evalOracle g (QueryPlan.bind plan next) call =
      evalOracle g (next (evalOracle g plan call)) (call + k) := by
  induction plan generalizing call with
  | done value => simp [QueryPlan.bind, evalOracle]
  | ask query rest ih =>
    simpa only [QueryPlan.bind, evalOracle, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (g call query) (call + 1)

lemma evalOracle_map (g : ℕ → Q → R) (f : U → V) {k : ℕ}
    (plan : QueryPlan Q R U k) (call : ℕ) :
    evalOracle g (map f plan) call = f (evalOracle g plan call) := by
  induction plan generalizing call with
  | done value => rfl
  | ask query rest ih => exact ih (g call query) (call + 1)

lemma advance_plan (g : ℕ → Q → R) (q0 : Q) {k K : ℕ}
    (plan : QueryPlan Q R U k) (h : k ≤ K) (call : ℕ) :
    StochasticGradient.advance (fun j s => update s (g j (query q0 s)))
      K call ⟨k, plan⟩ = ⟨0, done (evalOracle g plan call)⟩ := by
  induction plan generalizing K call with
  | done value =>
    induction K generalizing call with
    | zero => rfl
    | succ K ih => exact ih (Nat.zero_le K) (call + 1)
  | @ask k query rest ih =>
    cases K with
    | zero => omega
    | succ K => exact ih (g call query) (by omega) (call + 1)

lemma execute_plan {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (k K : ℕ) (plan : S → QueryPlan Q R U k)
    (O : Oracle Q R) (seed : S) (ξ : (j : ℕ) → O.Seed j) (h : k ≤ K) :
    execute O (algorithm law q0 u0 k plan) (fun _ => K) seed ξ =
      evalOracle (fun j q => O.answer j (0, q) (ξ j)) (plan seed) 0 := by
  erw [StochasticGradient.execute_advance]
  change output u0 (StochasticGradient.advance
    (fun j s => update s (O.answer j (0, (query q0 s)) (ξ j))) K 0 ⟨k, plan seed⟩) = _
  rw [advance_plan (fun j q => O.answer j (0, q) (ξ j)) q0 (plan seed) h 0]
  rfl

lemma evalOracle_shift (g : ℕ → Q → R) {k : ℕ} (plan : QueryPlan Q R U k) (offset call : ℕ) :
    evalOracle (fun j => g (offset + j)) plan call = evalOracle g plan (offset + call) := by
  induction plan generalizing call with
  | done value => rfl
  | ask query next ih =>
    simp only [evalOracle, ih, Nat.add_assoc]

lemma samplesPlan_evalOracle (g : ℕ → ℝ → ℝ) (x : ℝ) (n call : ℕ) :
    evalOracle g (ScalarSearchPlans.samplesPlan x n) call =
      fun i : Fin n => g (call + i) x := by
  induction n generalizing call with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [ScalarSearchPlans.samplesPlan, evalOracle, evalOracle_map, ih]
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [Nat.add_comm, Nat.add_left_comm]

lemma estimatePlan_evalOracle (g : ℕ → ℝ → ℝ) (σ p u x : ℝ) (k call : ℕ) :
    evalOracle g (ScalarSearchPlans.estimatePlan σ p u k x) call =
      ScalarHeavyTailEstimator.estimate σ p u k
        (fun j => if j < ScalarHeavyTailEstimator.calls σ p u k then g (call + j) x else 0) := by
  rw [ScalarSearchPlans.estimatePlan, evalOracle_map, samplesPlan_evalOracle]
  congr 1

lemma block_reads (σ p u : ℝ) (a b : ℕ → ℝ)
    (h : ∀ j < ScalarHeavyTailEstimator.blockSize σ p u, a j = b j) :
    ScalarHeavyTailEstimator.block σ p u a = ScalarHeavyTailEstimator.block σ p u b := by
  classical
  unfold ScalarHeavyTailEstimator.block
  split_ifs with hr
  · exact h 0 (by simp [ScalarHeavyTailEstimator.blockSize, hr])
  · have h0 := h 0 (by simp [ScalarHeavyTailEstimator.blockSize, hr])
    rw [h0]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [h (i + 1) (by simp only [ScalarHeavyTailEstimator.blockSize, ite_eq_right hr]; omega)]

lemma estimate_reads (σ p u : ℝ) (k : ℕ) (a b : ℕ → ℝ)
    (h : ∀ j < ScalarHeavyTailEstimator.calls σ p u k, a j = b j) :
    ScalarHeavyTailEstimator.estimate σ p u k a = ScalarHeavyTailEstimator.estimate σ p u k b := by
  unfold ScalarHeavyTailEstimator.estimate
  congr 1
  funext i
  apply block_reads
  intro j hj
  apply h
  unfold ScalarHeavyTailEstimator.calls
  have hi := Nat.mul_le_mul_right (ScalarHeavyTailEstimator.blockSize σ p u) (Nat.succ_le_of_lt i.isLt)
  nlinarith

lemma estimatePlan_evalOracle_full (g : ℕ → ℝ → ℝ) (σ p u x : ℝ) (k call : ℕ) :
    evalOracle g (ScalarSearchPlans.estimatePlan σ p u k x) call =
      ScalarHeavyTailEstimator.estimate σ p u k (fun j => g (call + j) x) := by
  rw [estimatePlan_evalOracle]
  apply estimate_reads
  intro j hj
  simp only [hj, ite_true]

lemma walkPlan_length (g : ℕ → ℝ → ℝ) (σ p ε x0 s : ℝ) (D n call : ℕ)
    (path : List ScalarNoisySearch.Node) :
    (evalOracle g (ScalarSearchPlans.walkPlan σ p ε x0 s D n path) call).length = n := by
  induction n generalizing path call with
  | zero => rfl
  | succ n ih =>
    rw [ScalarSearchPlans.walkPlan, evalOracle_bind, evalOracle_map]
    simp only [List.length_cons]
    rw [ih]

lemma root_record_index (g : ℕ → ℝ → ℝ) (σ p ε x0 s hi : ℝ) (D call : ℕ)
    (time : Fin (16 * D)) :
    time.val < (evalOracle g (ScalarSearchPlans.walkPlan σ p ε x0 s D (16 * D)
      [.interval 0 hi 0]) call).length := by
  rw [walkPlan_length]
  exact time.isLt

lemma trace_shift (ε : ℝ) (D ℓ : ℕ)
    (reply : ℕ → List ScalarNoisySearch.Node → Fin 3 → ℝ)
    (path : List ScalarNoisySearch.Node) (m n : ℕ) :
    ScalarNoisySearch.trace ε D ℓ reply path (m + n) =
      ScalarNoisySearch.trace ε D ℓ (fun j => reply (m + j))
        (ScalarNoisySearch.trace ε D ℓ reply path m) n := by
  induction n with
  | zero => simp [ScalarNoisySearch.trace]
  | succ n ih =>
    change ScalarNoisySearch.advance ε D ℓ
      (reply (m + n) (ScalarNoisySearch.trace ε D ℓ reply path (m + n)))
      (ScalarNoisySearch.trace ε D ℓ reply path (m + n)) = _
    rw [ih]
    rfl

noncomputable def walkReplies (g : ℕ → ℝ → ℝ) (σ p ε x0 s : ℝ) (call : ℕ)
    (t : ℕ) (path : List ScalarNoisySearch.Node) : Fin 3 → ℝ :=
  evalOracle g (ScalarSearchPlans.triplePlan σ p (ε / 96) 6 x0 s
    (ScalarNoisySearch.queries (path.headD (.interval 0 0 0))))
      (call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * t)

lemma walk_trace_next (g : ℕ → ℝ → ℝ) (σ p ε x0 s : ℝ) (D call n : ℕ)
    (path : List ScalarNoisySearch.Node) :
    ScalarNoisySearch.trace ε D (2 * D) (walkReplies g σ p ε x0 s call) path (n + 1) =
      ScalarNoisySearch.trace ε D (2 * D)
        (walkReplies g σ p ε x0 s (call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6))
        (ScalarNoisySearch.advance ε D (2 * D) (walkReplies g σ p ε x0 s call 0 path) path) n := by
  rw [Nat.add_comm n 1, trace_shift]
  congr 1
  funext j state
  simp only [walkReplies]
  congr 1
  ring

lemma walkPlan_records (g : ℕ → ℝ → ℝ) (σ p ε x0 s : ℝ) (D n call : ℕ)
    (path : List ScalarNoisySearch.Node) :
    evalOracle g (ScalarSearchPlans.walkPlan σ p ε x0 s D n path) call =
      List.ofFn (fun i : Fin n => ScalarNoisySearch.recordedPoint 0
        (ScalarNoisySearch.trace ε D (2 * D) (walkReplies g σ p ε x0 s call) path i)) := by
  induction n generalizing path call with
  | zero => rfl
  | succ n ih =>
    rw [ScalarSearchPlans.walkPlan, evalOracle_bind, evalOracle_map, ih, List.ofFn_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [Fin.val_succ, walk_trace_next]
    rfl

lemma evalOracle_congr (g h : ℕ → Q → R) {k : ℕ} (plan : QueryPlan Q R U k)
    (call : ℕ) (he : ∀ j, call ≤ j → j < call + k → ∀ x, g j x = h j x) :
    evalOracle g plan call = evalOracle h plan call := by
  induction plan generalizing call with
  | done value => rfl
  | @ask k query rest ih =>
    simp only [evalOracle]
    have hfirst := he call le_rfl (by omega) query
    rw [hfirst]
    apply ih
    intro j hj hj' x
    exact he j (by omega) (by omega) x

lemma evalOracle_cast (g : ℕ → Q → R) {k l : ℕ} (h : k = l)
    (plan : QueryPlan Q R U k) (call : ℕ) :
    evalOracle g (h ▸ plan) call = evalOracle g plan call := by
  subst l
  rfl

lemma evalOracle_mpr (g : ℕ → Q → R) {k l : ℕ}
    (h : QueryPlan Q R U l = QueryPlan Q R U k) (hkl : k = l)
    (plan : QueryPlan Q R U k) (call : ℕ) :
    evalOracle g (h.mpr plan) call = evalOracle g plan call := by
  subst l
  rfl

lemma triplePlan_evalOracle (g : ℕ → ℝ → ℝ) (σ p u x0 s : ℝ) (k call : ℕ)
    (points : Fin 3 → ℝ) :
    evalOracle g (ScalarSearchPlans.triplePlan σ p u k x0 s points) call =
      ![s * ScalarHeavyTailEstimator.estimate σ p u k (fun j => g (call + j) (x0 + s * points 0)),
        s * ScalarHeavyTailEstimator.estimate σ p u k
          (fun j => g (call + ScalarHeavyTailEstimator.calls σ p u k + j) (x0 + s * points 1)),
        s * ScalarHeavyTailEstimator.estimate σ p u k
          (fun j => g (call + 2 * ScalarHeavyTailEstimator.calls σ p u k + j) (x0 + s * points 2))] := by
  unfold ScalarSearchPlans.triplePlan
  rw [evalOracle_mpr _ _ (by omega)]
  simp only [evalOracle_bind, evalOracle_map, estimatePlan_evalOracle_full]
  simp only [two_mul, Nat.add_assoc]

lemma triplePlan_evalOracle_apply (g : ℕ → ℝ → ℝ) (σ p u x0 s : ℝ) (k call : ℕ)
    (points : Fin 3 → ℝ) (i : Fin 3) :
    evalOracle g (ScalarSearchPlans.triplePlan σ p u k x0 s points) call i =
      s * ScalarHeavyTailEstimator.estimate σ p u k
        (fun j => g (call + ScalarHeavyTailEstimator.calls σ p u k * i.val + j)
          (x0 + s * points i)) := by
  rw [triplePlan_evalOracle]
  fin_cases i <;> simp [Nat.mul_comm]

lemma walk_trace_reads (g h : ℕ → ℝ → ℝ) (σ p ε x0 s : ℝ) (D call n : ℕ)
    (path : List ScalarNoisySearch.Node)
    (he : ∀ j, call ≤ j →
      j < call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * n → ∀ x, g j x = h j x) :
    ScalarNoisySearch.trace ε D (2 * D) (walkReplies g σ p ε x0 s call) path n =
      ScalarNoisySearch.trace ε D (2 * D) (walkReplies h σ p ε x0 s call) path n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : ∀ j, call ≤ j →
        j < call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * n → ∀ x, g j x = h j x := by
      intro j hj hj' x
      apply he j hj _ x
      exact lt_of_lt_of_le hj' (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_succ n)) call)
    simp only [ScalarNoisySearch.trace, ih hn]
    congr 1
    unfold walkReplies
    apply evalOracle_congr
    intro j hj hj' x
    apply he j (by omega) _ x
    calc
      j < call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * n +
          3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 := hj'
      _ = call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * (n + 1) := by ring

lemma rootAttemptPlan_evalOracle (g : ℕ → ℝ → ℝ) (σ p ε x0 s hi : ℝ) (D call : ℕ)
    (time : Fin (16 * D)) :
    evalOracle g (ScalarSearchPlans.rootAttemptPlan σ p ε x0 s hi D time.val) call =
      let x := x0 + s * ScalarNoisySearch.recordedPoint 0
        (ScalarNoisySearch.trace ε D (2 * D) (walkReplies g σ p ε x0 s call) [.interval 0 hi 0] time.val)
      (x, ScalarHeavyTailEstimator.estimate σ p (ε / 48) 6
        (fun j => g (call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * (16 * D) + j) x)) := by
  simp only [ScalarSearchPlans.rootAttemptPlan, evalOracle_bind, evalOracle_map,
    walkPlan_records, estimatePlan_evalOracle_full]
  simp [time.isLt]

end OracleTemplate.ScalarSearchExecution
