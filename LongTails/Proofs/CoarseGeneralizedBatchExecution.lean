import LongTails.Proofs.CoarseGeneralizedExecution
import LongTails.Proofs.CoarseGeneralizedFailures
import LongTails.Proofs.RobustGeneralizedExecution
import LongTails.Algorithms.CoarseGeneralizedAccelerated

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
open RobustGeneralized (replyPrefix replyPrefix_update)
open StochasticGeneralized (blockTrace blockCalls blockAdvance)

set_option maxRecDepth 4000 in
lemma warmEstimate_congr_prefix (p : Params) {v w : ℕ → p.E}
    (h : ∀ i < warmBatch p, v i = w i) : warmEstimate p v = warmEstimate p w := by
  unfold warmEstimate
  congr 1
  funext i
  apply RobustGeneralized.meanBlock_congr
  intro j hj
  apply h
  have hi := Nat.mul_le_mul_right 576 (Nat.succ_le_of_lt i.isLt)
  simp only [Nat.succ_mul] at hi
  unfold warmBatch
  omega

lemma warmEstimate_replyPrefix (p : Params) (v : ℕ → p.E) :
    warmEstimate p (replyPrefix (warmBatch p) v) = warmEstimate p v := by
  apply warmEstimate_congr_prefix
  intro i hi
  simp [replyPrefix, hi]

lemma warmBatch_pos (p : Params) : 0 < warmBatch p := by
  unfold warmBatch warmGroups
  positivity

noncomputable def rawAdvance (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n call : ℕ) (s : CombinedState p.E) : CombinedState p.E :=
  StochasticGradient.advance (fun k state => (algorithm p).update state (g (((algorithm p).query state).2) (ξ k))) n call s

lemma rawAdvance_add (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n m call : ℕ) (s : CombinedState p.E) :
    rawAdvance p g ξ (n + m) call s = rawAdvance p g ξ m (call + n) (rawAdvance p g ξ n call s) :=
  HeavyTailedMarkovGradient.advance_add _ _ _ _ _

lemma rawAdvance_warm_prefix (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Search p.E) (blocks call j : ℕ) (hj : j < warmBatch p) :
    rawAdvance p g ξ j call (.warm s blocks 0 (fun _ => 0)) =
      .warm s blocks j (replyPrefix j (fun i => g (searchPoint s) (ξ (call + i)))) := by
  induction j with
  | zero =>
      simp only [rawAdvance, StochasticGradient.advance]
      congr 1
  | succ j ih =>
      rw [rawAdvance_add, ih (by omega)]
      simp only [rawAdvance, StochasticGradient.advance, algorithm, hj, ↓reduceIte]
      rw [replyPrefix_update]

lemma rawAdvance_warm_block (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Search p.E) (blocks call : ℕ) :
    rawAdvance p g ξ (warmBatch p) call (.warm s blocks 0 (fun _ => 0)) =
      let s' := searchUpdate (warmTuning p) s
        (warmEstimate p (fun i => g (searchPoint s) (ξ (call + i))))
      if blocks + 1 < warmCalls p then .warm s' (blocks + 1) 0 (fun _ => 0)
      else startFinal p (warmOutput s') := by
  have hm := warmBatch_pos p
  obtain ⟨j, he⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [he, Nat.succ_eq_add_one, rawAdvance_add,
    rawAdvance_warm_prefix p g ξ s blocks call j (by omega)]
  simp only [rawAdvance, StochasticGradient.advance, algorithm, he, Nat.succ_eq_add_one,
    lt_self_iff_false, ↓reduceIte, replyPrefix_update]
  have he' : j + 1 = warmBatch p := he.symm
  rw [he', warmEstimate_replyPrefix]

lemma rawAdvance_final (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (x : p.E) (n call : ℕ) (s : RobustGeneralized.State p.E) :
    rawAdvance p g ξ n call (.final x s) =
      .final x (RobustGeneralized.rawAdvance (restartParams p x) g ξ n call s) := by
  induction n generalizing call s with
  | zero => rfl
  | succ n ih =>
      change rawAdvance p g ξ n (call + 1)
        (.final x ((RobustGeneralized.algorithm (restartParams p x)).update s
          (g (((RobustGeneralized.algorithm (restartParams p x)).query s).2) (ξ call)))) = _
      exact ih (call + 1) _

lemma advance_shift {State : Type*} (step : ℕ → State → State) (n offset call : ℕ) (s : State) :
    StochasticGradient.advance step n (offset + call) s =
      StochasticGradient.advance (fun k => step (offset + k)) n call s := by
  induction n generalizing call s with
  | zero => rfl
  | succ n ih =>
      simp only [StochasticGradient.advance]
      rw [show offset + call + 1 = offset + (call + 1) by omega, ih]

lemma rawAdvance_final_shift (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (x : p.E) (n call : ℕ) (s : RobustGeneralized.State p.E) :
    rawAdvance p g ξ n call (.final x s) =
      .final x (RobustGeneralized.rawAdvance (restartParams p x) g (fun k => ξ (call + k)) n 0 s) := by
  rw [rawAdvance_final]
  congr 1
  unfold RobustGeneralized.rawAdvance
  exact advance_shift (State := RobustGeneralized.State p.E)
    (fun k state => (RobustGeneralized.algorithm (restartParams p x)).update state
      (g (((RobustGeneralized.algorithm (restartParams p x)).query state).2) (ξ k))) n call 0 s

lemma warmEstimate_stream (p : Params) (g : p.E → p.Ω → p.E) (x : p.E)
    (ξ : ℕ → p.Ω) (offset : ℕ) :
    warmEstimate p (RobustGeneralized.sampleReplies g x (fun i : Fin (warmBatch p) => ξ (offset + i))) =
      warmEstimate p (fun i => g x (ξ (offset + i))) := by
  apply warmEstimate_congr_prefix
  intro i hi
  simp only [RobustGeneralized.sampleReplies, hi, ↓reduceDIte]

lemma coarse_trace_tail (p : Params) (oracle : p.E → p.Ω → p.E) (s : Search p.E)
    (ξ : ℕ → p.Ω) (n k : ℕ) :
    (blockTrace (fun _ => warmBatch p) (coarseNext p oracle) s ξ n).2 k =
      ξ (n * warmBatch p + k) := by
  rw [StochasticGeneralized.blockTrace_tail]
  simp [blockCalls]

set_option maxRecDepth 4000 in
lemma coarse_trace_state (p : Params) (oracle : p.E → p.Ω → p.E) (s : Search p.E)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    (blockTrace (fun _ => warmBatch p) (coarseNext p oracle) s ξ n).1 =
      StochasticGradient.advance (fun k q => searchUpdate (warmTuning p) q
        (warmEstimate p (fun j => oracle (searchPoint q) (ξ (k * warmBatch p + j))))) n 0 s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [StochasticGeneralized.blockTrace_succ, advance_append_step]
      dsimp only [blockAdvance, coarseNext]
      simp_rw [coarse_trace_tail]
      rw [warmEstimate_stream, ih, Nat.zero_add]


lemma rawAdvance_warm_prefix_blocks (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Search p.E) (n : ℕ) (hn : n < warmCalls p) :
    rawAdvance p g ξ (n * warmBatch p) 0 (.warm s 0 0 (fun _ => 0)) =
      .warm (blockTrace (fun _ => warmBatch p) (coarseNext p g) s ξ n).1 n 0 (fun _ => 0) := by
  induction n with
  | zero => rw [Nat.zero_mul]; rfl
  | succ n ih =>
      rw [Nat.succ_mul, rawAdvance_add, ih (by omega)]
      rw [rawAdvance_warm_block]
      simp only [zero_add, hn, ↓reduceIte]
      rw [StochasticGeneralized.blockTrace_succ]
      dsimp only [blockAdvance, coarseNext]
      simp_rw [coarse_trace_tail]
      rw [warmEstimate_stream]

lemma rawAdvance_warm_all (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Search p.E) (hM : 0 < warmCalls p) :
    rawAdvance p g ξ (warmCost p) 0 (.warm s 0 0 (fun _ => 0)) =
      startFinal p (warmOutput (blockTrace (fun _ => warmBatch p) (coarseNext p g) s ξ (warmCalls p)).1) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  unfold warmCost
  rw [hn, Nat.succ_mul, rawAdvance_add, rawAdvance_warm_prefix_blocks p g ξ s n (by omega)]
  rw [rawAdvance_warm_block]
  simp only [zero_add, hn, Nat.succ_eq_add_one, lt_self_iff_false, ↓reduceIte]
  rw [StochasticGeneralized.blockTrace_succ]
  dsimp only [blockAdvance, coarseNext]
  simp_rw [coarse_trace_tail]
  rw [warmEstimate_stream]

lemma output_startFinal (p : Params) (x : p.E) : (algorithm p).output (startFinal p x) = x := by
  dsimp only [startFinal, algorithm, RobustGeneralized.algorithm, RobustGeneralized.resume,
    StochasticGeneralized.initialIterate]
  split_ifs <;> rfl

lemma rawAdvance_initial_warm (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) :
    rawAdvance p g ξ (warmCost p) 0 ((algorithm p).initial ()) = startFinal p (warmPoint p g ξ) := by
  by_cases hs : p.L1 * p.R < 1
  · simp only [algorithm, hs, ↓reduceIte, warmCost, warmCalls, zero_mul,
      rawAdvance, StochasticGradient.advance, warmPoint]
  · simp only [algorithm, hs, ↓reduceIte]
    erw [rawAdvance_warm_all p g ξ _ (warmCalls_pos p (le_of_not_gt hs))]
    simp only [warmPoint, hs, ↓reduceIte]

lemma execute_split (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (P Q : MeasureTheory.ProbabilityMeasure (ℕ → p.Ω)) (n : ℕ) :
    execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm p) (fun _ => warmCost p + n) () ξ =
    execute { Seed := fun _ => p.Ω, law := Q, answer := fun _ (_, x) ω => g x ω }
      (RobustGeneralized.algorithm (restartParams p (warmPoint p g ξ))) (fun _ => n) ()
      (fun k => ξ (warmCost p + k)) := by
  erw [StochasticGradient.execute_advance, StochasticGradient.execute_advance]
  change (algorithm p).output (rawAdvance p g ξ (warmCost p + n) 0 ((algorithm p).initial ())) =
    (RobustGeneralized.algorithm (restartParams p (warmPoint p g ξ))).output
      (RobustGeneralized.rawAdvance (restartParams p (warmPoint p g ξ)) g
        (fun k => ξ (warmCost p + k)) n 0
        ((RobustGeneralized.algorithm (restartParams p (warmPoint p g ξ))).initial ()))
  erw [rawAdvance_add, rawAdvance_initial_warm, Nat.zero_add]
  unfold startFinal
  erw [rawAdvance_final_shift]
  rfl

lemma warmPoint_eq_output (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) :
    warmPoint p g ξ = (algorithm p).output
      (rawAdvance p g ξ (warmCost p) 0 ((algorithm p).initial ())) := by
  erw [rawAdvance_initial_warm, output_startFinal]

set_option maxRecDepth 4000 in
lemma rawAdvance_congr_stream (p : Params) (g : p.E → p.Ω → p.E)
    (ξ ζ : ℕ → p.Ω) (n call : ℕ) (s : CombinedState p.E)
    (he : ∀ i, call ≤ i → i < call + n → ξ i = ζ i) :
    rawAdvance p g ξ n call s = rawAdvance p g ζ n call s := by
  induction n generalizing call s with
  | zero => rfl
  | succ n ih =>
      change rawAdvance p g ξ n (call + 1)
        ((algorithm p).update s (g (((algorithm p).query s).2) (ξ call))) =
        rawAdvance p g ζ n (call + 1)
        ((algorithm p).update s (g (((algorithm p).query s).2) (ζ call)))
      rw [he call le_rfl (by omega)]
      apply ih
      intro i hi hi'
      exact he i (by omega) (by omega)

set_option maxRecDepth 4000 in
lemma warmPoint_congr_prefix (p : Params) (g : p.E → p.Ω → p.E) (ξ ζ : ℕ → p.Ω)
    (he : ∀ i < warmCost p, ξ i = ζ i) : warmPoint p g ξ = warmPoint p g ζ := by
  rw [warmPoint_eq_output, warmPoint_eq_output]
  congr 1
  apply rawAdvance_congr_stream
  intro i _ hi
  exact he i (by simpa using hi)

end OracleTemplate.CoarseGeneralized
