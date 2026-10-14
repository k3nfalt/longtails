import LongTails.Proofs.AdaptiveEntropicStateMeasurable
import LongTails.Proofs.AdaptiveEntropicConcentration
import LongTails.Proofs.AdaptiveEntropicGeometry

open MeasureTheory

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def blockUpdate (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) : (n : ℕ) → State q → (Fin n → Ω) → State q
  | 0, s, _ => s
  | n + 1, s, b => blockUpdate q g n
      (updateState q s (g (queryPoint q s) (b 0))) (fun i => b i.succ)

lemma measurable_blockUpdate (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (blockUpdate q g n)) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hreply : Measurable (fun w : State q × (Fin (n + 1) → Ω) =>
        g (queryPoint q w.1) (w.2 0)) :=
      hg.comp (((measurable_queryPoint q).comp measurable_fst).prodMk
        ((measurable_pi_apply 0).comp measurable_snd))
    have hs := (measurable_updateState q).comp (measurable_fst.prodMk hreply)
    have ht : Measurable (fun w : State q × (Fin (n + 1) → Ω) =>
        fun i : Fin n => w.2 i.succ) := by fun_prop
    exact ih.comp (hs.prodMk ht)

lemma blockUpdate_eq_advance (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n call : ℕ) (s : State q) :
    blockUpdate q g n s (fun i => ξ (call + i)) =
      StochasticGradient.advance (fun k s => updateState q s (g (queryPoint q s) (ξ k)))
        n call s := by
  induction n generalizing call s with
  | zero => rfl
  | succ n ih =>
    simp only [blockUpdate, Fin.val_zero, Nat.add_zero, StochasticGradient.advance]
    convert ih (call + 1) (updateState q s (g (queryPoint q s) (ξ call))) using 1
    congr 1
    funext i
    congr 1
    simp only [Fin.val_succ]
    omega

lemma advance_add {S : Type*} (step : ℕ → S → S) (m n call : ℕ) (s : S) :
    StochasticGradient.advance step (m + n) call s =
      StochasticGradient.advance step n (call + m)
        (StochasticGradient.advance step m call s) := by
  induction m generalizing call s with
  | zero => simp [StochasticGradient.advance]
  | succ m ih =>
    rw [Nat.succ_add, StochasticGradient.advance, ih]
    change StochasticGradient.advance step n (call + 1 + m)
      (StochasticGradient.advance step m (call + 1) (step call s)) =
      StochasticGradient.advance step n (call + (m + 1))
        (StochasticGradient.advance step m (call + 1) (step call s))
    rw [show call + 1 + m = call + (m + 1) by omega]

lemma blockTrace_eq_advance (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (cost : State q → ℕ)
    (s : State q) (ξ : ℕ → Ω) (n : ℕ) :
    (StochasticGeneralized.blockTrace cost (blockUpdate q g) s ξ n).1 =
      StochasticGradient.advance (fun k s => updateState q s (g (queryPoint q s) (ξ k)))
        (StochasticGeneralized.blockCalls cost (blockUpdate q g) s ξ n) 0 s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [StochasticGeneralized.blockTrace_succ, StochasticGeneralized.blockCalls_succ]
    change blockUpdate q g (cost (StochasticGeneralized.blockTrace cost (blockUpdate q g) s ξ n).1)
      (StochasticGeneralized.blockTrace cost (blockUpdate q g) s ξ n).1
      (fun i => (StochasticGeneralized.blockTrace cost (blockUpdate q g) s ξ n).2 i) = _
    simp_rw [StochasticGeneralized.blockTrace_tail]
    rw [blockUpdate_eq_advance, advance_add, Nat.zero_add, ih]

noncomputable def analysisCost (q : Public) (s : State q) : ℕ :=
  if 0 < s.warmup then 1 else 2

lemma measurable_analysisCost (q : Public) : Measurable (analysisCost q) := by
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_warmup q))
    measurable_const measurable_const

noncomputable def blockFromStream (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (n : ℕ) (s : State q) (ξ : ℕ → Ω) : State q :=
  blockUpdate q g n s (fun i => ξ i)

lemma blockUpdate_structure (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (s : State q) (ξ : ℕ → Ω)
    (hp : s.pending = none) :
    let z := blockUpdate q g (analysisCost q s) s (fun i => ξ i)
    z.pending = none ∧ z.history = g (queryPoint q s) (ξ 0) :: s.history ∧
      z.warmup = s.warmup - 1 ∧
      z.completed = s.completed + if 0 < s.warmup then 0 else 1 := by
  change (blockFromStream q g (analysisCost q s) s ξ).pending = none ∧
    (blockFromStream q g (analysisCost q s) s ξ).history = g (queryPoint q s) (ξ 0) :: s.history ∧
    (blockFromStream q g (analysisCost q s) s ξ).warmup = s.warmup - 1 ∧
    (blockFromStream q g (analysisCost q s) s ξ).completed =
      s.completed + if 0 < s.warmup then 0 else 1
  by_cases hw : 0 < s.warmup
  · simp only [analysisCost, ite_eq_left hw]
    simp [blockFromStream, blockUpdate, updateState, hw, hp]
  · have hz : s.warmup = 0 := by omega
    simp only [analysisCost, ite_eq_right hw]
    simp [blockFromStream, blockUpdate, updateState, hz, hp]

lemma blockTrace_structure (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1
    s.pending = none ∧ s.history.length = n ∧ s.warmup = preload q - n ∧
      s.completed = n - preload q := by
  induction n with
  | zero => simp [StochasticGeneralized.blockTrace_zero, initialState]
  | succ n ih =>
    let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ n
    change tr.1.pending = none ∧ tr.1.history.length = n ∧
      tr.1.warmup = preload q - n ∧ tr.1.completed = n - preload q at ih
    have hs := blockUpdate_structure q g tr.1 tr.2 ih.1
    rw [StochasticGeneralized.blockTrace_succ]
    change (blockUpdate q g (analysisCost q tr.1) tr.1 (fun i => tr.2 i)).pending = none ∧
      (blockUpdate q g (analysisCost q tr.1) tr.1 (fun i => tr.2 i)).history.length = n + 1 ∧
      (blockUpdate q g (analysisCost q tr.1) tr.1 (fun i => tr.2 i)).warmup = preload q - (n + 1) ∧
      (blockUpdate q g (analysisCost q tr.1) tr.1 (fun i => tr.2 i)).completed = n + 1 - preload q
    refine ⟨hs.1, ?_, ?_, ?_⟩
    · rw [hs.2.1, List.length_cons, ih.2.1]
    · rw [hs.2.2.1, ih.2.2.1]
      omega
    · rw [hs.2.2.2, ih.2.2.1, ih.2.2.2]
      split_ifs <;> omega

lemma blockCalls_exact (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    StochasticGeneralized.blockCalls (analysisCost q) (blockUpdate q g) (initialState q) ξ n =
      min n (preload q) + 2 * (n - preload q) := by
  induction n with
  | zero => simp [StochasticGeneralized.blockCalls]
  | succ n ih =>
    have hs := blockTrace_structure q g ξ n
    rw [StochasticGeneralized.blockCalls_succ, ih]
    simp only [analysisCost, hs.2.2.1]
    split_ifs <;> omega

lemma blockCalls_preload_pairs (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (T : ℕ) :
    StochasticGeneralized.blockCalls (analysisCost q) (blockUpdate q g)
      (initialState q) ξ (preload q + T) = preload q + 2 * T := by
  rw [blockCalls_exact]
  omega

lemma blockTrace_history_succ (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ (n + 1)).1.history =
      g (queryPoint q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ n).1)
        (ξ (StochasticGeneralized.blockCalls (analysisCost q) (blockUpdate q g)
          (initialState q) ξ n)) ::
      (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ n).1.history := by
  let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ n
  have hs := blockUpdate_structure q g tr.1 tr.2 (blockTrace_structure q g ξ n).1
  rw [StochasticGeneralized.blockTrace_succ]
  change (blockUpdate q g (analysisCost q tr.1) tr.1 (fun i => tr.2 i)).history = _
  rw [hs.2.1]
  congr 2
  exact StochasticGeneralized.blockTrace_tail _ _ _ _ _ 0

noncomputable def blockQuery (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) : simplex q.d :=
  queryPoint q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ n).1

noncomputable def primaryReply (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) : Vector q.d :=
  g (blockQuery q g ξ n) (ξ (StochasticGeneralized.blockCalls (analysisCost q)
    (blockUpdate q g) (initialState q) ξ n))

lemma blockTrace_history_eq (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1.history =
      (List.ofFn (fun i : Fin n => primaryReply q g ξ i)).reverse := by
  induction n with
  | zero => simp [StochasticGeneralized.blockTrace_zero, initialState]
  | succ n ih =>
    rw [blockTrace_history_succ, ih, List.ofFn_succ_last, List.reverse_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
    rfl

lemma blockTrace_window_eq (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) {n k : ℕ} (hk : k ≤ n) :
    ((StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1.history).take k =
      List.ofFn (fun i : Fin k => primaryReply q g ξ (n - 1 - i)) := by
  rw [blockTrace_history_eq]
  apply List.ext_getElem
  · simp [hk]
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]

lemma blockFromStream_pair_output (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (s : State q) (ξ : ℕ → Ω)
    (hw : s.warmup = 0) (hp : s.pending = none) :
    ∃ z : simplex q.d, (blockFromStream q g 2 s ξ).y = mix s.completed s.y z := by
  simp only [blockFromStream, blockUpdate, updateState, hw, Nat.lt_irrefl,
    ite_false, hp]
  exact ⟨_, rfl⟩

lemma blockTrace_pair_output (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) {n : ℕ} (hn : preload q ≤ n) :
    ∃ z : simplex q.d,
      (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ (n + 1)).1.y =
      mix (n - preload q) (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ n).1.y z := by
  let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ n
  have hs := blockTrace_structure q g ξ n
  have hw : tr.1.warmup = 0 := by
    have he : tr.1.warmup = preload q - n := hs.2.2.1
    rw [he]
    omega
  have ho := blockFromStream_pair_output q g tr.1 tr.2 hw hs.1
  rw [hs.2.2.2] at ho
  rw [StochasticGeneralized.blockTrace_succ]
  change ∃ z, (blockFromStream q g (analysisCost q tr.1) tr.1 tr.2).y = mix (n - preload q) tr.1.y z
  simpa only [analysisCost, hw, Nat.lt_irrefl, ite_false] using ho

lemma blockQuery_warm (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) {n : ℕ} (hn : n < preload q) :
    blockQuery q g ξ n = uniform q := by
  have hs := blockTrace_structure q g ξ n
  have hw : 0 < (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1.warmup := by rw [hs.2.2.1]; omega
  simp only [blockQuery, queryPoint, ite_eq_left hw]

lemma blockQuery_pair (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) {n : ℕ} (hn : preload q ≤ n) :
    blockQuery q g ξ n =
      mix (n - preload q) (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ n).1.y
        (predictableProx q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ n).1) := by
  have hs := blockTrace_structure q g ξ n
  have hw : ¬ 0 < (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1.warmup := by rw [hs.2.2.1]; omega
  simp only [blockQuery, queryPoint, ite_eq_right hw, hs.2.2.2]

lemma blockQuery_distance (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) {n : ℕ} (hn : preload q ≤ n) :
    oneNorm ((blockQuery q g ξ (n + 1)).val - (blockQuery q g ξ n).val) ≤
      8 / ((n - preload q : ℕ) + 2) := by
  obtain ⟨z, hz⟩ := blockTrace_pair_output q g ξ hn
  rw [blockQuery_pair q g ξ (by omega : preload q ≤ n + 1), blockQuery_pair q g ξ hn,
    hz, show n + 1 - preload q = (n - preload q) + 1 by omega]
  exact successive_query_distance _ _ _ _ _

noncomputable def queryTrajectory (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (t : ℕ) : simplex q.d :=
  if t = 0 then uniform q else blockQuery q g ξ (preload q + t - 1)

lemma queryTrajectory_distance (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    oneNorm ((queryTrajectory q g ξ (n + 1)).val - (queryTrajectory q g ξ n).val) ≤
      8 / (n + 1) := by
  cases n with
  | zero =>
    exact (simplex_diameter _ _).trans (by norm_num)
  | succ n =>
    have h := blockQuery_distance q g ξ (n := preload q + n) (by omega)
    simpa [queryTrajectory, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using h

lemma blockQuery_eq_trajectory (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    blockQuery q g ξ n = queryTrajectory q g ξ (n + 1 - preload q) := by
  by_cases hn : n < preload q
  · rw [blockQuery_warm q g ξ hn]
    simp [queryTrajectory, show n + 1 - preload q = 0 by omega]
  · have ht : n + 1 - preload q ≠ 0 := by omega
    simp only [queryTrajectory, ite_eq_right ht]
    congr 1
    omega

end OracleTemplate.AdaptiveHeavyTailSimplex
