import LongTails.Proofs.AdaptiveEntropicMeasurable
import Mathlib.Logic.Equiv.Option
import LongTails.Proofs.SgdExecution

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

set_option backward.isDefEq.respectTransparency false

abbrev StateCode (q : Public) := ℕ × ℕ × (Vector q.d ⊕ PUnit.{1}) × List (Vector q.d) ×
  Vector q.d × simplex q.d × (Fin (trimCount q) → ℝ) × ℝ

def stateEquiv (q : Public) : State q ≃ StateCode q where
  toFun s := (s.warmup, s.completed, Equiv.optionEquivSumPUnit.{0, 0} _ s.pending, s.history,
    s.sumGradient, s.y, s.extremes, s.variation)
  invFun w := ⟨w.1, w.2.1, (Equiv.optionEquivSumPUnit.{0, 0} _).symm w.2.2.1, w.2.2.2.1,
    w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2⟩
  left_inv s := by cases s; simp
  right_inv w := by rcases w with ⟨a, b, c, d, e, f, g, h⟩; simp

instance (q : Public) : MeasurableSpace (State q) :=
  MeasurableSpace.comap (stateEquiv q) inferInstance

def stateMeasurableEquiv (q : Public) : State q ≃ᵐ StateCode q where
  toEquiv := stateEquiv q
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    change Measurable[(inferInstance : MeasurableSpace (StateCode q)),
      MeasurableSpace.comap (stateEquiv q) (inferInstance : MeasurableSpace (StateCode q))]
      (stateEquiv q).symm
    apply measurable_comap_iff.mpr
    convert (measurable_id : Measurable (id : StateCode q → _)) using 1
    exact (stateEquiv q).self_comp_symm

@[fun_prop]
lemma measurable_warmup (q : Public) : Measurable (fun s : State q => s.warmup) :=
  (stateMeasurableEquiv q).measurable.fst

@[fun_prop]
lemma measurable_completed (q : Public) : Measurable (fun s : State q => s.completed) :=
  (stateMeasurableEquiv q).measurable.snd.fst

@[fun_prop]
lemma measurable_pendingCode (q : Public) :
    Measurable (fun s : State q => Equiv.optionEquivSumPUnit.{0, 0} _ s.pending) :=
  (stateMeasurableEquiv q).measurable.snd.snd.fst

@[fun_prop]
lemma measurable_history (q : Public) : Measurable (fun s : State q => s.history) :=
  (stateMeasurableEquiv q).measurable.snd.snd.snd.fst

@[fun_prop]
lemma measurable_sumGradient (q : Public) : Measurable (fun s : State q => s.sumGradient) :=
  (stateMeasurableEquiv q).measurable.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_y (q : Public) : Measurable (fun s : State q => s.y) :=
  (stateMeasurableEquiv q).measurable.snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_extremes (q : Public) : Measurable (fun s : State q => s.extremes) :=
  (stateMeasurableEquiv q).measurable.snd.snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_variation (q : Public) : Measurable (fun s : State q => s.variation) :=
  (stateMeasurableEquiv q).measurable.snd.snd.snd.snd.snd.snd.snd

lemma continuous_dualNorm (d : ℕ) : Continuous (dualNorm : Vector d → ℝ) :=
  continuous_norm.comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))

lemma continuous_softmax {d : ℕ} (hd : 0 < d) : Continuous (softmax hd) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro i
  apply Continuous.div
  · exact Real.continuous_exp.comp (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)
  · exact continuous_finsetSum _ (fun j _ => Real.continuous_exp.comp (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j))
  · intro v
    exact ne_of_gt (Finset.sum_pos (fun j _ => Real.exp_pos (v j))
      ⟨⟨0, hd⟩, Finset.mem_univ _⟩)

lemma measurable_buffer_eval {K : ℕ} :
    Measurable (fun w : (Fin K → ℝ) × Fin K => w.1 w.2) :=
  measurable_from_prod_countable_left (fun i => measurable_pi_apply i)

lemma measurable_fold_minimum {K : ℕ} (l : List (Fin K)) :
    Measurable (fun w : (Fin K → ℝ) × Fin K =>
      l.foldl (fun i j => if w.1 j < w.1 i then j else i) w.2) := by
  induction l with
  | nil => exact measurable_snd
  | cons j l ih =>
    have hj : Measurable (fun w : (Fin K → ℝ) × Fin K => w.1 j) :=
      (measurable_pi_apply j).comp measurable_fst
    have hs : Measurable (fun w : (Fin K → ℝ) × Fin K =>
        if w.1 j < w.1 w.2 then j else w.2) :=
      Measurable.ite (measurableSet_lt hj measurable_buffer_eval) measurable_const measurable_snd
    simpa only [List.foldl_cons, Function.comp_def] using ih.comp (measurable_fst.prodMk hs)

lemma measurable_minimumIndex {K : ℕ} (hK : 0 < K) : Measurable (minimumIndex hK) := by
  exact (measurable_fold_minimum (List.finRange K)).comp
    (measurable_id.prodMk (measurable_const (a := (⟨0, hK⟩ : Fin K))))

@[fun_prop]
lemma measurable_quantileIndex (q : Public) : Measurable (quantileIndex q) :=
  (measurable_minimumIndex _).comp (measurable_extremes q)

@[fun_prop]
lemma measurable_empiricalQuantile (q : Public) : Measurable (empiricalQuantile q) :=
  measurable_buffer_eval.comp ((measurable_extremes q).prodMk (measurable_quantileIndex q))

@[fun_prop]
lemma measurable_regularization (q : Public) : Measurable (regularization q) := by
  unfold regularization
  have hw : Measurable (fun s : State q => (window q (s.completed + 1) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (window q (n + 1) : ℝ))).comp
      (measurable_completed q)
  fun_prop

@[fun_prop]
lemma measurable_predictableProx (q : Public) : Measurable (predictableProx q) := by
  unfold predictableProx
  apply (continuous_softmax _).measurable.comp
  fun_prop

@[fun_prop]
lemma measurable_mix {α : Type*} [MeasurableSpace α] {d : ℕ}
    {n : α → ℕ} {x y : α → simplex d} (hn : Measurable n)
    (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun a => mix (n a) (x a) (y a)) := by
  apply Measurable.subtype_mk
  change Measurable (fun a => (1 - 2 / ((n a : ℝ) + 2)) • (x a).val +
    (2 / ((n a : ℝ) + 2)) • (y a).val)
  fun_prop

@[fun_prop]
lemma measurable_queryPoint (q : Public) : Measurable (queryPoint q) := by
  unfold queryPoint
  apply Measurable.ite (measurableSet_lt measurable_const (measurable_warmup q))
  · exact measurable_const
  · exact measurable_mix (measurable_completed q) (measurable_y q) (measurable_predictableProx q)

@[fun_prop]
lemma measurable_dualNorm (d : ℕ) : Measurable (dualNorm : Vector d → ℝ) :=
  (continuous_dualNorm d).measurable

@[fun_prop]
lemma measurable_driftRadius (q : Public) : Measurable (driftRadius q) := by
  have hw : Measurable (fun s : State q => (window q (s.completed + 1) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (window q (n + 1) : ℝ))).comp
      (measurable_completed q)
  unfold driftRadius
  fun_prop

@[fun_prop]
lemma measurable_clippingThreshold (q : Public) : Measurable (clippingThreshold q) := by
  unfold clippingThreshold
  fun_prop

@[fun_prop]
lemma measurable_clippedReply {α : Type*} [MeasurableSpace α] {d : ℕ}
    {r : α → ℝ} {c g : α → Vector d} (hr : Measurable r)
    (hc : Measurable c) (hg : Measurable g) :
    Measurable (fun a => clippedReply (r a) (c a) (g a)) := by
  unfold clippedReply
  apply hc.add
  apply Measurable.ite (measurableSet_le ((measurable_dualNorm d).comp (hg.sub hc)) hr)
  · exact hg.sub hc
  · fun_prop

lemma measurable_windowHistory (q : Public) :
    Measurable (fun s : State q => s.history.take (window q (s.completed + 1))) := by
  apply ScalarNoisySearch.measurable_nat_selection _ (fun s : State q => window q (s.completed + 1))
    ((measurable_of_countable (fun n : ℕ => window q (n + 1))).comp (measurable_completed q))
    (fun n s => s.history.take n)
  · intro n
    exact (AdaptiveList.measurable_take n).comp (measurable_history q)
  · intro s
    rfl

@[fun_prop]
lemma measurable_state_mk {α : Type*} [MeasurableSpace α] (q : Public)
    {w n : α → ℕ} {p : α → Option (Vector q.d)} {h : α → List (Vector q.d)}
    {s : α → Vector q.d} {y : α → simplex q.d} {b : α → Fin (trimCount q) → ℝ}
    {v : α → ℝ} (hw : Measurable w) (hn : Measurable n)
    (hp : Measurable (fun a => Equiv.optionEquivSumPUnit.{0, 0} _ (p a)))
    (hh : Measurable h) (hs : Measurable s) (hy : Measurable y)
    (hb : Measurable b) (hv : Measurable v) :
    Measurable (fun a => State.mk (w a) (n a) (p a) (h a) (s a) (y a) (b a) (v a)) := by
  apply measurable_comap_iff.mpr
  exact hw.prodMk (hn.prodMk (hp.prodMk (hh.prodMk (hs.prodMk (hy.prodMk (hb.prodMk hv))))))

@[fun_prop]
lemma measurable_pending_some {α : Type*} [MeasurableSpace α] {d : ℕ}
    {g : α → Vector d} (hg : Measurable g) :
    Measurable (fun a => Equiv.optionEquivSumPUnit.{0, 0} _ (some (g a))) :=
  measurable_inl.comp hg

lemma measurable_list_cons {α E : Type*} [MeasurableSpace α] [MeasurableSpace E]
    {h : α → E} {l : α → List E} (fallback : E) (hh : Measurable h) (hl : Measurable l) :
    Measurable (fun a => h a :: l a) := (AdaptiveList.measurable_cons fallback).comp (hh.prodMk hl)

@[fun_prop]
lemma measurable_vector_cons {α : Type*} [MeasurableSpace α] {d : ℕ}
    {h : α → Vector d} {l : α → List (Vector d)} (hh : Measurable h) (hl : Measurable l) :
    Measurable (fun a => h a :: l a) := measurable_list_cons 0 hh hl

@[fun_prop]
lemma measurable_buffer_update {α : Type*} [MeasurableSpace α] {K : ℕ}
    {b : α → Fin K → ℝ} {i : α → Fin K} {r : α → ℝ}
    (hb : Measurable b) (hi : Measurable i) (hr : Measurable r) :
    Measurable (fun a => Function.update (b a) (i a) (r a)) := by
  apply measurable_pi_iff.mpr
  intro j
  have he : (fun a => Function.update (b a) (i a) (r a) j) =
      fun a => if j = i a then r a else b a j := by
    funext a
    by_cases h : j = i a <;> simp [Function.update, h]
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun measurable_const hi) hr
    ((measurable_pi_apply j).comp hb)

@[fun_prop]
lemma measurable_softmax {d : ℕ} (hd : 0 < d) : Measurable (softmax hd) :=
  (continuous_softmax hd).measurable

attribute [fun_prop] measurable_medianCenter measurable_windowHistory

@[fun_prop]
lemma measurable_natCastReal : Measurable (fun n : ℕ => (n : ℝ)) := measurable_of_countable _

lemma measurable_primaryState (q : Public) :
    Measurable (fun w : State q × Vector q.d => { w.1 with pending := some w.2 }) := by
  fun_prop

lemma measurable_warmupState (q : Public) :
    Measurable (fun w : State q × Vector q.d =>
      { w.1 with warmup := w.1.warmup - 1, history := w.2 :: w.1.history }) := by
  apply measurable_state_mk q
  all_goals first | exact (measurable_pendingCode q).comp measurable_fst | fun_prop

lemma measurable_pairState (q : Public) :
    Measurable (fun w : (State q × Vector q.d) × Vector q.d =>
      updateState q { w.1.1 with warmup := 0, pending := some w.1.2 } w.2) := by
  have hs : Measurable (fun w : (State q × Vector q.d) × Vector q.d =>
      { w.1.1 with warmup := 0, pending := some w.1.2 }) := by
    apply measurable_state_mk q
    all_goals fun_prop
  have ht : Measurable (fun w : (State q × Vector q.d) × Vector q.d =>
      ((w.1.1.completed + 1 : ℕ) : ℝ)) := by
    exact measurable_natCastReal.comp (((measurable_completed q).comp measurable_fst.fst).add_const 1)
  have hc : Measurable (fun w : (State q × Vector q.d) × Vector q.d =>
      medianCenter (w.1.1.history.take (window q (w.1.1.completed + 1)))) :=
    (measurable_medianCenter q.d).comp ((measurable_windowHistory q).comp measurable_fst.fst)
  have hr := (measurable_clippingThreshold q).comp hs
  have hg₁ := measurable_clippedReply hr hc (measurable_fst.snd :
    Measurable (fun w : (State q × Vector q.d) × Vector q.d => w.1.2))
  have hg₂ := measurable_clippedReply hr hc (measurable_snd :
    Measurable (fun w : (State q × Vector q.d) × Vector q.d => w.2))
  simp only [updateState, Nat.lt_irrefl, ↓reduceIte]
  apply measurable_state_mk q
  all_goals fun_prop

lemma measurable_update_noWarmup (q : Public) :
    Measurable (fun w : State q × Vector q.d => updateState q { w.1 with warmup := 0 } w.2) := by
  let F : (Vector q.d ⊕ PUnit.{1}) × (State q × Vector q.d) → State q := fun u =>
    match u.1 with
    | .inl g₁ => updateState q { u.2.1 with warmup := 0, pending := some g₁ } u.2.2
    | .inr _ => { u.2.1 with warmup := 0, pending := some u.2.2 }
  have hF : Measurable F := by
    apply (MeasurableEquiv.sumProdDistrib (Vector q.d) PUnit.{1}
      (State q × Vector q.d)).symm.measurable_comp_iff.mp
    apply measurable_fun_sum
    · have hm : Measurable (fun w : Vector q.d × (State q × Vector q.d) =>
          ((w.2.1, w.1), w.2.2)) := by fun_prop
      exact (measurable_pairState q).comp hm
    · dsimp only [F]
      apply measurable_state_mk q
      all_goals fun_prop
  have hp : Measurable (fun w : State q × Vector q.d =>
      (Equiv.optionEquivSumPUnit.{0, 0} _ w.1.pending, w)) :=
    ((measurable_pendingCode q).comp measurable_fst).prodMk measurable_id
  convert hF.comp hp using 1
  funext w
  rcases w with ⟨s, g⟩
  rcases s with ⟨warm, n, pending, hist, total, y, buf, v⟩
  cases pending <;> rfl

@[fun_prop]
lemma measurable_updateState (q : Public) : Measurable (Function.uncurry (updateState q)) := by
  classical
  have hcond : MeasurableSet {w : State q × Vector q.d | 0 < w.1.warmup} :=
    measurableSet_lt measurable_const ((measurable_warmup q).comp measurable_fst)
  have hm : Measurable (fun w : State q × Vector q.d =>
      if 0 < w.1.warmup then
        { w.1 with warmup := w.1.warmup - 1, history := w.2 :: w.1.history }
      else updateState q { w.1 with warmup := 0 } w.2) :=
    Measurable.ite hcond (measurable_warmupState q) (measurable_update_noWarmup q)
  convert hm using 1
  funext w
  by_cases hw : 0 < w.1.warmup
  · simp [Function.uncurry, updateState, hw]
  · have hz : w.1.warmup = 0 := by omega
    have he : { w.1 with warmup := 0 } = w.1 := by
      rcases w with ⟨⟨warm, n, pending, hist, total, y, buf, v⟩, g⟩
      dsimp at hz ⊢
      subst warm
      rfl
    simp only [hw, ↓reduceIte, he, Function.uncurry]

lemma measurable_advance (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (N call : ℕ) :
    Measurable (fun w : State q × (ℕ → Ω) =>
      StochasticGradient.advance (fun k s => updateState q s (g (queryPoint q s) (w.2 k)))
        N call w.1) := by
  induction N generalizing call with
  | zero => exact measurable_fst
  | succ N ih =>
    have hr : Measurable (fun w : State q × (ℕ → Ω) => g (queryPoint q w.1) (w.2 call)) :=
      hg.comp (((measurable_queryPoint q).comp measurable_fst).prodMk
        ((measurable_pi_apply call).comp measurable_snd))
    have hu := (measurable_updateState q).comp (measurable_fst.prodMk hr)
    simpa only [StochasticGradient.advance, Function.comp_def, Function.uncurry] using
      (ih (call + 1)).comp (hu.prodMk measurable_snd)

lemma measurable_execute_output (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : simplex q.d → Ω → Vector q.d)
    (hg : Measurable (Function.uncurry g)) (N : ℕ) :
    Measurable (fun w : Unit × (ℕ → Ω) =>
      (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ξ => g x ξ }
        (algorithm q) (fun _ => N) w.1 w.2)) := by
  have he : (fun w : Unit × (ℕ → Ω) =>
      (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ξ => g x ξ }
        (algorithm q) (fun _ => N) w.1 w.2)) =
      fun w => (StochasticGradient.advance
        (fun k s => updateState q s (g (queryPoint q s) (w.2 k))) N 0 (initialState q)).y := by
    funext w
    rw [StochasticGradient.execute_advance]
    rfl
  rw [he]
  exact (measurable_y q).comp ((measurable_advance q hg N 0).comp
    (measurable_const.prodMk measurable_snd))

end OracleTemplate.AdaptiveHeavyTailSimplex
