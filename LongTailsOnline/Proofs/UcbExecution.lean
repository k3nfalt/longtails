import LongTailsOnline.Algorithms.Ucb

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Proofs.Ucb

open LongTailsOnline.Setups.StochasticBandit LongTailsOnline.Algorithms.Ucb

noncomputable def trajectory {k : ℕ} (w : Sample k) : ℕ → Statistics k
  | 0 => (fun _ => 0, fun _ => 0)
  | t + 1 =>
    let s := trajectory w t
    let a := select t s
    record s a (w (a, s.1 a))

noncomputable def play {k : ℕ} (w : Sample k) (t : ℕ) : Arm k := select t (trajectory w t)

noncomputable def reward {k : ℕ} (w : Sample k) (t : ℕ) : ℝ :=
  w (play w t, (trajectory w t).1 (play w t))

@[fun_prop]
lemma measurable_trajectory (k t : ℕ) : Measurable (fun w : Sample k => trajectory w t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    change Measurable (fun w : Sample k =>
      record (trajectory w t) (select t (trajectory w t))
        (w (select t (trajectory w t), (trajectory w t).1 (select t (trajectory w t)))))
    have ha := (measurable_select k t).comp ih
    have hn := measurable_eval_countable ih.fst ha
    have hr := measurable_eval_countable measurable_id (ha.prodMk hn)
    exact (measurable_record k).comp (ih.prodMk (ha.prodMk hr))

@[fun_prop]
lemma measurable_play (k t : ℕ) : Measurable (fun w : Sample k => play w t) :=
  (measurable_select k t).comp (measurable_trajectory k t)

@[fun_prop]
lemma measurable_reward (k t : ℕ) : Measurable (fun w : Sample k => reward w t) := by
  apply measurable_eval_countable measurable_id
  exact (measurable_play k t).prodMk
    (measurable_eval_countable (measurable_trajectory k t).fst (measurable_play k t))

noncomputable def history {k : ℕ} (w : Sample k) :
    (T : ℕ) → OnlineTemplate.Trace Unit (Arm k) ℝ Unit T
  | 0 => fun i => Fin.elim0 i
  | T + 1 => OnlineTemplate.Trace.append (history w T) ((), play w T, reward w T, ())

@[fun_prop]
lemma measurable_history (k T : ℕ) : Measurable (fun w : Sample k => history w T) := by
  induction T with
  | zero => exact measurable_const
  | succ T ih =>
    exact OnlineTemplate.Trace.measurable_append.comp
      (ih.prodMk (measurable_const.prodMk
        ((measurable_play k T).prodMk ((measurable_reward k T).prodMk measurable_const))))

lemma history_apply {k T : ℕ} (w : Sample k) (i : Fin T) :
    history w T i = ((), play w i.val, reward w i.val, ()) := by
  induction T with
  | zero => exact Fin.elim0 i
  | succ T ih =>
    simp only [history, OnlineTemplate.Trace.append]
    split_ifs with hi
    · exact ih ⟨i.val, hi⟩
    · have he : i.val = T := by omega
      simp [he]

noncomputable def joint {k : ℕ} (P : ProbabilityMeasure (Sample k)) (w : Sample k) (T : ℕ) :
    OnlineTemplate.RunState (algorithm k) (environment P) T :=
  (trajectory w T, (w, (trajectory w T).1), history w T)

@[fun_prop]
lemma measurable_joint {k : ℕ} (P : ProbabilityMeasure (Sample k)) (T : ℕ) :
    Measurable (fun w => joint P w T) := by
  unfold joint
  fun_prop

lemma step_joint {k : ℕ} (P : ProbabilityMeasure (Sample k)) (w : Sample k) (t : ℕ) :
    OnlineTemplate.step (algorithm k) (environment P) t (joint P w t) =
      Measure.dirac (joint P w (t + 1)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [OnlineTemplate.lintegral_step _ _ _ _ _ hf]
  simp only [algorithm, environment, Kernel.deterministic_apply, joint,
    lintegral_dirac]
  rfl

lemma execution_joint {k : ℕ} (P : ProbabilityMeasure (Sample k)) (T : ℕ) :
    OnlineTemplate.executionKernel (algorithm k) (environment P) T () =
      P.toMeasure.map (fun w => joint P w T) := by
  induction T with
  | zero =>
    rw [OnlineTemplate.executionKernel_zero_apply]
    change ((Measure.dirac (fun _ : Arm k => 0, fun _ : Arm k => (0 : ℝ))).prod
      (P.toMeasure.map (fun w => (w, fun _ => 0)))).map _ = _
    rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  | succ T ih =>
    rw [OnlineTemplate.executionKernel_succ_apply, ih]
    unfold Measure.bind
    rw [Measure.map_map (OnlineTemplate.step _ _ _).measurable (measurable_joint P T)]
    have he : (fun w => OnlineTemplate.step (algorithm k) (environment P) T (joint P w T)) =
        fun w => Measure.dirac (joint P w (T + 1)) := by
      funext w
      exact step_joint P w T
    change (P.toMeasure.map (fun w =>
      OnlineTemplate.step (algorithm k) (environment P) T (joint P w T))).join = _
    rw [he]
    exact Measure.bind_dirac_eq_map P.toMeasure (measurable_joint P (T + 1))

lemma execute_history {k : ℕ} (P : ProbabilityMeasure (Sample k)) (T : ℕ) :
    (OnlineTemplate.execute (algorithm k) (environment P) T).toMeasure =
      P.toMeasure.map (fun w => history w T) := by
  rw [OnlineTemplate.execute_toMeasure, execution_joint,
    Measure.map_map (by fun_prop) (measurable_joint P T)]
  rfl

lemma count_succ {k : ℕ} (w : Sample k) (t : ℕ) (i : Arm k) :
    (trajectory w (t + 1)).1 i = (trajectory w t).1 i + if i = play w t then 1 else 0 := rfl

lemma count_le {k : ℕ} (w : Sample k) (t : ℕ) (i : Arm k) :
    (trajectory w t).1 i ≤ t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => rw [count_succ]; split_ifs <;> omega

lemma count_pos {k : ℕ} (w : Sample k) (t : ℕ) (i : Arm k) (hi : i.val < t) :
    0 < (trajectory w t).1 i := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [count_succ]
    by_cases hit : i.val < t
    · have := ih hit
      omega
    · have he : i.val = t := by omega
      have hp : play w t = i := by
        simp only [play, select, ite_eq_left (show t < k + 1 by omega)]
        rw [← he, armOfNat_val]
      simp [hp]

lemma total_eq_empirical {k : ℕ} (w : Sample k) (t : ℕ) (i : Arm k) :
    (trajectory w t).2 i = ∑ n ∈ Finset.range ((trajectory w t).1 i), w (i, n) := by
  induction t with
  | zero => simp [trajectory]
  | succ t ih =>
    change (trajectory w t).2 i + (if i = play w t then reward w t else 0) = _
    rw [count_succ]
    by_cases hi : i = play w t
    · simp only [hi, ite_true, Finset.sum_range_succ, reward]
      rw [← hi, ih]
    · simp [hi, ih]

lemma index_eq_empirical {k : ℕ} (w : Sample k) (t : ℕ) (i : Arm k) :
    index t (trajectory w t) i = empirical w i ((trajectory w t).1 i) +
      radius t ((trajectory w t).1 i) := by rw [index, empirical, total_eq_empirical]

end LongTailsOnline.Proofs.Ucb
