import LongTailsOnline.Algorithms.ParallelTaskAllocation

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

lemma start_statistics (p : Public) (s : Statistics p.k) (ci : Intervals p.k) (h : ℕ) :
    (start p s ci h).1 = s := by
  unfold start
  split_ifs <;> rfl

lemma prepare_statistics (p : Public) (s : State p) : (prepare p s).1 = s.1 := by
  unfold prepare
  split_ifs <;> (try dsimp only)
  all_goals (try split_ifs) <;> simp only [start_statistics]

noncomputable def trajectory (p : Public) (w : Sample p.k) : ℕ → State p
  | 0 => initialState p
  | t + 1 =>
    let s := trajectory p w t
    let prepared := prepare p s
    let a := select p prepared
    update p prepared a (batch w s.1.1 a)

noncomputable def play (p : Public) (w : Sample p.k) (t : ℕ) : Allocation p.k p.B :=
  select p (prepare p (trajectory p w t))

noncomputable def response (p : Public) (w : Sample p.k) (t : ℕ) : Feedback p.k p.B :=
  batch w (trajectory p w t).1.1 (play p w t)

@[fun_prop]
lemma measurable_trajectory (p : Public) (t : ℕ) :
    Measurable (fun w : Sample p.k => trajectory p w t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hp := (measurable_prepare p).comp ih
    have ha := (measurable_select p).comp hp
    have hf := (measurable_batch p.k p.B).comp
      (measurable_id.prodMk (ih.fst.fst.prodMk ha))
    exact (measurable_update p).comp (hp.prodMk (ha.prodMk hf))

@[fun_prop]
lemma measurable_play (p : Public) (t : ℕ) : Measurable (fun w : Sample p.k => play p w t) :=
  (measurable_select p).comp ((measurable_prepare p).comp (measurable_trajectory p t))

@[fun_prop]
lemma measurable_response (p : Public) (t : ℕ) :
    Measurable (fun w : Sample p.k => response p w t) :=
  (measurable_batch p.k p.B).comp (measurable_id.prodMk
    ((measurable_trajectory p t).fst.fst.prodMk (measurable_play p t)))

noncomputable def history (p : Public) (w : Sample p.k) :
    (T : ℕ) → OnlineTemplate.Trace Unit (Allocation p.k p.B) (Feedback p.k p.B) Unit T
  | 0 => fun i => Fin.elim0 i
  | T + 1 => OnlineTemplate.Trace.append (history p w T) ((), play p w T, response p w T, ())

@[fun_prop]
lemma measurable_history (p : Public) (T : ℕ) :
    Measurable (fun w : Sample p.k => history p w T) := by
  induction T with
  | zero => exact measurable_const
  | succ T ih =>
    exact OnlineTemplate.Trace.measurable_append.comp
      (ih.prodMk (measurable_const.prodMk ((measurable_play p T).prodMk
        ((measurable_response p T).prodMk measurable_const))))

lemma history_apply (p : Public) (w : Sample p.k) {T : ℕ} (i : Fin T) :
    history p w T i = ((), play p w i.val, response p w i.val, ()) := by
  induction T with
  | zero => exact Fin.elim0 i
  | succ T ih =>
    simp only [history, OnlineTemplate.Trace.append]
    split_ifs with hi
    · exact ih ⟨i.val, hi⟩
    · have he : i.val = T := by omega
      simp [he]

lemma counts_succ (p : Public) (w : Sample p.k) (t : ℕ) :
    (trajectory p w (t + 1)).1.1 = increment (trajectory p w t).1.1 (play p w t) := by
  change increment (prepare p (trajectory p w t)).1.1 (play p w t) = _
  rw [prepare_statistics]

noncomputable def joint (p : Public) (P : ProbabilityMeasure (Sample p.k))
    (w : Sample p.k) (T : ℕ) : OnlineTemplate.RunState (algorithm p) (environment P) T :=
  (trajectory p w T, (w, (trajectory p w T).1.1), history p w T)

@[fun_prop]
lemma measurable_joint (p : Public) (P : ProbabilityMeasure (Sample p.k)) (T : ℕ) :
    Measurable (fun w => joint p P w T) := by
  unfold joint
  fun_prop

lemma step_joint (p : Public) (P : ProbabilityMeasure (Sample p.k)) (w : Sample p.k) (t : ℕ) :
    OnlineTemplate.step (algorithm p) (environment P) t (joint p P w t) =
      Measure.dirac (joint p P w (t + 1)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [OnlineTemplate.lintegral_step _ _ _ _ _ hf, lintegral_dirac' _ hf]
  simp only [algorithm, environment, Kernel.deterministic_apply, joint, lintegral_dirac]
  apply congrArg f
  change (trajectory p w (t + 1), (w, increment (trajectory p w t).1.1 (play p w t)),
    history p w (t + 1)) = _
  rw [← counts_succ]

lemma execution_joint (p : Public) (P : ProbabilityMeasure (Sample p.k)) (T : ℕ) :
    OnlineTemplate.executionKernel (algorithm p) (environment P) T () =
      P.toMeasure.map (fun w => joint p P w T) := by
  induction T with
  | zero =>
    rw [OnlineTemplate.executionKernel_zero_apply]
    change ((Measure.dirac (initialState p)).prod
      (P.toMeasure.map (fun w => (w, fun _ => 0)))).map _ = _
    rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  | succ T ih =>
    rw [OnlineTemplate.executionKernel_succ_apply, ih]
    unfold Measure.bind
    rw [Measure.map_map (OnlineTemplate.step _ _ _).measurable (measurable_joint p P T)]
    have he : (fun w => OnlineTemplate.step (algorithm p) (environment P) T (joint p P w T)) =
        fun w => Measure.dirac (joint p P w (T + 1)) := by
      funext w
      exact step_joint p P w T
    change (P.toMeasure.map (fun w =>
      OnlineTemplate.step (algorithm p) (environment P) T (joint p P w T))).join = _
    rw [he]
    exact Measure.bind_dirac_eq_map P.toMeasure (measurable_joint p P (T + 1))

lemma execute_history (p : Public) (P : ProbabilityMeasure (Sample p.k)) (T : ℕ) :
    (OnlineTemplate.execute (algorithm p) (environment P) T).toMeasure =
      P.toMeasure.map (fun w => history p w T) := by
  rw [OnlineTemplate.execute_toMeasure, execution_joint,
    Measure.map_map (by fun_prop) (measurable_joint p P T)]
  rfl

lemma counts_le (p : Public) (w : Sample p.k) (t : ℕ) (i : Worker p.k) :
    (trajectory p w t).1.1 i ≤ t * p.B := by
  induction t with
  | zero => simp [trajectory, initialState]
  | succ t ih =>
    rw [counts_succ]
    have ha : ((play p w t).val i).val ≤ p.B := Nat.le_of_lt_succ ((play p w t).val i).isLt
    simp only [increment, Nat.succ_mul]
    omega

lemma total_counts (p : Public) (w : Sample p.k) (t : ℕ) :
    ∑ i, (trajectory p w t).1.1 i = t * p.B := by
  induction t with
  | zero => simp [trajectory, initialState]
  | succ t ih =>
    rw [counts_succ]
    simp only [increment, Finset.sum_add_distrib, ih, (play p w t).property, Nat.succ_mul]

lemma sum_fin_indicator {B a : ℕ} (ha : a ≤ B) (f : ℕ → ℝ) :
    (∑ j : Fin B, if j.val < a then f j.val else 0) = ∑ j ∈ Finset.range a, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < a then f j else 0) B]
  rw [← Finset.sum_filter]
  have heq : (Finset.range B).filter (fun j => j < a) = Finset.range a := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [heq]

lemma record_batch_total {k B : ℕ} (H : ℝ) (w : Sample k) (s : Statistics k)
    (a : Allocation k B) (i : Worker k) :
    (record H s a (batch w s.1 a)).2 i =
      s.2 i + ∑ j ∈ Finset.range (a.val i).val, clipped H w i (s.1 i + j) := by
  change s.2 i + (∑ j : Fin B, if j.val < (a.val i).val then
    min (batch w s.1 a i j) H else 0) = _
  congr 1
  calc
    _ = ∑ j : Fin B, if j.val < (a.val i).val then
        clipped H w i (s.1 i + j.val) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val < (a.val i).val <;> simp [batch, clipped, hj]
    _ = _ := sum_fin_indicator (Nat.le_of_lt_succ (a.val i).isLt)
      (fun j => clipped H w i (s.1 i + j))

lemma total_eq_sum (p : Public) (w : Sample p.k) (t : ℕ) (i : Worker p.k) :
    (trajectory p w t).1.2 i = ∑ j ∈ Finset.range ((trajectory p w t).1.1 i),
      clipped (clipLevel p) w i j := by
  induction t with
  | zero => simp [trajectory, initialState]
  | succ t ih =>
    change (record (clipLevel p) (prepare p (trajectory p w t)).1 (play p w t)
      (batch w (trajectory p w t).1.1 (play p w t))).2 i = _
    rw [prepare_statistics, record_batch_total, counts_succ]
    change (trajectory p w t).1.2 i + _ =
      ∑ j ∈ Finset.range ((trajectory p w t).1.1 i + ((play p w t).val i).val), _
    rw [Finset.sum_range_add, ih]

lemma statistics_empirical (p : Public) (w : Sample p.k) (t : ℕ) (i : Worker p.k) :
    (trajectory p w t).1.2 i / (trajectory p w t).1.1 i =
      empirical (clipLevel p) w i ((trajectory p w t).1.1 i) := by
  rw [total_eq_sum]
  rfl

end LongTailsOnline.Proofs.TaskAllocation
