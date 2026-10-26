import LongTailsOnline.Proofs.TaskAllocationPhases
import LongTailsOnline.Proofs.TaskAllocationSchedule

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

structure PhaseInvariant (p : Public) (μ : Worker p.k → ℝ) (s : State p) : Prop where
  intervals : ValidIntervals μ s.2.1
  precision : ∀ i, uncertainty p.B (level (B := p.B) s.2.1.2) s.2.1.1 s.2.1.2 i ≤
    Algorithms.ParallelTaskAllocation.precision p s.2.2.1
  mode : s.2.2.2.2 = 0 ∨ s.2.2.2.2 = 1 ∨ s.2.2.2.2 = 2
  active : s.2.2.2.2 = 1 →
    accuracy p < Algorithms.ParallelTaskAllocation.precision p s.2.2.1 ∧
      accuracy p < level (B := p.B) s.2.1.2 ∧
      (∀ e ∈ s.2.2.2.1,
        (∀ i, e i ≤ capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1 i) ∧
          ∑ i, e i ≤ p.B) ∧
      (∀ i, quota p (Algorithms.ParallelTaskAllocation.precision p s.2.2.1)
        (s.2.1.2 i) (capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1 i) ≤
          s.1.1 i + (s.2.2.2.1.map (fun e => e i)).sum)
  stopped : s.2.2.2.2 = 2 →
    Algorithms.ParallelTaskAllocation.precision p s.2.2.1 ≤ accuracy p ∨
      level (B := p.B) s.2.1.2 ≤ accuracy p

lemma precision_succ (p : Public) (h : ℕ) : precision p (h + 1) = precision p h / 2 := by
  unfold precision
  rw [pow_succ]
  ring

lemma start_invariant {p : Public} (hB : 0 < p.B) {μ : Worker p.k → ℝ}
    (s : Statistics p.k) (ci : Intervals p.k) (h : ℕ)
    (hci : ValidIntervals μ ci)
    (hD : ∀ i, uncertainty p.B (level (B := p.B) ci.2) ci.1 ci.2 i ≤ precision p h) :
    PhaseInvariant p μ (start p s ci h) := by
  have hvalid : ∀ i, ci.1 i ≤ ci.2 i := fun i => (hci i).2.1.trans (hci i).2.2.1
  unfold start
  rw [ite_eq_left hvalid]
  by_cases hstop : precision p h ≤ accuracy p ∨ level (B := p.B) ci.2 ≤ accuracy p
  · rw [ite_eq_left hstop]
    exact ⟨hci, hD, by simp, by simp, fun _ => hstop⟩
  · rw [ite_eq_right hstop]
    dsimp only
    let C := capacity p.B (level (B := p.B) ci.2) ci.1
    let q := fun i => quota p (precision p h) (ci.2 i) (C i)
    refine ⟨hci, hD, by simp, ?_, by simp⟩
    intro _
    refine ⟨lt_of_not_ge (fun hh => hstop (Or.inl hh)),
      lt_of_not_ge (fun hh => hstop (Or.inr hh)), ?_, ?_⟩
    · intro e he
      apply schedule_row_feasible hB q C _ he
      intro i hi
      by_contra hnot
      have hzero : C i = 0 := by omega
      have : q i = 0 := by simp only [q, quota, hzero, ite_true]
      omega
    · intro i
      exact (schedule_quota_bounds q C i).1.trans (Nat.le_add_left _ _)

lemma start_mode {p : Public} {μ : Worker p.k → ℝ} (s : Statistics p.k)
    (ci : Intervals p.k) (h : ℕ) (hci : ValidIntervals μ ci) :
    (start p s ci h).2.2.2.2 = 1 ∨ (start p s ci h).2.2.2.2 = 2 := by
  unfold start
  rw [ite_eq_left (fun i => (hci i).2.1.trans (hci i).2.2.1)]
  split_ifs <;> simp

lemma prepare_invariant {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} (s : State p) (hs : PhaseInvariant p μ s)
    (hnew : ValidIntervals μ (refineIntervals p s.1 s.2.1)) :
    PhaseInvariant p μ (prepare p s) ∧
      ((prepare p s).2.2.2.2 = 1 ∨ (prepare p s).2.2.2.2 = 2) := by
  unfold prepare
  by_cases hzero : s.2.2.2.2 = 0
  · rw [ite_eq_left hzero]
    exact ⟨start_invariant hB s.1 s.2.1 s.2.2.1 hs.intervals hs.precision,
      start_mode s.1 s.2.1 s.2.2.1 hs.intervals⟩
  · rw [ite_eq_right hzero]
    by_cases hdone : s.2.2.2.2 = 1 ∧ s.2.2.2.1 = []
    · rw [ite_eq_left hdone]
      dsimp only
      have hactive := hs.active hdone.1
      have hN : ∀ i, quota p (precision p s.2.2.1) (s.2.1.2 i)
          (capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1 i) ≤ s.1.1 i := by
        intro i
        simpa only [hdone.2, List.map_nil, List.sum_nil, Nat.add_zero] using hactive.2.2.2 i
      have hD := quota_phase_refinement hB hT s.1 s.2.1 hs.intervals hnew hactive.1 hN
      rw [ite_eq_left hD]
      refine ⟨start_invariant hB s.1 _ (s.2.2.1 + 1) hnew ?_,
        start_mode s.1 _ (s.2.2.1 + 1) hnew⟩
      simpa only [precision_succ] using hD
    · rw [ite_eq_right hdone]
      refine ⟨hs, ?_⟩
      rcases hs.mode with hm | hm | hm
      · exact (hzero hm).elim
      · exact Or.inl hm
      · exact Or.inr hm

lemma head_feasible {p : Public} {μ : Worker p.k → ℝ} {s : State p}
    (hs : PhaseInvariant p μ s) (hm : s.2.2.2.2 = 1) :
    (∀ i, s.2.2.2.1.headD (fun _ => 0) i ≤
      capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1 i) ∧
      ∑ i, s.2.2.2.1.headD (fun _ => 0) i ≤ p.B := by
  have hrows := (hs.active hm).2.2.1
  cases heq : s.2.2.2.1 with
  | nil => simp
  | cons e es =>
    simpa only [heq, List.headD_cons] using hrows e (by simp [heq])

lemma select_active_spec {p : Public} {μ : Worker p.k → ℝ} {s : State p}
    (hs : PhaseInvariant p μ s) (hm : s.2.2.2.2 = 1) :
    ∀ i, s.2.2.2.1.headD (fun _ => 0) i ≤ ((select p s).val i).val ∧
      ((select p s).val i).val ≤ capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1 i := by
  have hhead := head_feasible hs hm
  have hb (i) : ((upperOracle (B := p.B) s.2.1.2).val i).val ≤
      capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1 i := by
    apply allocation_le_capacity
    exact loss_mono (fun i => (hs.intervals i).2.1.trans (hs.intervals i).2.2.1) _
  have hspec := fill_spec hb hhead.1 hhead.2
  unfold select
  rw [ite_eq_right (by rw [hm]; decide), ite_eq_left hm]
  exact fun i => ⟨(hspec i).1, (hspec i).2.1⟩

lemma update_invariant {p : Public} {μ : Worker p.k → ℝ} {s : State p}
    (hs : PhaseInvariant p μ s) (f : Feedback p.k p.B) :
    PhaseInvariant p μ (update p s (select p s) f) := by
  refine ⟨hs.intervals, hs.precision, hs.mode, ?_, hs.stopped⟩
  intro hm
  change s.2.2.2.2 = 1 at hm
  have hactive := hs.active hm
  refine ⟨hactive.1, hactive.2.1, ?_, ?_⟩
  · intro e he
    apply hactive.2.2.1 e
    have he' : e ∈ s.2.2.2.1.tail := by
      simpa only [update, ite_eq_left hm] using he
    exact List.mem_of_mem_tail he'
  · intro i
    have hquota := hactive.2.2.2 i
    have hhead := (select_active_spec hs hm i).1
    change quota p (precision p s.2.2.1) (s.2.1.2 i)
      (capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1 i) ≤
      s.1.1 i + ((select p s).val i).val +
        ((if s.2.2.2.2 = 1 then s.2.2.2.1.tail else s.2.2.2.1).map (fun e => e i)).sum
    rw [ite_eq_left hm]
    cases heq : s.2.2.2.1 with
    | nil =>
      simp only [heq, List.map_nil, List.sum_nil, Nat.add_zero] at hquota
      simpa only [List.tail_nil, List.map_nil, List.sum_nil, Nat.add_zero] using
        hquota.trans (Nat.le_add_right _ _)
    | cons e es =>
      simp only [heq, List.map_cons, List.sum_cons] at hquota
      simp only [heq, List.headD_cons] at hhead
      simp only [List.tail_cons]
      omega

lemma initial_phase_invariant {p : Public} {μ : Worker p.k → ℝ}
    (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) : PhaseInvariant p μ (initialState p) := by
  refine ⟨?_, ?_, by simp [initialState], by simp [initialState], by simp [initialState]⟩
  · intro i
    exact ⟨le_rfl, (hμ i).1, (hμ i).2, le_rfl⟩
  · intro i
    simp [initialState, uncertainty, capacity, precision]

lemma trajectory_phase_invariant {p : Params} {w : Sample p.config.k}
    (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1) (hw : w ∉ confidenceFailure p)
    {t : ℕ} (ht : t ≤ p.config.T) :
    PhaseInvariant p.config p.μ (trajectory p.config w t) := by
  induction t with
  | zero => exact initial_phase_invariant hμ
  | succ t ih =>
    have hs := ih (by omega)
    have hnew := refine_intervals_valid hB hT hw (trajectory p.config w t).1
      (trajectory p.config w t).2.1 hs.intervals (fun i => ?_) (statistics_empirical _ _ _)
    · exact update_invariant (prepare_invariant hB hT _ hs hnew).1 _
    · exact (counts_le p.config w t i).trans
        (by nlinarith [Nat.mul_le_mul_right p.config.B (show t ≤ p.config.T by omega)])

lemma prepared_phase_invariant {p : Params} {w : Sample p.config.k}
    (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1) (hw : w ∉ confidenceFailure p)
    {t : ℕ} (ht : t ≤ p.config.T) :
    PhaseInvariant p.config p.μ (prepare p.config (trajectory p.config w t)) ∧
      ((prepare p.config (trajectory p.config w t)).2.2.2.2 = 1 ∨
        (prepare p.config (trajectory p.config w t)).2.2.2.2 = 2) := by
  have hs := trajectory_phase_invariant hB hT hμ hw ht
  apply prepare_invariant hB hT _ hs
  apply refine_intervals_valid hB hT hw _ _ hs.intervals _ (statistics_empirical _ _ _)
  intro i
  exact (counts_le p.config w t i).trans
    (by nlinarith [Nat.mul_le_mul_right p.config.B ht])

lemma select_active_regret {p : Public} {μ : Worker p.k → ℝ} {s : State p}
    (hs : PhaseInvariant p μ s) (hm : s.2.2.2.2 = 1) :
    loss μ (select p s) - optimum (B := p.B) μ ≤ 2 * precision p s.2.2.1 := by
  apply capacity_regret (fun i => (hs.intervals i).1)
    (fun i => (hs.intervals i).2.1) (fun i => (hs.intervals i).2.2.1)
  · simpa only [← level_eq_optimum] using hs.precision
  · simpa only [← level_eq_optimum] using fun i => (select_active_spec hs hm i).2

lemma select_stopped_regret {p : Public} {μ : Worker p.k → ℝ} {s : State p}
    (hs : PhaseInvariant p μ s) (hm : s.2.2.2.2 = 2) :
    loss μ (select p s) - optimum (B := p.B) μ ≤ accuracy p := by
  have hlower : optimum (B := p.B) s.2.1.1 ≤ optimum (B := p.B) μ :=
    optimum_mono (fun i => (hs.intervals i).2.1)
  have hnonneg : 0 ≤ optimum (B := p.B) μ :=
    optimum_nonneg (fun i => (hs.intervals i).1.trans (hs.intervals i).2.1)
  have hupper : loss μ (select p s) ≤ level (B := p.B) s.2.1.2 := by
    unfold select
    rw [ite_eq_left hm]
    exact loss_mono (fun i => (hs.intervals i).2.2.1) _
  rcases hs.stopped hm with hθ | hV
  · have hgap := (precision_gap
      (fun i => (hs.intervals i).2.1.trans (hs.intervals i).2.2.1)
      (by simpa only [← level_eq_optimum] using hs.precision)).2
    rw [← level_eq_optimum] at hgap
    linarith
  · linarith

end LongTailsOnline.Proofs.TaskAllocation
