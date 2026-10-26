import LongTailsOnline.Proofs.TaskAllocationPhaseCosts
import LongTailsOnline.Proofs.TaskAllocationProgress

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

noncomputable def phaseAllowance (p : Public) : ℝ :=
  100000 * scale p * groupLimit p * imbalance p * (1 + 1 / accuracy p)

noncomputable def remainingPotential (p : Public) (μ : Worker p.k → ℝ) (s : State p) : ℝ :=
  if s.2.2.2.2 = 1 then frozenPlanCost (B := p.B) μ s.2.1.2
    (precision p s.2.2.1) s.2.2.2.1 +
      phaseAllowance p * ((phaseLimit p - (s.2.2.1 + 1) : ℕ) : ℝ)
  else if s.2.2.2.2 = 0 then phaseAllowance p * phaseLimit p else 0

lemma phase_allowance_nonneg {p : Public} (hB : 0 < p.B) (hT : 0 < p.T) :
    0 ≤ phaseAllowance p := by
  have hχ : 0 < scale p := by linarith [scale_ge_one hB hT]
  have hd : 0 < imbalance p := by linarith [imbalance_ge_two hB]
  have hacc := accuracy_pos hB hT
  unfold phaseAllowance
  positivity

lemma exploration_load_nonneg {k : ℕ} {u : Worker k → ℝ} (hu : ∀ i, 0 ≤ u i)
    (e : Counts k) : 0 ≤ explorationLoad u e :=
  (mul_nonneg (Nat.cast_nonneg _) (hu 0)).trans
    (Finset.le_sup' (fun i => (e i : ℝ) * u i) (Finset.mem_univ 0))

lemma frozen_plan_cost_nonneg {k B : ℕ} {μ u : Worker k → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hμu : ∀ i, μ i ≤ u i) {θ : ℝ} (hθ : 0 ≤ θ) (plan : Plan k) :
    0 ≤ frozenPlanCost (B := B) μ u θ plan := by
  have hgap : 0 ≤ level (B := B) u - optimum (B := B) μ := by
    rw [level_eq_optimum]
    exact sub_nonneg.mpr (optimum_mono hμu)
  have hsum : 0 ≤ (plan.map (explorationLoad u)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact exploration_load_nonneg hu e
  unfold frozenPlanCost
  split_ifs <;> positivity

lemma frozen_plan_cost_nil {k B : ℕ} (μ u : Worker k → ℝ) (θ : ℝ) :
    frozenPlanCost (B := B) μ u θ [] = 0 := by
  unfold frozenPlanCost
  split_ifs <;> simp

lemma remaining_potential_nonneg {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} {s : State p} (hs : PhaseInvariant p μ s) :
    0 ≤ remainingPotential p μ s := by
  have hF := phase_allowance_nonneg hB hT
  have hcost := frozen_plan_cost_nonneg (B := p.B)
    (fun i => (hs.intervals i).1.trans ((hs.intervals i).2.1.trans (hs.intervals i).2.2.1))
    (fun i => (hs.intervals i).2.2.1)
    (by unfold precision; positivity : 0 ≤ precision p s.2.2.1) s.2.2.2.1
  unfold remainingPotential
  split_ifs <;> positivity

lemma schedule_nonempty {k B : ℕ} {q C : Counts k} (hq : ∃ i, 0 < q i) :
    schedule B q C ≠ [] := by
  intro heq
  obtain ⟨i, hi⟩ := hq
  have htotal := (schedule_quota_bounds (B := B) q C i).1
  simp only [heq, List.map_nil, List.sum_nil] at htotal
  omega

lemma start_active_nonempty {p : Public} (hB : 0 < p.B) {μ : Worker p.k → ℝ}
    (s : Statistics p.k) (ci : Intervals p.k) (h : ℕ) (hci : ValidIntervals μ ci)
    (hm : (start p s ci h).2.2.2.2 = 1) : (start p s ci h).2.2.2.1 ≠ [] := by
  have hvalid : ∀ i, ci.1 i ≤ ci.2 i := fun i => (hci i).2.1.trans (hci i).2.2.1
  unfold start at hm ⊢
  rw [ite_eq_left hvalid] at hm ⊢
  by_cases hstop : precision p h ≤ accuracy p ∨ level (B := p.B) ci.2 ≤ accuracy p
  · rw [ite_eq_left hstop] at hm
    norm_num at hm
  · rw [ite_eq_right hstop]
    dsimp only
    apply schedule_nonempty
    let C := capacity p.B (level (B := p.B) ci.2) ci.1
    have hb (i) : ((upperOracle (B := p.B) ci.2).val i).val ≤ C i := by
      apply allocation_le_capacity
      exact loss_mono hvalid _
    have hC : ∃ i, 0 < C i := by
      by_contra hnot
      push Not at hnot
      have hz (i) : ((upperOracle (B := p.B) ci.2).val i).val = 0 := by
        have := hb i
        have := hnot i
        omega
      have hsum := (upperOracle (B := p.B) ci.2).property
      simp only [hz, Finset.sum_const_zero] at hsum
      omega
    obtain ⟨i, hi⟩ := hC
    exact ⟨i, quota_pos p _ _ hi⟩

lemma prepared_active_nonempty {p : Public} (hB : 0 < p.B)
    {μ : Worker p.k → ℝ} (s : State p) (hs : PhaseInvariant p μ s)
    (hnew : ValidIntervals μ (refineIntervals p s.1 s.2.1))
    (hm : (prepare p s).2.2.2.2 = 1) : (prepare p s).2.2.2.1 ≠ [] := by
  unfold prepare at hm ⊢
  by_cases hzero : s.2.2.2.2 = 0
  · rw [ite_eq_left hzero] at hm ⊢
    exact start_active_nonempty hB _ _ _ hs.intervals hm
  · rw [ite_eq_right hzero] at hm ⊢
    by_cases hdone : s.2.2.2.2 = 1 ∧ s.2.2.2.1 = []
    · rw [ite_eq_left hdone] at hm ⊢
      dsimp only at hm ⊢
      split_ifs with hD
      · rw [ite_eq_left hD] at hm
        exact start_active_nonempty hB _ _ _ hnew hm
      · rw [ite_eq_right hD] at hm
        norm_num at hm
    · rw [ite_eq_right hdone] at hm ⊢
      intro heq
      exact hdone ⟨hm, heq⟩

lemma select_active_loss {p : Public} {μ : Worker p.k → ℝ} {s : State p}
    (hs : PhaseInvariant p μ s) (hm : s.2.2.2.2 = 1) :
    loss μ (select p s) ≤ level (B := p.B) s.2.1.2 +
      explorationLoad s.2.1.2 (s.2.2.2.1.headD (fun _ => 0)) := by
  have hhead := head_feasible hs hm
  have hb (i) : ((upperOracle (B := p.B) s.2.1.2).val i).val ≤
      capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1 i := by
    apply allocation_le_capacity
    exact loss_mono (fun i => (hs.intervals i).2.1.trans (hs.intervals i).2.2.1) _
  apply (loss_mono (fun i => (hs.intervals i).2.2.1) (select p s)).trans
  unfold select
  rw [ite_eq_right (by rw [hm]; decide), ite_eq_left hm]
  exact fill_loss_le
    (fun i => (hs.intervals i).1.trans ((hs.intervals i).2.1.trans (hs.intervals i).2.2.1))
    hb hhead.1 hhead.2

lemma active_regret_le_plan_drop {p : Public} {μ : Worker p.k → ℝ} {s : State p}
    (hs : PhaseInvariant p μ s) (hm : s.2.2.2.2 = 1) (hne : s.2.2.2.1 ≠ []) :
    loss μ (select p s) - optimum (B := p.B) μ ≤
      frozenPlanCost (B := p.B) μ s.2.1.2 (precision p s.2.2.1) s.2.2.2.1 -
        frozenPlanCost (B := p.B) μ s.2.1.2 (precision p s.2.2.1) s.2.2.2.1.tail := by
  cases heq : s.2.2.2.1 with
  | nil => exact (hne heq).elim
  | cons e es =>
    have hloss := select_active_loss hs hm
    simp only [heq, List.headD_cons] at hloss
    have hregret := select_active_regret hs hm
    unfold frozenPlanCost
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.tail_cons, Nat.cast_add,
      Nat.cast_one]
    split_ifs <;> linarith

lemma start_potential_le {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} (hμ : ∀ i, 0 < μ i) (s : Statistics p.k)
    (ci : Intervals p.k) (h : ℕ) (hci : ValidIntervals μ ci)
    (hD : ∀ i, uncertainty p.B (level (B := p.B) ci.2) ci.1 ci.2 i ≤ precision p h) :
    remainingPotential p μ (start p s ci h) ≤
      phaseAllowance p * ((phaseLimit p - h : ℕ) : ℝ) := by
  have hF := phase_allowance_nonneg hB hT
  have hvalid : ∀ i, ci.1 i ≤ ci.2 i := fun i => (hci i).2.1.trans (hci i).2.2.1
  unfold start
  rw [ite_eq_left hvalid]
  by_cases hstop : precision p h ≤ accuracy p ∨ level (B := p.B) ci.2 ≤ accuracy p
  · rw [ite_eq_left hstop]
    change 0 ≤ phaseAllowance p * ((phaseLimit p - h : ℕ) : ℝ)
    positivity
  · rw [ite_eq_right hstop]
    have hθ : accuracy p < precision p h := lt_of_not_ge (fun hh => hstop (Or.inl hh))
    have hV : accuracy p < level (B := p.B) ci.2 := lt_of_not_ge (fun hh => hstop (Or.inr hh))
    have hindex := phase_index_lt_limit hB hT hθ
    have hcost := frozen_plan_cost_bound hB hT ci hci hμ hθ hD hV
    change _ ≤ phaseAllowance p at hcost
    change frozenPlanCost (B := p.B) μ ci.2 (precision p h)
      (schedule p.B (fun i => quota p (precision p h) (ci.2 i)
        (capacity p.B (level (B := p.B) ci.2) ci.1 i))
          (capacity p.B (level (B := p.B) ci.2) ci.1)) +
      phaseAllowance p * ((phaseLimit p - (h + 1) : ℕ) : ℝ) ≤
        phaseAllowance p * ((phaseLimit p - h : ℕ) : ℝ)
    have hnat : phaseLimit p - h = phaseLimit p - (h + 1) + 1 := by omega
    rw [hnat, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    change _ + phaseAllowance p * ((phaseLimit p - (h + 1) : ℕ) : ℝ) ≤
      phaseAllowance p * ((phaseLimit p - (h + 1) : ℕ) : ℝ) + phaseAllowance p
    linarith

lemma prepare_potential_le {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} (hμ : ∀ i, 0 < μ i) (s : State p) (hs : PhaseInvariant p μ s)
    (hnew : ValidIntervals μ (refineIntervals p s.1 s.2.1)) :
    remainingPotential p μ (prepare p s) ≤ remainingPotential p μ s := by
  have hF := phase_allowance_nonneg hB hT
  unfold prepare
  by_cases hzero : s.2.2.2.2 = 0
  · rw [ite_eq_left hzero]
    have hsp : remainingPotential p μ s = phaseAllowance p * phaseLimit p := by
      unfold remainingPotential
      rw [ite_eq_right (by rw [hzero]; decide), ite_eq_left hzero]
    rw [hsp]
    exact (start_potential_le hB hT hμ s.1 s.2.1 s.2.2.1 hs.intervals hs.precision).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le (phaseLimit p) s.2.2.1) hF)
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
      have hsp : remainingPotential p μ s =
          phaseAllowance p * ((phaseLimit p - (s.2.2.1 + 1) : ℕ) : ℝ) := by
        unfold remainingPotential
        rw [ite_eq_left hdone.1, hdone.2, frozen_plan_cost_nil, zero_add]
      rw [hsp]
      apply start_potential_le hB hT hμ s.1 _ (s.2.2.1 + 1) hnew
      simpa only [precision_succ] using hD
    · rw [ite_eq_right hdone]

lemma update_potential_regret {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} {s : State p} (hs : PhaseInvariant p μ s)
    (hm : s.2.2.2.2 = 1 ∨ s.2.2.2.2 = 2)
    (hne : s.2.2.2.2 = 1 → s.2.2.2.1 ≠ []) (f : Feedback p.k p.B) :
    loss μ (select p s) - optimum (B := p.B) μ ≤
      remainingPotential p μ s - remainingPotential p μ (update p s (select p s) f) +
        accuracy p := by
  have hacc := accuracy_pos hB hT
  rcases hm with hm | hm
  · have hd := active_regret_le_plan_drop hs hm (hne hm)
    have heq : remainingPotential p μ s - remainingPotential p μ (update p s (select p s) f) =
        frozenPlanCost (B := p.B) μ s.2.1.2 (precision p s.2.2.1) s.2.2.2.1 -
          frozenPlanCost (B := p.B) μ s.2.1.2 (precision p s.2.2.1) s.2.2.2.1.tail := by
      simp only [remainingPotential, update, ite_eq_left hm]
      ring
    rw [heq]
    linarith
  · have hr := select_stopped_regret hs hm
    have h1 : s.2.2.2.2 ≠ 1 := by rw [hm]; decide
    have h0 : s.2.2.2.2 ≠ 0 := by rw [hm]; decide
    simpa only [remainingPotential, update, ite_eq_right h1, ite_eq_right h0, sub_self,
      zero_add] using hr

lemma trajectory_potential_step {p : Params} {w : Sample p.config.k}
    (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ : ∀ i, p.μ i ∈ Set.Ioc (0 : ℝ) 1) (hw : w ∉ confidenceFailure p)
    {t : ℕ} (ht : t < p.config.T) :
    loss p.μ (play p.config w t) - optimum (B := p.config.B) p.μ ≤
      remainingPotential p.config p.μ (trajectory p.config w t) -
        remainingPotential p.config p.μ (trajectory p.config w (t + 1)) + accuracy p.config := by
  have hμ' (i) : p.μ i ∈ Set.Icc (0 : ℝ) 1 := ⟨(hμ i).1.le, (hμ i).2⟩
  have hs := trajectory_phase_invariant hB hT hμ' hw ht.le
  have hnew := refine_intervals_valid hB hT hw (trajectory p.config w t).1
    (trajectory p.config w t).2.1 hs.intervals (fun i => ?_) (statistics_empirical _ _ _)
  · have hp := prepare_invariant hB hT _ hs hnew
    have hstep := update_potential_regret hB hT hp.1 hp.2
      (fun hm => prepared_active_nonempty hB _ hs hnew hm)
      (batch w (trajectory p.config w t).1.1 (play p.config w t))
    have hprepare := prepare_potential_le hB hT (fun i => (hμ i).1) _ hs hnew
    exact hstep.trans (add_le_add (sub_le_sub_right hprepare _) le_rfl)
  · exact (counts_le p.config w t i).trans
      (by nlinarith [Nat.mul_le_mul_right p.config.B ht.le])

end LongTailsOnline.Proofs.TaskAllocation
