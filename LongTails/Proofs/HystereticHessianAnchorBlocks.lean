import LongTails.Proofs.HystereticHessianBlocks

namespace LongTails.Proofs.HystereticHessianAnchorBlocks

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianMoments HystereticHessianBlocks HeavyTailedProductProcess
open OracleTemplate.StochasticGeneralized

lemma anchoredPath_add (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : AnchoredState p c) (ξ : ℕ → ℝ × Ω) (m n : ℕ) :
    anchoredPath p c answer s ξ (m + n) =
      anchoredPath p c answer (anchoredPath p c answer s ξ m) (fun k => ξ (m + k)) n :=
  HeavyTailedSospEpochIntegration.trajectory_add _ _ _ _ _

lemma anchored_gradient_prefix (p : Params) (c : Config) (s : State p c) (a : Space p)
    (refresh : Bool) (j : Fin (c.groups + 1)) (values : Fin (c.groups + 1) → Space p)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ) (ha : s.active = true)
    (hn : n ≤ if refresh then c.resetBatch else c.pilotBatch)
    (ht : s.slot + n < macroCalls c) :
    anchoredPath p c answer ⟨{ s with phase := .gradient refresh j 0 0 values }, a⟩ ξ n =
      ⟨{ s with
        slot := s.slot + n
        phase := .gradient refresh j n
          (∑ k ∈ Finset.range n, answer (s.point, none) (ξ k).2) values }, a⟩ := by
  induction n with
  | zero => simp [anchoredPath, trajectory]
  | succ n ih =>
    have hi : n < if refresh then c.resetBatch else c.pilotBatch := by omega
    have hclock : s.slot + n + 1 < macroCalls c := by omega
    rw [anchoredPath, trajectory_succ_last]
    change anchoredUpdate p c (anchoredPath p c answer _ ξ n) (ξ n).1
      (answer (query p c (anchoredPath p c answer _ ξ n).value (ξ n).1) (ξ n).2) = _
    simp only [ih (by omega) (by omega)]
    cases refresh <;>
      simp_all [anchoredUpdate, update, rawUpdate, query, nextAnchor,
        Finset.sum_range_succ, Nat.add_assoc]

noncomputable def finishAnchor (p : Params) (c : Config) (refresh : Bool)
    (s : State p c) (a : Space p) (values : Fin (c.groups + 1) → Space p) : Space p :=
  if refresh then a else
    if c.guardThreshold < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid values‖ then a
    else s.point

lemma anchoredState_ext (p : Params) (c : Config) (s t : AnchoredState p c)
    (hv : s.value = t.value) (ha : s.anchor = t.anchor) : s = t := by
  cases s
  cases t
  simp_all

lemma anchored_gradient_group (p : Params) (c : Config) (s : State p c) (a : Space p)
    (refresh : Bool) (j : Fin (c.groups + 1)) (values : Fin (c.groups + 1) → Space p)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + ((if refresh then c.resetBatch else c.pilotBatch) + 1) < macroCalls c) :
    anchoredPath p c answer ⟨{ s with phase := .gradient refresh j 0 0 values }, a⟩ ξ
      ((if refresh then c.resetBatch else c.pilotBatch) + 1) =
      let b := if refresh then c.resetBatch else c.pilotBatch
      let values' := Function.update values j
        (((b + 1 : ℕ) : ℝ)⁻¹ •
          ∑ k ∈ Finset.range (b + 1), answer (s.point, none) (ξ k).2)
      if hj : j.val + 1 < c.groups + 1 then
        ⟨{ s with
          slot := s.slot + (b + 1)
          phase := .gradient refresh ⟨j.val + 1, hj⟩ 0 0 values' }, a⟩
      else ⟨finishGradient p c refresh { s with slot := s.slot + (b + 1) } values',
        finishAnchor p c refresh s a values'⟩ := by
  apply anchoredState_ext
  · rw [anchoredPath_projection]
    have hv := gradient_group p c s refresh j values answer ξ ha ht
    by_cases hj : j.val + 1 < c.groups + 1
    · simpa only [hj, dite_true] using hv
    · simpa only [hj, dite_false] using hv
  · let b := if refresh then c.resetBatch else c.pilotBatch
    rw [anchoredPath, trajectory_succ_last]
    change (anchoredUpdate p c (anchoredPath p c answer _ ξ b) (ξ b).1
      (answer (query p c (anchoredPath p c answer _ ξ b).value (ξ b).1) (ξ b).2)).anchor = _
    simp only [anchored_gradient_prefix p c s a refresh j values answer ξ b ha le_rfl (by omega)]
    cases refresh <;>
      simp_all [anchoredUpdate, nextAnchor, query, finishAnchor, b, Finset.sum_range_succ]
    all_goals split_ifs <;> rfl


lemma anchored_gradient_groups_prefix (p : Params) (c : Config) (s : State p c) (a : Space p)
    (refresh : Bool) {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (j : ℕ) (hj : j ≤ c.groups) (ha : s.active = true)
    (ht : s.slot + j * ((if refresh then c.resetBatch else c.pilotBatch) + 1) < macroCalls c) :
    anchoredPath p c answer ⟨{ s with phase := .gradient refresh 0 0 0 (fun _ => 0) }, a⟩ ξ
      (j * ((if refresh then c.resetBatch else c.pilotBatch) + 1)) =
      ⟨{ s with
        slot := s.slot + j * ((if refresh then c.resetBatch else c.pilotBatch) + 1)
        phase := .gradient refresh ⟨j, by omega⟩ 0 0
          (fun k => if k.val < j then
            (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
              ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
                answer (s.point, none)
                  (ξ (k.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2
            else 0) }, a⟩ := by
  let b := if refresh then c.resetBatch else c.pilotBatch
  induction j with
  | zero => simp [anchoredPath, trajectory]
  | succ j ih =>
    have htime : s.slot + j * (b + 1) + (b + 1) < macroCalls c := by
      simpa only [Nat.succ_mul, Nat.add_assoc] using ht
    have hbefore : s.slot + j * ((if refresh then c.resetBatch else c.pilotBatch) + 1) <
        macroCalls c := lt_of_le_of_lt (Nat.le_add_right _ _) htime
    rw [Nat.succ_mul, anchoredPath_add, ih (by omega) hbefore]
    rw [anchored_gradient_group p c { s with slot := s.slot + j * (b + 1) } a refresh
      ⟨j, by omega⟩ _ answer _ ha htime]
    simp only [show j + 1 < c.groups + 1 by omega, dite_true]
    rw [GuardedHessianExecution.prefix_values_update]
    simp only [b, Nat.add_assoc]

lemma anchored_gradient_pass (p : Params) (c : Config) (s : State p c) (a : Space p)
    (refresh : Bool) {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + (c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1) <
      macroCalls c) :
    anchoredPath p c answer ⟨{ s with phase := .gradient refresh 0 0 0 (fun _ => 0) }, a⟩ ξ
      ((c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1)) =
      let values := fun j : Fin (c.groups + 1) =>
        (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
          ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
            answer (s.point, none)
              (ξ (j.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2
      ⟨finishGradient p c refresh
        { s with slot := s.slot + (c.groups + 1) *
          ((if refresh then c.resetBatch else c.pilotBatch) + 1) } values,
        finishAnchor p c refresh s a values⟩ := by
  let b := if refresh then c.resetBatch else c.pilotBatch
  have htime : s.slot + c.groups * (b + 1) + (b + 1) < macroCalls c := by
    simpa only [Nat.succ_mul, Nat.add_assoc] using ht
  have hbefore : s.slot + c.groups * ((if refresh then c.resetBatch else c.pilotBatch) + 1) <
      macroCalls c := lt_of_le_of_lt (Nat.le_add_right _ _) htime
  rw [Nat.succ_mul, anchoredPath_add,
    anchored_gradient_groups_prefix p c s a refresh answer ξ _ le_rfl ha hbefore]
  rw [anchored_gradient_group p c { s with slot := s.slot + c.groups * (b + 1) } a refresh
    ⟨c.groups, by omega⟩ _ answer _ ha htime]
  simp only [lt_self_iff_false, dite_false]
  rw [GuardedHessianExecution.prefix_values_update]
  simp only [Fin.is_lt, ite_true, b, Nat.add_assoc, finishAnchor]

lemma anchoredPath_constant_anchor (p : Params) (c : Config) (s : State p c) (a : Space p)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ)
    (ha : ∀ k < n, nextAnchor p c ⟨path p c answer s ξ k, a⟩
      (answer (query p c (path p c answer s ξ k) (ξ k).1) (ξ k).2) = a) :
    anchoredPath p c answer ⟨s, a⟩ ξ n = ⟨path p c answer s ξ n, a⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun k hk => ha k (by omega))
    rw [anchoredPath, trajectory_succ_last]
    change anchoredUpdate p c (anchoredPath p c answer ⟨s, a⟩ ξ n) (ξ n).1
      (answer (query p c (anchoredPath p c answer ⟨s, a⟩ ξ n).value (ξ n).1) (ξ n).2) = _
    simp only [hp, anchoredUpdate]
    rw [ha n (by omega)]
    simp only [path, trajectory_succ_last]

lemma transport_anchor (p : Params) (c : Config) (s : State p c) (a : Space p)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + (c.transportBatch + 1) < macroCalls c) :
    anchoredPath p c answer ⟨{ s with phase := .transport 0 0 }, a⟩ ξ (c.transportBatch + 1) =
      ⟨path p c answer { s with phase := .transport 0 0 } ξ (c.transportBatch + 1), a⟩ := by
  apply anchoredPath_constant_anchor
  intro k hk
  simp only [transport_prefix p c s answer ξ k ha (by omega) (by omega)]
  simp [nextAnchor, ha]

lemma padding_anchor (p : Params) (c : Config) (s : State p c) (a : Space p)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hp : s.active = false ∨ s.phase = .padding)
    (ht : s.slot < macroCalls c) :
    anchoredPath p c answer ⟨s, a⟩ ξ (macroCalls c - s.slot) =
      ⟨{ s with slot := 0, inner := 0, phase := .gradient false 0 0 0 (fun _ => 0) }, a⟩ := by
  rw [anchoredPath_constant_anchor p c s a answer ξ _ (by
    intro k hk
    simp only [padding_prefix p c s answer ξ k hp (by omega)]
    rcases hp with ha | hp
    · simp [nextAnchor, ha]
    · simp [nextAnchor, hp])]
  rw [padding_pass p c s answer ξ hp ht]

lemma refresh_potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (a : Space p) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + resetCalls c < macroCalls c) :
    potential p c g (anchoredPath p c answer
      ⟨{ s with phase := .gradient true 0 0 0 (fun _ => 0) }, a⟩ ξ (resetCalls c)) =
      potential p c g ⟨s, a⟩ := by
  rw [show resetCalls c = (c.groups + 1) * (c.resetBatch + 1) from rfl]
  have hout := anchored_gradient_pass p c s a true answer ξ ha ht
  simp only [ite_true] at hout
  rw [hout]
  simp only [finishGradient, finishAnchor, ite_true]
  trans ‖g a‖ ^ 2
  · apply beginFineStep_potential
    exact ha
  · simp [potential, ha]

lemma pilot_potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (a : Space p) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + pilotCalls c < macroCalls c) :
    potential p c g (anchoredPath p c answer
      ⟨{ s with phase := .gradient false 0 0 0 (fun _ => 0) }, a⟩ ξ (pilotCalls c)) =
      let v := OracleTemplate.MultiplicativeRobustEstimator.medoid
        (fun j : Fin (c.groups + 1) => ((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ •
          ∑ l ∈ Finset.range (c.pilotBatch + 1),
            answer (s.point, none) (ξ (j.val * (c.pilotBatch + 1) + l)).2)
      if c.guardThreshold < ‖v‖ then 0 else ‖g s.point‖ ^ 2 := by
  rw [show pilotCalls c = (c.groups + 1) * (c.pilotBatch + 1) from rfl]
  have hout := anchored_gradient_pass p c s a false answer ξ ha ht
  simp only [Bool.false_eq_true, ite_false] at hout
  rw [hout]
  simp only [finishGradient, finishAnchor, Bool.false_eq_true, ite_false]
  exact finishPilot_potential p c g _ a _ ha

lemma transport_potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (a : Space p) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + (c.transportBatch + 1) < macroCalls c) :
    potential p c g (anchoredPath p c answer
      ⟨{ s with phase := .transport 0 0 }, a⟩ ξ (c.transportBatch + 1)) =
      potential p c g ⟨s, a⟩ := by
  rw [transport_anchor p c s a answer ξ ha ht, transport_pass p c s answer ξ ha ht]
  simp [potential, ha]

lemma padding_potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (a : Space p) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hp : s.active = false ∨ s.phase = .padding)
    (ht : s.slot < macroCalls c) :
    potential p c g (anchoredPath p c answer ⟨s, a⟩ ξ (macroCalls c - s.slot)) =
      potential p c g ⟨s, a⟩ := by
  rw [padding_anchor p c s a answer ξ hp ht]
  rfl

abbrev AnchoredTimedState (p : Params) (c : Config) := AnchoredState p c × ℕ

def forgetAnchor (p : Params) (c : Config) (s : AnchoredTimedState p c) : TimedState p c :=
  (s.1.value, s.2)

def anchoredTimedCost (p : Params) (c : Config) (s : AnchoredTimedState p c) : ℕ :=
  timedCost p c (forgetAnchor p c s)

noncomputable def anchoredTimedAdvance (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : AnchoredTimedState p c) (z : ℝ × Ω) : AnchoredTimedState p c :=
  (anchoredUpdate p c s.1 z.1 (answer (query p c s.1.value z.1) z.2), s.2 + 1)

lemma forgetAnchor_advance (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : AnchoredTimedState p c) (z : ℝ × Ω) :
    forgetAnchor p c (anchoredTimedAdvance p c answer s z) =
      timedAdvance p c answer (forgetAnchor p c s) z := rfl

lemma anchored_timed_trajectory (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : AnchoredTimedState p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    trajectory (anchoredTimedAdvance p c answer) n s ξ =
      (anchoredPath p c answer s.1 ξ n, s.2 + n) := by
  induction n generalizing s ξ with
  | zero => simp [trajectory, anchoredPath]
  | succ n ih =>
    rw [trajectory, ih]
    simp only [anchoredTimedAdvance, anchoredPath, trajectory]
    congr 1
    omega

lemma anchored_timed_trace_projection (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : AnchoredTimedState p c) (ξ : ℕ → ℝ × Ω) (k : ℕ) :
    let t := blockTrace (anchoredTimedCost p c) (finiteRun (anchoredTimedAdvance p c answer)) s ξ k
    (forgetAnchor p c t.1, t.2) =
      blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer)) (forgetAnchor p c s) ξ k :=
  blockTrace_map _ _ _ (forgetAnchor_advance p c answer) _ _ _ _

lemma anchored_timed_trace_horizon (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) :
    (blockTrace (anchoredTimedCost p c) (finiteRun (anchoredTimedAdvance p c answer))
      (⟨initial p c, p.x0⟩, 0) ξ (blockCap c)).1.2 = trialCalls c := by
  have he := anchored_timed_trace_projection p c answer (⟨initial p c, p.x0⟩, 0) ξ (blockCap c)
  have ht := congrArg (fun t => t.1.2) he
  exact ht.trans (timed_trace_horizon p c answer ξ)

lemma anchored_timed_trace_output (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) :
    (blockTrace (anchoredTimedCost p c) (finiteRun (anchoredTimedAdvance p c answer))
      (⟨initial p c, p.x0⟩, 0) ξ (blockCap c)).1.1 =
      anchoredPath p c answer ⟨initial p c, p.x0⟩ ξ (trialCalls c) := by
  have ht := anchored_timed_trace_horizon p c answer ξ
  rw [blockTrace_eq_trajectory, anchored_timed_trajectory] at ht ⊢
  simpa only [Nat.zero_add] using congrArg (anchoredPath p c answer ⟨initial p c, p.x0⟩ ξ) ht

lemma path_move_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) (hs : MoveValid p c s) :
    MoveValid p c (path p c answer s ξ n) := by
  induction n generalizing s ξ with
  | zero => exact hs
  | succ n ih => exact ih _ _ (update_move_valid p c s hs _ _)

def BlockValid (p : Params) (c : Config) (g : Space p → Space p) (M : ℝ)
    (s : AnchoredTimedState p c) : Prop :=
  TimedValid p c (forgetAnchor p c s) ∧ AnchoredValid p c s.1 ∧
    MoveValid p c s.1.value ∧ ProposalValid p c g M s.1

lemma initial_block_valid (p : Params) (c : Config) (g : Space p → Space p) (M : ℝ) :
    BlockValid p c g M (⟨initial p c, p.x0⟩, 0) := by
  refine ⟨initial_timed_valid p c, initial_anchored_valid p c, ?_, ?_⟩
  · trivial
  · exact fun _ => self_proposal_bound p g M p.x0

lemma anchored_timed_next_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (s : AnchoredTimedState p c) (ξ : ℕ → ℝ × Ω) (hs : BlockValid p c g M s) :
    BlockValid p c g M
      (finiteRun (anchoredTimedAdvance p c answer) (anchoredTimedCost p c s) s (fun i => ξ i)) := by
  have hv := timed_next_valid p c answer (forgetAnchor p c s) ξ hs.1
  rw [finiteRun_eq_trajectory, timed_trajectory] at hv
  rw [finiteRun_eq_trajectory, anchored_timed_trajectory]
  refine ⟨?_, anchoredPath_valid p c answer s.1 hs.2.1 ξ _, ?_,
    anchoredPath_proposal_valid p c answer g M hcoarse hfine s.1 hs.2.1 hs.2.2.1 hs.2.2.2 ξ _⟩
  · simpa only [forgetAnchor, anchoredPath_projection, anchoredTimedCost] using hv
  · rw [anchoredPath_projection]
    exact path_move_valid p c answer s.1.value ξ _ hs.2.2.1

abbrev BlockState (p : Params) (c : Config) (g : Space p → Space p) (M : ℝ) :=
  { s : AnchoredTimedState p c // BlockValid p c g M s }

lemma anchored_finite_next_valid (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (s : AnchoredTimedState p c) (ξ : Fin (anchoredTimedCost p c s) → ℝ × Ω)
    (hs : BlockValid p c g M s) :
    BlockValid p c g M (finiteRun (anchoredTimedAdvance p c answer) (anchoredTimedCost p c s) s ξ) := by
  classical
  let stream : ℕ → ℝ × Ω := fun k =>
    if h : k < anchoredTimedCost p c s then ξ ⟨k, h⟩ else Classical.choice inferInstance
  have hp : (fun i : Fin (anchoredTimedCost p c s) => stream i) = ξ := by
    funext i
    simp [stream, i.isLt]
  have hh := anchored_timed_next_valid p c answer g M hcoarse hfine s stream hs
  rwa [hp] at hh

noncomputable def blockNext (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (n : ℕ) (s : BlockState p c g M) (ξ : Fin n → ℝ × Ω) : BlockState p c g M :=
  if hn : n = anchoredTimedCost p c s.val then
    ⟨finiteRun (anchoredTimedAdvance p c answer) n s.val ξ, by
      subst n
      exact anchored_finite_next_valid p c answer g M hcoarse hfine s.val ξ s.property⟩
  else s

lemma blockNext_at_cost (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (s : BlockState p c g M) (ξ : Fin (anchoredTimedCost p c s.val) → ℝ × Ω) :
    (blockNext p c answer g M hcoarse hfine (anchoredTimedCost p c s.val) s ξ).val =
      finiteRun (anchoredTimedAdvance p c answer) (anchoredTimedCost p c s.val) s.val ξ := by
  simp [blockNext]

lemma valid_block_trace_projection (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (s : BlockState p c g M) (ξ : ℕ → ℝ × Ω) (k : ℕ) :
    let t := blockTrace (fun s : BlockState p c g M => anchoredTimedCost p c s.val)
      (blockNext p c answer g M hcoarse hfine) s ξ k
    (t.1.val, t.2) =
      blockTrace (anchoredTimedCost p c) (finiteRun (anchoredTimedAdvance p c answer)) s.val ξ k := by
  dsimp only
  induction k generalizing s ξ with
  | zero => rfl
  | succ k ih =>
    rw [blockTrace_start_succ, blockTrace_start_succ, ih, blockNext_at_cost]

end LongTails.Proofs.HystereticHessianAnchorBlocks
