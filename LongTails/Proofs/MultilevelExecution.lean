import LongTails.Proofs.MultilevelWorker
import LongTails.Proofs.MultilevelInformation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultilevelExecution

open DistributedTemplate MeasureTheory LongTails.Setups
open DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState MultilevelTimetable MultilevelWireState MultilevelWireTransitions
open MultilevelDeadline MultilevelBookkeeping MultilevelActions MultilevelCoordinator MultilevelWorker

variable {p : Params}

noncomputable def awake (u : Context p) (c : u.Exec) : Finset (Fin (p.n+1)) :=
  Finset.univ.filter fun i => c.wakeTime i ≤ u.T

noncomputable def charge (u : Context p) (b : Book p) (c : u.Exec) :=
  workLeft u.t b * (p.n + 2 : ℕ) + (awake u c).card

noncomputable def jump (u : Context p) (c : u.Exec) : ℕ :=
  if event u.O u.A c c.time = none ∧ c.time < c.deadline then 1 else 0

noncomputable def rank (u : Context p) (b : Book p) (c : u.Exec) := 2*charge u b c + jump u c

lemma charge_less (u : Context p) (b z : Book p) (c d : u.Exec) (h : Progress u b c z d)
    (hc : c.time ≤ u.T) : charge u z d < charge u b c := by
  cases h with
  | job h =>
    have ha : (awake u d).card ≤ (p.n:ℕ)+1 := by
      simpa using (Finset.card_le_univ (awake u d))
    have hm := Nat.mul_le_mul_right (p.n+2 : ℕ) h
    unfold charge
    rw [Nat.succ_mul] at hm
    omega
  | idle v he hready htime =>
    subst z
    have hnew : awake u d = (awake u c).erase v := by
      ext i
      by_cases hi : i = v
      · subst i
        have h : ¬max c.time (u.T+1) ≤ u.T := by simp
        simp [awake,htime,h]
      · simp [awake,hi,htime]
    have hv : v ∈ awake u c := by simpa [awake] using hready.trans hc
    simp only [charge,hnew,Nat.add_lt_add_iff_left]
    exact Finset.card_lt_card (Finset.erase_ssubset hv)

lemma advance_rank (u : Context p) (b : Book p) (c : u.Exec) (hc : c.time < c.deadline)
    (he : event u.O u.A c c.time = none) :
    let d := {c with time := nextTime (event u.O u.A c) c.time c.deadline}
    rank u b d < rank u b c := by
  intro d
  have hex := DistributedExecution.star_nextTime_exists (Network p) (evalPair u.g) u.P u.A c hc.le
  have ht := (DistributedExecution.nextTime_spec _ _ _ hex).1.2.2
  have heq : event u.O u.A d = event u.O u.A c := rfl
  have hflag : jump u d = 0 := by
    unfold jump
    apply ite_eq_right
    intro h
    rcases ht with hl | hr
    · exact h.2.ne hl
    · exact (Option.isSome_iff_ne_none.mp hr) (heq ▸ h.1)
  have hflag' : jump u c = 1 := by simp [jump, he,hc]
  have hsame : charge u b d = charge u b c := rfl
  simp [rank,hflag,hflag',hsame]

lemma progress (u : Context p) (b : Book p) (c d : u.Exec) (hg : Good u b c)
    (sc : Timetable p u.t u.T) (hh : ∀ i, 0 < p.h i) (ht : c.time ≤ c.deadline)
    (hT : c.deadline ≤ u.T) (hs : step u.O u.A c = some d) :
    ∃ z, Good u z d ∧ rank u z d < rank u b c := by
  cases he : event u.O u.A c c.time with
  | none =>
    have hn : c.time ≠ c.deadline := by
      intro hl
      have hstop := (DistributedExecution.step_terminal_iff _ _ c ht).mpr ⟨hl,he⟩
      rw [hstop] at hs
      contradiction
    have hd : d = {c with time := nextTime (event u.O u.A c) c.time c.deadline} := by
      simpa [step,not_lt_of_ge ht,he,hn,eq_comm] using hs
    subst d
    exact ⟨b,jump_good u b c hg sc hh ht he,advance_rank u b c (lt_of_le_of_ne ht hn) he⟩
  | some data =>
    rcases data with ⟨⟨v,ev⟩,o⟩
    obtain ⟨z,hz,hprog⟩ := event_move u b c d hg sc v ev o he hs
    refine ⟨z,hz,?_⟩
    have hcharge := charge_less u b z c d hprog (ht.trans hT)
    have hflag : jump u d ≤ 1 := by unfold jump; split <;> decide
    unfold rank
    omega

lemma eventually_terminal (u : Context p) (sc : Timetable p u.t u.T) (hh : ∀ i, 0 < p.h i)
    (b : Book p) (c : u.Exec) (hg : Good u b c) (ht : c.time ≤ c.deadline) (hT : c.deadline ≤ u.T) :
    ∃ k z, let d := run u.O u.A k c
      Good u z d ∧ step u.O u.A d = none := by
  cases hs : step u.O u.A c with
  | none => exact ⟨0,b,hg,hs⟩
  | some d =>
    obtain ⟨z,hz,hrank⟩ := progress u b c d hg sc hh ht hT hs
    have hdead := DistributedExecution.step_deadline _ _ c d hs
    obtain ⟨k,z',h⟩ := eventually_terminal u sc hh z d hz
      (DistributedExecution.step_time_le_deadline _ _ c d ht hs) (hdead ▸ hT)
    exact ⟨k+1,z',by simpa only [run,hs] using h⟩
termination_by rank u b c

lemma finite (u : Context p) (sc : Timetable p u.t u.T) (hh : ∀ i, 0 < p.h i) :
    FiniteEvents u.O u.A u.T (u.seed,u.xs) := by
  intro D hD
  obtain ⟨k,b,_,hk⟩ := eventually_terminal u sc hh {} _ (initial_good u D) zero_le hD
  exact ⟨k,hk⟩

lemma execute_script (u : Context p) (sc : Timetable p u.t u.T) (hh : ∀ i, 0 < p.h i) :
    execute u.O u.A u.T u.seed u.xs =
      u.t.output u.seed (fun j => if j < u.t.count then u.out j else []) := by
  let c := initial u.O u.A u.T (u.seed,u.xs)
  obtain ⟨k,b,hg,hk⟩ := eventually_terminal u sc hh {} c (initial_good u _) zero_le le_rfl
  let d := run u.O u.A k c
  have hc : d.time ≤ d.deadline := DistributedExecution.run_time_le_deadline _ _ c k zero_le
  have hd : d.deadline = u.T := DistributedExecution.run_deadline _ _ c k
  obtain ⟨ht,hquiet⟩ := (DistributedExecution.step_terminal_iff _ _ d hc).mp hk
  have hdone (j : ℕ) : j ∈ b.done ↔ j < u.t.count :=
    ⟨fun hj => (hg.valid.2.1 _ hj).trans_le hg.valid.1, fun hj => terminal_done u b d hg sc hd ht hquiet j hj hh⟩
  rw [DistributedExecution.execute_eq_terminal u.O u.A u.T (u.seed,u.xs) k hk]
  change u.A.output (d.workers 0) = _
  rw [hg.workers]
  apply congrArg (u.t.output u.seed)
  funext j
  by_cases hj : j < u.t.count <;> simp [nodes,root,hdone,hj]

end LongTails.Proofs.MultilevelExecution
