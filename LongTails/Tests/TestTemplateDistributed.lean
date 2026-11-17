import LongTails.TemplateDistributed
import Mathlib.Tactic

open MeasureTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace DistributedTemplate.DistributedTests

lemma nextTime_eq {Event : Type} (event : Time → Option Event) (time limit finish : Time)
    (h : IsLeast {t | time ≤ t ∧ t ≤ limit ∧
      (t = limit ∨ (event t).isSome)} finish) :
    nextTime event time limit = finish := by
  classical
  unfold nextTime
  rw [dite_eq_left ⟨finish, h⟩]
  exact le_antisymm ((Classical.choose_spec ⟨finish, h⟩).2 h.1)
    (h.2 (Classical.choose_spec ⟨finish, h⟩).1)

def worker : Algorithm Unit Unit Unit (List ClockReading) where
  clock t := if t < 1 then 7 else 9
  timer t := t.val
  State := List ClockReading
  root := 0
  initial _ _ := []
  query _ s _ := (.advance 2, s)
  update _ s reading _ := reading :: s
  output := id

def oracle (finish : Time) : Oracle Unit Unit Unit where
  computation := {
    State := Bool
    initial _ _ := true
    submit _ s _ _ := s
    answer _ s time :=
      if s then
        if finish ≤ time then some ((), false) else none
      else none }
  communication := {
    State := Unit
    initial _ := ()
    submit s _ _ _ := s
    answer _ _ := none }

lemma event_nextTime (finish : Time) (c : ExecutionState (oracle finish) worker)
    (hs : c.oracle.computation 0 = true) (hw : finish ≤ c.wakeTime 0)
    (ht : c.time ≤ finish) (hl : finish ≤ c.deadline) :
    nextTime (event (oracle finish) worker c) c.time c.deadline = finish := by
  apply nextTime_eq
  constructor
  · exact ⟨ht, hl, Or.inr (by simp [event, Oracle.answer, oracle, List.finRange, hs])⟩
  · intro t ht
    rcases ht with ⟨_, _, hlimit | hready⟩
    · simpa [hlimit] using hl
    · by_contra h
      have hwake : ¬ c.wakeTime 0 ≤ t := fun ht => h (le_trans hw ht)
      simp [event, Oracle.answer, oracle, List.finRange, List.rotate, h, hwake] at hready

lemma immediate_reply_uses_clock :
    (run (oracle 0) worker 1 (initial (oracle 0) worker 2 ((), ()))).workers 0 = [7] := by
  dsimp [run, step, event, initial, Oracle.initial, Oracle.answer, oracle, worker]
  norm_num [clockBits, List.finRange, Function.update]

lemma wake_update_uses_clock :
    (run (oracle (1 / 2)) worker 1
      (initial (oracle (1 / 2)) worker 2 ((), ()))).workers 0 = [7] := by
  dsimp [run, step, event, initial, Oracle.initial, Oracle.answer, oracle, worker]
  norm_num [clockBits, List.finRange, List.rotate, Function.update, div_le_iff₀]

lemma delayed_reply_keeps_exact_time :
    let c := run (oracle (1 / 2)) worker 3
      (initial (oracle (1 / 2)) worker 2 ((), ()))
    c.time = 1 / 2 ∧ c.workers 0 = [7, 7] := by
  have ht := event_nextTime (1 / 2)
    { initial (oracle (1 / 2)) worker 2 ((), ()) with
      workers := Function.update (fun _ => []) 0 [7]
      wakeTime := Function.update (fun _ => 0) 0 2
      turn := 1 } (by rfl) (by norm_num [Function.update, div_le_iff₀]) (by norm_num [initial]) (by norm_num [initial, div_le_iff₀])
  dsimp only [initial, Oracle.initial, oracle, worker] at ht
  dsimp only [oracle, worker] at *
  norm_num [clockBits, ht, run, step, initial, event_nextTime, event, Oracle.initial, Oracle.answer,
    oracle, worker, List.finRange, List.rotate, Function.update, div_le_iff₀]

lemma delayed_reply_uses_arrival_clock :
    let c := run (oracle (3 / 2)) worker 3
      (initial (oracle (3 / 2)) worker 2 ((), ()))
    c.time = 3 / 2 ∧ c.workers 0 = [9, 7] := by
  have ht := event_nextTime (3 / 2)
    { initial (oracle (3 / 2)) worker 2 ((), ()) with
      workers := Function.update (fun _ => []) 0 [7]
      wakeTime := Function.update (fun _ => 0) 0 2
      turn := 1 } (by rfl) (by norm_num [Function.update, div_le_iff₀]) (by norm_num [initial]) (by norm_num [initial, div_le_iff₀])
  dsimp only [initial, Oracle.initial, oracle, worker] at ht
  dsimp only [oracle, worker] at *
  norm_num [clockBits, ht, run, step, initial, event_nextTime, event, Oracle.initial, Oracle.answer,
    oracle, worker, List.finRange, List.rotate, Function.update, div_le_iff₀]

lemma wake_event_is_explicit :
    event (oracle 1) worker (initial (oracle 1) worker 2 ((), ())) 0 =
      some ((0, .wake), (oracle 1).initial ()) := by
  dsimp only [oracle, worker] at *
  norm_num [clockBits, event, initial, Oracle.initial, Oracle.answer, oracle, worker,
    List.finRange, List.rotate]

lemma reply_precedes_simultaneous_wake :
    match event (oracle 0) worker (initial (oracle 0) worker 2 ((), ())) 0 with
    | some ((v, .computed ()), s) => v = 0 ∧ s.computation 0 = false
    | _ => False := by
  dsimp only [oracle, worker] at *
  norm_num [clockBits, event, initial, Oracle.initial, Oracle.answer, oracle, worker,
    List.finRange, Function.update]

lemma wake_before_reply :
    let c := { initial (oracle 3) worker 4 ((), ()) with wakeTime := fun _ => 1 }
    nextTime (event (oracle 3) worker c) c.time c.deadline = 1 := by
  apply nextTime_eq
  constructor
  · refine ⟨by norm_num [clockBits, initial], by norm_num [clockBits, initial], Or.inr ?_⟩
    dsimp only [oracle, worker] at *
    norm_num [clockBits, event, initial, Oracle.initial, Oracle.answer, oracle, worker,
      List.finRange, List.rotate]
  · intro t ht
    rcases ht with ⟨_, _, hlimit | hready⟩
    · norm_num [clockBits, initial] at hlimit
      rw [hlimit]
      norm_num
    · by_contra h
      have hfinish : ¬ (3 : Time) ≤ t := fun ht => h (le_trans (by norm_num) ht)
      simp [event, initial, Oracle.initial, Oracle.answer, oracle, worker,
        List.finRange, List.rotate, h, hfinish] at hready

lemma no_reply_before_deadline :
    nextTime ((oracle 3).answer ((oracle 3).initial ())) 0 2 = 2 := by
  apply nextTime_eq
  constructor
  · exact ⟨by norm_num, le_rfl, Or.inl rfl⟩
  · intro t ht
    rcases ht with ⟨_, hbound, hlimit | hready⟩
    · exact le_of_eq hlimit.symm
    · have h : ¬ (3 : Time) ≤ t := by exact not_le_of_gt (lt_of_le_of_lt hbound (by norm_num))
      simp [Oracle.answer, Oracle.initial, oracle, List.finRange, h] at hready

def racingOracle (computeFinish commFinish : Time) : Oracle Unit Unit Unit 2 where
  computation := {
    State := Bool
    initial _ _ := true
    submit _ s _ _ := s
    answer _ s time :=
      if s then
        if computeFinish ≤ time then some ((), false) else none
      else none }
  communication := {
    State := Bool
    initial _ := true
    submit s _ _ _ := s
    answer s time :=
      if s then
        if commFinish ≤ time then some ((1, ()), false) else none
      else none }

def reactingWorker : Algorithm Unit Unit Unit (List ℕ) 2 where
  clock _ := 0
  timer t := t.val
  State := List ℕ
  root := 0
  initial _ _ := []
  update _ s _ notification :=
    match notification with
    | .wake => 0 :: s
    | .computed () => 1 :: s
    | .received () => 2 :: s
  query _ s _ := (.advance 2, 9 :: s)
  output := id

lemma every_event_updates_then_acts :
    (run (racingOracle 1 2) reactingWorker 1
      (initial (racingOracle 1 2) reactingWorker 3 ((), ()))).workers 0 = [9, 0] ∧
    (run (racingOracle 0 2) reactingWorker 1
      (initial (racingOracle 0 2) reactingWorker 3 ((), ()))).workers 0 = [9, 1] ∧
    (run (racingOracle 2 0) reactingWorker 1
      (initial (racingOracle 2 0) reactingWorker 3 ((), ()))).workers 1 = [9, 2] := by
  dsimp only [racingOracle, reactingWorker] at *
  norm_num [clockBits, run, step, event, initial, Oracle.initial, Oracle.answer, racingOracle,
    reactingWorker, List.finRange, List.rotate, Function.update]

lemma reply_replaces_old_wake :
    let c := { initial (racingOracle 0 2) reactingWorker 12 ((), ()) with
      wakeTime := fun _ => 10 }
    (run (racingOracle 0 2) reactingWorker 1 c).wakeTime 0 = 2 := by
  dsimp only [racingOracle, reactingWorker] at *
  norm_num [clockBits, run, step, event, initial, Oracle.initial, Oracle.answer, racingOracle,
    reactingWorker, List.finRange, Function.update]

lemma pending_answers_expose_no_result :
    (racingOracle 2 1).answer ((racingOracle 2 1).initial ()) 0 = none := by
  dsimp [Oracle.answer, Oracle.initial, racingOracle]
  norm_num [clockBits, List.finRange]

lemma computation_finishes_locally :
    match (racingOracle 1 2).answer ((racingOracle 1 2).initial ()) 1 with
    | some ((v, .computed ()), s) => v = 0 ∧ s.computation 0 = false ∧
        s.computation 1 = true ∧ s.communication = true
    | _ => False := by
  dsimp [Oracle.answer, Oracle.initial, racingOracle]
  norm_num [clockBits, List.finRange, Function.update]

lemma communication_can_finish_first :
    match (racingOracle 2 1).answer ((racingOracle 2 1).initial ()) 1 with
    | some ((v, .received ()), s) => v = 1 ∧ s.computation 0 = true ∧
        s.computation 1 = true ∧ s.communication = false
    | _ => False := by
  dsimp [Oracle.answer, Oracle.initial, racingOracle]
  norm_num [clockBits, List.finRange, Function.update]

lemma communication_wakes_before_computation :
    nextTime ((racingOracle 2 1).answer ((racingOracle 2 1).initial ())) 0 3 = 1 := by
  apply nextTime_eq
  constructor
  · refine ⟨by norm_num, by norm_num, Or.inr ?_⟩
    dsimp only [racingOracle, reactingWorker] at *
    norm_num [clockBits, Oracle.answer, Oracle.initial, racingOracle, List.finRange]
  · intro t ht
    rcases ht with ⟨_, _, hlimit | hready⟩
    · rw [hlimit]
      norm_num
    · by_contra h
      have hcompute : ¬ (2 : Time) ≤ t := by
        intro ht
        exact h (le_trans (by norm_num) ht)
      simp [Oracle.answer, Oracle.initial, racingOracle, List.finRange, h, hcompute] at hready

lemma simultaneous_events_keep_worker_order :
    match (racingOracle 1 1).answer ((racingOracle 1 1).initial ()) 1 with
    | some ((v, _), s) => v = 0 ∧ s.computation 0 = false ∧
        s.computation 1 = true ∧ s.communication = true
    | _ => False := by
  dsimp [Oracle.answer, Oracle.initial, racingOracle]
  norm_num [clockBits, List.finRange, Function.update]

lemma no_pending_operations_is_idle :
    (racingOracle 1 2).answer ⟨fun _ => false, false⟩ 0 = none := by
  dsimp [Oracle.answer, racingOracle]
  norm_num [clockBits, List.finRange]

private def optionalReplyOracle : Oracle Unit (Option ℕ) Bool 2 where
  computation := {
    State := Option (Option ℕ)
    initial v _ := if v = 0 then some none else some (some 7)
    submit _ s _ _ := s
    answer _ s _ := s.map fun reply => (reply, none) }
  communication := {
    State := Option (Fin 2 × Bool)
    initial _ := some (1, true)
    submit s _ _ _ := s
    answer s _ := s.map fun reply => (reply, none) }

lemma optional_none_is_a_computation_reply :
    match optionalReplyOracle.answer (optionalReplyOracle.initial ()) 0 with
    | some ((v, .computed none), s) =>
        v = 0 ∧ s.computation 0 = none ∧ s.computation 1 = some (some 7) ∧
          s.communication = some (1, true)
    | _ => False := by
  dsimp [Oracle.answer, Oracle.initial, optionalReplyOracle]
  norm_num [List.finRange, Function.update]

lemma answers_drain_computations_then_communication :
    (do
      let (first, s₁) ← optionalReplyOracle.answer (optionalReplyOracle.initial ()) 0
      let (second, s₂) ← optionalReplyOracle.answer s₁ 0
      let (third, s₃) ← optionalReplyOracle.answer s₂ 0
      pure (first, second, third, optionalReplyOracle.answer s₃ 0)) =
    some ((0, .computed none), (1, .computed (some 7)), (1, .received true), none) := by
  dsimp [Oracle.answer, Oracle.initial, optionalReplyOracle]
  norm_num [List.finRange, Function.update]

end DistributedTemplate.DistributedTests
