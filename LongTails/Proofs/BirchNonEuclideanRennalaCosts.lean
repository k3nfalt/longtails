import LongTails.Proofs.BirchNonEuclideanRennalaScheduling
import LongTails.Proofs.BirchNonEuclideanEvents

namespace LongTails.Proofs.BirchNonEuclideanRennalaCosts

open LongTails.Setups.BirchNonEuclidean hiding State
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanRennalaScheduling
open LongTails.Proofs.BirchNonEuclideanEvents (state_map_apply state_forIn_weighted_cost)

def eventQueries {m : ℕ} : Event m → ℕ
  | .query _ => 1
  | .reply _ => 0

lemma step_query_length {m : ℕ} (K B : ℕ) (s : State m) (e : Event m) :
    (step K B s e).queries.length = s.queries.length + eventQueries e := by
  cases e with
  | query w => simp [step, eventQueries]
  | reply w => by_cases ha : s.round < K <;> simp [step, ha, eventQueries]

lemma fold_query_length {m : ℕ} (K B : ℕ) (events : List (Event m)) (s : State m) :
    (events.foldl (step K B) s).queries.length = s.queries.length + (events.map eventQueries).sum := by
  induction events generalizing s with
  | nil => simp
  | cons e events ih =>
      rw [List.foldl_cons, ih, step_query_length]
      simp [Nat.add_assoc]

lemma run_query_length {m : ℕ} (K B : ℕ) (events : List (Event m)) :
    (run K B events).queries.length = (events.map eventQueries).sum := by
  simpa only [run, List.length_nil, Nat.zero_add] using fold_query_length K B events {}

lemma eventCode_public {m : ℕ} (K B : ℕ) (e : Event m) (state : State m × Registers m)
    (s : CodeState) : (eventCode K B e state s).1.1 = step K B state.1 e := by
  cases e <;> simp only [eventCode, replyCode, commitCode, relaunchCode, state_bind_apply, state_pure_apply]

lemma replyCode_calls {m : ℕ} (K B : ℕ) (w : Fin m) (state : State m) (regs : Registers m)
    (s : CodeState) : codeCalls (replyCode K B w state regs s).2 = codeCalls s := by
  simp only [replyCode, commitCode, relaunchCode, state_bind_apply]
  split_ifs <;>
    simp [state_bind_apply, state_pure_apply, state_map_apply, emit_apply, codeCalls,
      InstructionTemplate.instantiate, Instruction.oracleCost]

lemma eventCode_calls {m : ℕ} (K B : ℕ) (e : Event m) (state : State m × Registers m)
    (s : CodeState) : codeCalls (eventCode K B e state s).2 = codeCalls s + eventQueries e := by
  cases e with
  | query w =>
      simp [eventCode, state_map_apply, emit_apply, codeCalls,
        InstructionTemplate.instantiate, Instruction.oracleCost, eventQueries]
  | reply w => simpa only [eventCode, state_bind_apply, state_pure_apply, eventQueries, Nat.add_zero]
      using replyCode_calls K B w state.1 state.2 s

lemma launchCode_calls (w : ℕ) (s : CodeState) : codeCalls (launchCode w s).2 = codeCalls s := by
  simp [launchCode, state_bind_apply, state_pure_apply, emit_apply, codeCalls,
    InstructionTemplate.instantiate, Instruction.oracleCost]

lemma initialCode_run (m : ℕ) (s : CodeState) :
    initialCode m s =
      let sent := (forIn (List.finRange m) ()
        (fun w _ => ForInStep.yield <$> launchCode (w.val + 1)) : StateM CodeState Unit) s
      (({} : Registers m), sent.2) := rfl

lemma initialCode_calls (m : ℕ) (s : CodeState) : codeCalls (initialCode m s).2 = codeCalls s := by
  rw [initialCode_run]
  dsimp only
  rw [state_forIn_cost codeCalls _ 0 (fun w _ s => by simpa using launchCode_calls (w.val + 1) s)]
  simp

lemma eventsStateCode_run {m : ℕ} (K B : ℕ) (events : List (Event m)) (s : CodeState) :
    eventsStateCode K B events s =
      let initial := initialCode m s
      (forIn events (({} : State m), initial.1)
        (fun e state => ForInStep.yield <$> eventCode K B e state) :
          StateM CodeState (State m × Registers m)) initial.2 := rfl

lemma eventsCode_calls {m : ℕ} (K B : ℕ) (events : List (Event m)) (s : CodeState) :
    codeCalls ((eventsCode K B events).run s).2 = codeCalls s + (events.map eventQueries).sum := by
  change codeCalls (eventsStateCode K B events s).2 = _
  rw [eventsStateCode_run]
  dsimp only
  rw [state_forIn_weighted_cost codeCalls _ eventQueries (eventCode_calls K B), initialCode_calls]

lemma eventsProgram_calls {m : ℕ} (K B : ℕ) (events : List (Event m)) (t : Tuning) :
    (eventsProgram K B events t).oracleCalls = (run K B events).queries.length := by
  rw [eventsProgram, template_tuning_oracleCalls _ t (canonicalTuning 0 1), run_query_length]
  change codeCalls ((eventsCode K B events).run {}).2 = _
  rw [eventsCode_calls]
  simp [codeCalls]

lemma completeTrace_calls {m : ℕ} (K B : ℕ) (events : List (Event m)) (t : Tuning)
    (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    (eventsProgram K B events t).oracleCalls = K * B + (run K B events).stale.length + (m - 1) := by
  rw [eventsProgram_calls, completeTrace_query_count K B events hK hB he]

lemma completeTrace_calls_bound {m : ℕ} (K B : ℕ) (events : List (Event m)) (t : Tuning)
    (hm : 0 < m) (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    (eventsProgram K B events t).oracleCalls ≤ K * (B + m - 1) := by
  rw [eventsProgram_calls]
  exact completeTrace_query_bound K B events hm hK hB he

end LongTails.Proofs.BirchNonEuclideanRennalaCosts
