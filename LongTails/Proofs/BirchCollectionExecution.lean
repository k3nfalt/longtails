import LongTails.Algorithms.BirchCollections
import LongTails.Proofs.BirchNonEuclideanExecution

namespace LongTails.Proofs.BirchCollectionExecution

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Setups.BirchNonEuclidean (Instruction Program)
open LongTails.Proofs.BirchNonEuclideanExecution (queryCount)

lemma eventCode_calls (τ : ℝ) (s : TraceState) (r : Registers) (e : Event) :
    queryCount (eventCode τ s r e) = e.calls := by
  cases e <;> simp [eventCode, queryCount, Instruction.oracleCost, Event.calls]

lemma step_raw (s : TraceState) (e : Event) :
    (step s e).nextRaw = s.nextRaw + e.calls := by
  cases e <;> simp [step, Event.calls]

lemma step_state_mono (s : TraceState) (e : Event) : s.nextState ≤ (step s e).nextState := by
  cases e <;> simp [step]

lemma step_collection_mono (s : TraceState) (e : Event) :
    s.nextCollection ≤ (step s e).nextCollection := by
  cases e <;> simp [step]

lemma step_direction_mono (s : TraceState) (e : Event) :
    s.nextDirection ≤ (step s e).nextDirection := by
  cases e <;> simp [step]

lemma step_old_state (s : TraceState) (e : Event) (j : ℕ) (hj : j < s.nextState) :
    (step s e).states j = s.states j := by
  have hn : j ≠ s.nextState := ne_of_lt hj
  cases e <;> simp [step, hn]

lemma step_old_raw (s : TraceState) (e : Event) (j : ℕ) (hj : j < s.nextRaw) :
    (step s e).raws j = s.raws j := by
  have hn : j ≠ s.nextRaw := ne_of_lt hj
  cases e <;> simp [step, hn]

lemma step_old_direction (s : TraceState) (e : Event) (j : ℕ) (hj : j < s.nextDirection) :
    (step s e).directions j = s.directions j := by
  have hn : j ≠ s.nextDirection := ne_of_lt hj
  cases e <;> simp [step, hn]

lemma fold_trace (τ : ℝ) (events : List Event) (c : Compilation) :
    (events.foldl (compileStep τ) c).trace = events.foldl step c.trace := by
  induction events generalizing c with
  | nil => rfl
  | cons e rest ih => simpa only [List.foldl_cons, compileStep] using ih (compileStep τ c e)

lemma compile_trace (τ : ℝ) (events : List Event) :
    (compile τ events).trace = run events := fold_trace τ events {}

lemma fold_raw (events : List Event) (s : TraceState) :
    (events.foldl step s).nextRaw = s.nextRaw + calls events := by
  induction events generalizing s with
  | nil => simp [calls]
  | cons e rest ih =>
      simp only [List.foldl_cons, ih, step_raw, calls, List.map_cons, List.sum_cons]
      omega

lemma run_raw (events : List Event) : (run events).nextRaw = calls events := by
  simpa only [run, TraceState.nextRaw, zero_add] using fold_raw events {}

lemma fold_code_calls (τ : ℝ) (events : List Event) (c : Compilation) :
    queryCount (events.foldl (compileStep τ) c).code = queryCount c.code + calls events := by
  induction events generalizing c with
  | nil => simp [calls]
  | cons e rest ih =>
      rw [List.foldl_cons, ih]
      simp only [compileStep, queryCount, List.map_append, List.sum_append]
      change queryCount c.code + queryCount (eventCode τ c.trace c.registers e) + calls rest = _
      rw [eventCode_calls]
      simp [calls, queryCount, Nat.add_assoc]

lemma compile_calls (τ : ℝ) (events : List Event) :
    queryCount (compile τ events).code = calls events := by
  simpa [compile, queryCount] using fold_code_calls τ events {}

lemma program_calls (p : Params) : (program p).oracleCalls = calls p.events := by
  exact compile_calls (1 / (20 * p.L)) p.events

lemma registerStep_next (τ : ℝ) (s : TraceState) (r : Registers) (e : Event) :
    (registerStep τ s r e).next = r.next + (eventCode τ s r e).length := by
  cases e <;> rfl

lemma fold_registers_next (τ : ℝ) (events : List Event) (c : Compilation)
    (hc : c.registers.next = c.code.length + 1) :
    (events.foldl (compileStep τ) c).registers.next =
      (events.foldl (compileStep τ) c).code.length + 1 := by
  induction events generalizing c with
  | nil => exact hc
  | cons e rest ih =>
      apply ih (compileStep τ c e)
      simp only [compileStep, registerStep_next, List.length_append, hc]
      omega

lemma compile_registers_next (τ : ℝ) (events : List Event) :
    (compile τ events).registers.next = (compile τ events).code.length + 1 :=
  fold_registers_next τ events {} rfl

end LongTails.Proofs.BirchCollectionExecution
