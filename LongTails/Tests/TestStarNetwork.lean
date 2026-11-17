import LongTails.Setups.StarNetwork
import Mathlib.Tactic

namespace LongTails.Tests.StarNetwork

open DistributedTemplate LongTails.Setups.StarNetwork

private def network : Network 2 := ⟨fun _ => 1, 2, 3⟩

private noncomputable def comm := communication (Seed := Unit) network

private noncomputable def sent := comm.submit (comm.initial ()) 1 0 (1, [true, false])

example : sent.messages 0 1 = some (9, [true, false]) ∧ sent.messages 0 2 = none := by
  simp [sent, comm, communication, network]
  norm_num

example (s : CommunicationState 2) : comm.submit s 1 1 (2, [true]) = s := by
  simp [comm, communication]

example (s : CommunicationState 2) : comm.submit s 1 0 (0, [true]) = s := by
  simp [comm, communication]

example : comm.submit sent 2 0 (1, [false]) = sent := by
  simp [sent, comm, communication, network]

example : (comm.submit (comm.initial ()) 1 2 (0, [true])).messages 2 0 = some (6, [true]) := by
  simp [comm, communication, network]
  norm_num

example : comm.answer sent 8 = none := by
  simp [comm, communication, sent, network, List.finRange, List.ofFn_succ, List.argmin, List.argAux]
  norm_num

example : (comm.answer sent 9).map (fun result => (result.1, result.2.messages 0 1)) =
    some ((1, .received 0 [true, false]), none) := by
  simp [comm, communication, sent, network, List.finRange, List.ofFn_succ, List.argmin, List.argAux]
  norm_num

private noncomputable def comp := computation (Seed := Unit) network
  (fun _ (input : ℕ) _ used => input + used)

private noncomputable def started := comp.submit 1 (comp.initial 1 ()) 1 (.evaluate 7)

example : comp.submit 1 started 1 (.evaluate 99) = started := by
  dsimp [started, comp, computation]
  simp [Fin.cases, Fin.induction, Fin.induction.go]

example : comp.answer 1 started 1 = none := by
  dsimp [started, comp, computation, network]
  norm_num [Fin.cases, Fin.induction, Fin.induction.go]

example : comp.answer 1 started 2 =
    some (.computed 7 7, { started with pending := none, used := 1 }) := by
  dsimp [started, comp, computation, network]
  norm_num [Fin.cases, Fin.induction, Fin.induction.go]

example : comp.answer 1 (comp.submit 1 started 1 .abort) 2 = none := by
  dsimp [comp, computation]
  simp [Fin.cases, Fin.induction, Fin.induction.go]

example : comm.answer (comm.submit sent 2 0 (1, [false])) 2 = none := by
  dsimp [sent, comm, communication, network]
  simp [List.finRange, List.ofFn_succ, List.argmin, List.argAux]

end LongTails.Tests.StarNetwork
