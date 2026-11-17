import LongTails.TemplateTimedLowerBound
import LongTails.Setups.NetworkModels
import Mathlib.Tactic

open MeasureTheory

noncomputable section

namespace OracleTemplate.TimedTests

open LongTails.Setups.NetworkModels

def counter : TimedAlgorithm 1 ℕ ℕ ℕ where
  State := ℕ
  root := 0
  initial _ _ := 0
  react _ _ s
    | .start => (s, [.call s])
    | .replied _ reply => (reply, [.call reply])
    | .received _ _ => (s, [])
  output s := s

def successor : Oracle ℕ ℕ where
  answer _ q _ := q.2 + 1

def unitNetwork : QueueNetwork 1 where
  computeTime _ := 1
  channel _ _ := 0
  latency _ _ := 0
  timePerBit _ _ := 0
  connected _ _ := false

theorem no_fuel :
    executeTimed (fun _ => successor) (queueEnvironment unitNetwork) counter 5 0
      ((), (), fun _ _ => ()) = 0 := rfl

theorem two_calls_before_time_cap :
    executeTimed (fun _ => successor) (queueEnvironment unitNetwork) counter (5 / 2) 10
      ((), (), fun _ _ => ()) = 2 := by
  dsimp [executeTimed, counter, successor, queueEnvironment, unitNetwork]
  norm_num [runTimed, initialTimedConfig, deliverEvent, issueAction,
    handleCompletion, queueEnvironment, queueSubmit, scheduleCall, queueNext, earliest,
    counter, successor, unitNetwork, List.finRange, Function.update]

def messenger : TimedAlgorithm 2 Unit Unit (List Bool) where
  State := List Bool
  root := 1
  initial _ _ := []
  react v _ s
    | .start => (s, if v = 0 then [.send {1} [true, false, true]] else [])
    | .received _ bits => (s ++ bits, [])
    | .replied _ _ => (s, [])
  output := id

def bitNetwork : QueueNetwork 2 where
  computeTime _ := 1
  channel _ _ := 0
  latency _ _ := 1
  timePerBit _ _ := 2
  connected _ _ := true

def silent : Oracle Unit Unit where
  answer _ _ _ := ()

theorem bits_not_delivered_before_deadline :
    executeTimed (fun _ => silent) (queueEnvironment bitNetwork) messenger 6 2
      ((), (), fun _ _ => ()) = [] := by
  dsimp [executeTimed, messenger, silent, queueEnvironment, bitNetwork]
  norm_num [runTimed, initialTimedConfig, deliverEvent, issueAction, handleCompletion,
    queueSubmit, scheduleSend, scheduleDelivery, queueNext, earliest,
    List.finRange, Function.update]

theorem bits_delivered_at_deadline :
    executeTimed (fun _ => silent) (queueEnvironment bitNetwork) messenger 7 2
      ((), (), fun _ _ => ()) = [true, false, true] := by
  dsimp [executeTimed, messenger, silent, queueEnvironment, bitNetwork]
  norm_num [runTimed, initialTimedConfig, deliverEvent, issueAction, handleCompletion,
    queueSubmit, scheduleSend, scheduleDelivery, queueNext, earliest,
    List.finRange, Function.update]

theorem delivered_message_removed :
    (handleCompletion (fun _ => silent) (queueEnvironment bitNetwork) messenger
      (fun _ _ => ()) (initialTimedConfig (queueEnvironment bitNetwork) messenger () ())
      (.delivered 0 1)).sends = [] := by
  dsimp [messenger, silent, queueEnvironment, bitNetwork]
  norm_num [initialTimedConfig, deliverEvent, issueAction, handleCompletion,
    queueSubmit, scheduleSend, scheduleDelivery, List.finRange, Function.update]

theorem duplicate_delivery_ignored :
    let c := initialTimedConfig (queueEnvironment bitNetwork) messenger () ()
    let deliver := fun c => handleCompletion (fun _ => silent) (queueEnvironment bitNetwork)
      messenger (fun _ _ => ()) c (.delivered 0 1)
    (deliver (deliver c)).states 1 = [true, false, true] := by
  dsimp [messenger, silent, queueEnvironment, bitNetwork]
  norm_num [initialTimedConfig, deliverEvent, issueAction, handleCompletion,
    queueSubmit, scheduleSend, scheduleDelivery, List.finRange, Function.update]

end OracleTemplate.TimedTests
