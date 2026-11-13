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
  timePerFloat _ _ := 0
  connected _ _ := false

theorem no_fuel :
    executeTimed (fun _ => successor) (queueEnvironment unitNetwork) counter 5 0
      ((), (), fun _ _ => ()) = 0 := rfl

theorem two_calls_before_time_cap :
    executeTimed (fun _ => successor) (queueEnvironment unitNetwork) counter (5 / 2) 10
      ((), (), fun _ _ => ()) = 2 := by
  norm_num [executeTimed, runTimed, initialTimedConfig, deliverEvent, issueAction,
    handleCompletion, queueEnvironment, queueSubmit, scheduleCall, queueNext, earliest,
    counter, successor, unitNetwork, List.finRange, Function.update]

end OracleTemplate.TimedTests
