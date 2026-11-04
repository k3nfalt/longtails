import LongTails.Algorithms.QuarticAcceleration
import LongTails.Algorithms.QuarticProximalTrial

namespace LongTails.Algorithms.AcceleratedQuarticNewton

open LongTails.Algorithms.CompositeCubicAcceleration hiding advance damping
open LongTails.Algorithms.QuarticAcceleration
open LongTails.Algorithms.QuarticProximalTrial
open OracleTemplate OracleTemplate.QueryPlan

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

inductive Status where
  | initial
  | running (guess : ℝ) (state : State E)
  | finished (point : E)
  | failed

noncomputable def queryCenter (x0 : E) : Status E → E
  | .running μ s => center E μ s
  | _ => x0

noncomputable def receive (γ : ℝ) (x0 : E) (status : Status E) : TrialResult E → Status E
  | .accurate y => .finished y
  | .failed => .failed
  | .proximal y g =>
    let c := queryCenter E x0 status
    let lam := parameter E γ c y
    if lam = 0 then .finished y
    else match status with
    | .initial => .running (lam / 4) (advance E lam γ ⟨0, x0, x0⟩ y g)
    | .running μ s => .running (nextGuess μ lam) (advance E μ γ s y g)
    | .finished z => .finished z
    | .failed => .failed

variable {E} {n : ℕ} [NeZero n]

noncomputable def round (ε R Q L γ : ℝ) (x0 : E)
    (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) (status : Status E) :
    QueryPlan (Fin n × E) (LongTails.Algorithms.TaylorCorrectedNewton.Reply E) (Status E) (trialCost n Q) :=
  match status with
  | .finished y => padResult (0, x0) (trialCost n Q) (.finished y)
  | .failed => padResult (0, x0) (trialCost n Q) .failed
  | _ => (trial ε R Q L γ x0 (queryCenter E x0 status) seed).map (receive E γ x0 status)

noncomputable def run (ε R Q L γ : ℝ) (x0 : E) : (K : ℕ) →
    (Fin K → Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) → Status E →
    QueryPlan (Fin n × E) (LongTails.Algorithms.TaylorCorrectedNewton.Reply E) (Status E) (trialCost n Q * K)
  | 0, _, status => .done status
  | K + 1, seed, status => (round ε R Q L γ x0 (seed 0) status).bind
      (run ε R Q L γ x0 K (Fin.tail seed))

noncomputable def output (x0 : E) : Status E → E
  | .running _ s => s.point
  | .finished y => y
  | _ => x0

end LongTails.Algorithms.AcceleratedQuarticNewton
