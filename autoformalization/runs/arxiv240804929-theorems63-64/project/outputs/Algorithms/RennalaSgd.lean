import outputs.Algorithms.RennalaModel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.List.FinRange

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.Rennala

structure Job (d : ℕ) where
  started : ℝ
  point : Point d
  tag : ℕ

abbrev Query (p : Public) := Option (Fin p.n → Job p.d)

abbrev Reply (p : Public) := Option (Fin p.n × ℝ × ℕ × Point p.d)

structure State (p : Public) where
  iteration : ℕ
  count : ℕ
  accumulator : Point p.d
  point : Point p.d
  jobs : Fin p.n → Job p.d
  clock : ℝ
  chosenIndex : Fin (p.horizon + 1)
  selected : Point p.d

noncomputable def nextWorker {n : ℕ} (tau started : Fin n → ℝ) :
    List (Fin n) → Option (Fin n)
  | [] => none
  | i :: rest =>
      match nextWorker tau started rest with
      | none => some i
      | some j => if started i + tau i ≤ started j + tau j then some i else some j

def initialState (p : Public) (j : Fin (p.horizon + 1)) : State p where
  iteration := 0
  count := 0
  accumulator := 0
  point := p.x0
  jobs := fun _ => ⟨0, p.x0, 0⟩
  clock := 0
  chosenIndex := j
  selected := p.x0

noncomputable def eventAnswer (p : Public) (tau : Fin p.n → ℝ) {Ω : Type}
    (g : Point p.d → Ω → Point p.d) (query : Query p) (seed : Ω) : Reply p :=
  match query with
  | none => none
  | some jobs =>
      match nextWorker tau (fun i => (jobs i).started) (List.finRange p.n) with
      | none => none
      | some i => some (i, (jobs i).started + tau i, (jobs i).tag, g (jobs i).point seed)

noncomputable def eventOracle (p : Public) (tau : Fin p.n → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) : Oracle (Query p) (Reply p) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, query) seed => eventAnswer p tau g query seed

noncomputable def updateCore (p : Public) (s : State p) (reply : Reply p) : State p :=
    match reply with
    | none => s
    | some (i, time, tag, g) =>
        let jobs := Function.update s.jobs i ⟨time, s.point, s.iteration⟩
        let count := if tag = s.iteration then s.count + 1 else s.count
        let accumulator := if tag = s.iteration then
          s.accumulator + (1 / (batchSize p.v p.eps : ℝ)) • g else s.accumulator
        if count = batchSize p.v p.eps then
          let point := s.point - stepSize p.L p.v p.eps • accumulator
          { s with
            iteration := s.iteration + 1
            count := 0
            accumulator := 0
            point := point
            jobs := jobs
            clock := time
            selected := if s.chosenIndex.val = s.iteration + 1 then point else s.selected }
        else
          { s with count := count, accumulator := accumulator, jobs := jobs, clock := time }

noncomputable def update (p : Public) (s : State p) (reply : Reply p) : State p :=
  if p.horizon ≤ s.iteration then s else updateCore p s reply

noncomputable def algorithm (p : Public) : Algorithm (Query p) (Reply p) (Point p.d × ℝ) where
  Seed := Fin (p.horizon + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (p.horizon + 1))).toMeasure, inferInstance⟩
  State := State p
  initial := initialState p
  query := fun s => (0, if p.horizon ≤ s.iteration then none else some s.jobs)
  update := update p
  output := fun s => (s.selected, s.clock)

noncomputable def batchEstimator {d : ℕ} {Ω : Type} (S : ℕ)
    (g : Point d → Ω → Point d) (x : Point d) (seeds : Fin S → Ω) : Point d :=
  (1 / (S : ℝ)) • ∑ i, g x (seeds i)

noncomputable def iterate {d : ℕ} {Ω : Type} (g : Point d → Ω → Point d)
    (gamma : ℝ) (S : ℕ) (x0 : Point d) (seeds : ℕ → Ω) : ℕ → Point d
  | 0 => x0
  | k + 1 =>
      let x := iterate g gamma S x0 seeds k
      x - gamma • batchEstimator S g x (fun i => seeds (k * S + i.val))

end OracleTemplate.Rennala
