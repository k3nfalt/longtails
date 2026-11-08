import LongTails.Algorithms.BirchCollectionLocal

namespace LongTails.Algorithms.BirchCollectionDualProcess

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionLocal (localComplete localAbort)

abbrev PhysicalEvent := LongTails.Setups.BirchCollections.Event

inductive Event (m : ℕ) where
  | query (worker : Fin m)
  | compute (worker : Fin m)
  | send (worker : Fin m)
  | acknowledge (worker : Fin m)

structure Prefix where
  point : ℕ
  count : ℕ := 0

structure Worker where
  privateHead : Prefix
  acknowledged : Prefix
  message : Option Prefix := none
  pending : Option Ticket := none

structure Round (m : ℕ) where
  base : ℕ
  worker : Fin m → Worker
  acknowledged : ℕ := 0
  trace : TraceState
  events : List PhysicalEvent
  accepted : List ℕ

def initial (m : ℕ) (trace : TraceState) (events : List PhysicalEvent) (accepted : List ℕ) : Round m :=
  let base := trace.markers.getLast?.getD 0
  {base, worker := fun _ => {privateHead := ⟨base, 0⟩, acknowledged := ⟨base, 0⟩},
    trace, events, accepted}

def Round.append {m : ℕ} (s : Round m) (events : List PhysicalEvent) : Round m :=
  {s with trace := events.foldl step s.trace, events := s.events ++ events}

def Enabled {m : ℕ} (Q : ℕ) (s : Round m) : Event m → Prop
  | .query w => s.acknowledged ≠ Q ∧ (s.worker w).pending = none
  | .compute w => s.acknowledged ≠ Q ∧ (s.worker w).pending.isSome
  | .send w => s.acknowledged ≠ Q ∧ (s.worker w).message = none ∧
      (s.worker w).acknowledged.count < (s.worker w).privateHead.count
  | .acknowledge w => s.acknowledged ≠ Q ∧ (s.worker w).message.isSome

def advance {m : ℕ} (B : ℕ) (move : ℝ) (s : Round m) : Event m → Round m
  | .query w =>
    let worker := s.worker w
    let capture : PhysicalEvent := .capture (w.val + 1) worker.privateHead.point B 1 move
    let es := capture :: List.replicate B (.issue s.trace.nextCollection (w.val + 1))
    {s.append es with
      worker := Function.update s.worker w
        {worker with pending := some ⟨s.trace.nextCollection, s.trace.nextRaw⟩}}
  | .compute w =>
    let worker := s.worker w
    match worker.pending with
    | none => s
    | some j =>
      {s.append (localComplete B j) with
        worker := Function.update s.worker w
          {worker with
            privateHead := ⟨s.trace.nextState, worker.privateHead.count + 1⟩
            pending := none}}
  | .send w =>
    {s with
      worker := Function.update s.worker w
        {s.worker w with message := some (s.worker w).privateHead}}
  | .acknowledge w =>
    let worker := s.worker w
    match worker.message with
    | none => s
    | some sent =>
      let receive : PhysicalEvent := .merge 0 worker.acknowledged.point sent.point worker.acknowledged.point
      {s.append [receive] with
        worker := Function.update s.worker w
          {worker with
            acknowledged := ⟨s.trace.nextState, sent.count⟩
            message := none}
        acknowledged := s.acknowledged + (sent.count - worker.acknowledged.count)}

def LegalFrom {m : ℕ} (Q B : ℕ) (move : ℝ) : Round m → List (Event m) → Prop
  | _, [] => True
  | s, e :: es => Enabled Q s e ∧ LegalFrom Q B move (advance B move s e) es

def abortPending {m : ℕ} (B : ℕ) (s : Round m) : Round m :=
  (List.finRange m).foldl (fun t w =>
    match (t.worker w).pending with
    | none => t
    | some j => t.append (localAbort B j)) s

def publish {m : ℕ} (B : ℕ) (s : Round m) : Round m :=
  let s := abortPending B s
  let (out, head) := (List.finRange m).foldl (fun (t, left) w =>
    (t.append [.merge 0 left (s.worker w).acknowledged.point s.base], t.trace.nextState)) (s, s.base)
  let newLabels := (List.range out.trace.nextDirection).filter (fun d =>
    d ∈ (out.trace.states head).history ∧ d ∉ (out.trace.states s.base).history)
  {out.append [.mark head] with accepted := s.accepted ++ newLabels}

def runRound {m : ℕ} (B : ℕ) (move : ℝ) (s : Round m) (events : List (Event m)) : Round m :=
  let t := initial m s.trace s.events s.accepted
  publish B (events.foldl (advance B move) t)

def runRounds {m : ℕ} (B : ℕ) (move : ℝ) (rounds : List (List (Event m))) : Round m :=
  rounds.foldl (runRound B move) (initial m {} [] [])

def CompleteRounds {m : ℕ} (Q B : ℕ) (move : ℝ) : Round m → List (List (Event m)) → Prop
  | _, [] => True
  | s, es :: rest =>
    let t := initial m s.trace s.events s.accepted
    let out := es.foldl (advance B move) t
    LegalFrom Q B move t es ∧ out.acknowledged = Q ∧ CompleteRounds Q B move (publish B out) rest

def privateSteps {m : ℕ} (w : Fin m) : ℕ → List (Event m)
  | 0 => []
  | n + 1 => .query w :: .compute w :: privateSteps w n

def overlapWitness {m : ℕ} (w : Fin m) (Q suffix : ℕ) : List (Event m) :=
  privateSteps w Q ++ [.send w] ++ privateSteps w suffix ++ [.acknowledge w]

end LongTails.Algorithms.BirchCollectionDualProcess
