import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionDualProcess
import LongTails.Algorithms.BirchCollectionWorkerPools

namespace LongTails.Algorithms.BirchCollectionDualPool

open LongTails.Setups.BirchCollections (Params batchSize horizon)

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Algorithms.BirchCollectionDualProcess (Prefix)

abbrev Action := LongTails.Algorithms.BirchCollectionDualProcess.Event

structure Record where
  acknowledged : Prefix
  message : Option Prefix := none

structure Round (m : ℕ) where
  pool : Pool m
  record : Fin m → Record

def initial {m : ℕ} (s : Pool m) : Round m :=
  {pool := s, record := fun _ => {acknowledged := ⟨s.main, 0⟩}}

def acknowledged {m : ℕ} (s : Round m) : ℕ := ∑ w : Fin m, (s.record w).acknowledged.count

def Enabled {m : ℕ} (Q : ℕ) (s : Round m) (e : Action m) : Prop :=
  acknowledged s ≠ Q ∧ match e with
  | .query w => (s.pool.worker w).pending = none
  | .compute w => (s.pool.worker w).pending.isSome
  | .send w => (s.record w).message = none ∧
      (s.record w).acknowledged.count < (s.pool.worker w).privateLabels.length
  | .acknowledge w => (s.record w).message.isSome

def advance {m : ℕ} (B : ℕ) (move : ℝ) (s : Round m) : Action m → Round m
  | .query w => {s with pool := issue B move s.pool w}
  | .compute w => {s with pool := complete B s.pool w}
  | .send w =>
    let src := s.pool.worker w
    let msg : Prefix := ⟨src.head, src.privateLabels.length⟩
    {s with
      record := Function.update s.record w {s.record w with message := some msg}}
  | .acknowledge w =>
    match (s.record w).message with
    | none => s
    | some sent =>
      let old := (s.record w).acknowledged.point
      let p := s.pool.append [.merge 0 old sent.point old]
      {pool := p, record := Function.update s.record w
        {acknowledged := ⟨s.pool.trace.nextState, sent.count⟩}}

def LegalFrom {m : ℕ} (Q B : ℕ) (move : ℝ) : Round m → List (Action m) → Prop
  | _, [] => True
  | s, e :: es => Enabled Q s e ∧ LegalFrom Q B move (advance B move s e) es

def clip {m : ℕ} (s : Round m) (closed : Pool m) : Pool m :=
  { closed with worker := fun w =>
    let ack := (s.record w).acknowledged
    {closed.worker w with
      head := ack.point
      privateLabels := (closed.worker w).privateLabels.take ack.count
      pending := none}}

def finishRound {m : ℕ} (B : ℕ) (s : Round m) : Pool m :=
  let workers := List.finRange m
  let closed := workers.foldl (discard B) s.pool
  publish B (clip s closed) workers

def runRound {m : ℕ} (B : ℕ) (move : ℝ) (p : Pool m) (events : List (Action m)) : Pool m :=
  finishRound B (events.foldl (advance B move) (initial p))

def runRounds {m : ℕ} (B : ℕ) (move : ℝ) (events : List (List (Action m))) : Pool m :=
  events.foldl (runRound B move) {}

def CompleteRounds {m : ℕ} (Q B : ℕ) (move : ℝ) : Pool m → List (List (Action m)) → Prop
  | _, [] => True
  | p, es :: rest =>
    let out := es.foldl (advance B move) (initial p)
    LegalFrom Q B move (initial p) es ∧ acknowledged out = Q ∧ CompleteRounds Q B move (finishRound B out) rest


open LongTails.Algorithms.BirchCollectionProfiles (controls divisor resetOrdering)
open LongTails.Algorithms.BirchCollectionWorkerPools (ordering)

noncomputable def tuned (p : Params) (m Q : ℕ) : Params :=
  {p with workers := m + 1, controls := controls Q Q (Q - 1) 0}

noncomputable def dualProcess (p : Params) (m Q : ℕ) (events : List (List (Action m))) : Params :=
  let q := tuned p m Q
  let B := batchSize q
  let s := runRounds B (1 / (divisor Q (Q - 1) : ℝ)) events
  {q with
    controls := controls Q Q (Q - 1) (s.trace.nextRaw - B * s.accepted.length)
    events := s.events
    ordering := resetOrdering (ordering s)}

noncomputable abbrev Complete (p : Params) (m Q : ℕ) (events : List (List (Action m))) : Prop :=
  let q := tuned p m Q
  events.length = horizon q ∧
    CompleteRounds Q (batchSize q) (1 / (divisor Q (Q - 1) : ℝ)) {} events

end LongTails.Algorithms.BirchCollectionDualPool
