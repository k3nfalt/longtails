import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionLocal

namespace LongTails.Algorithms.BirchCollectionAsyncLocal

open LongTails.Setups.BirchCollections (Params batchSize horizon)

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionLocal (localComplete localAbort)

inductive Event (m : ℕ) where
  | query (worker : Fin m)
  | localReply (worker : Fin m)
  | submit (worker : Fin m)

structure Worker where
  base : ℕ := 0
  head : ℕ := 0
  round : ℕ := 0
  directions : List ℕ := []
  pending : Option Ticket := none

structure Controller (m : ℕ) where
  main : ℕ := 0
  rounds : ℕ := 0
  worker : Fin m → Worker := fun _ => {}
  trace : TraceState := {}
  events : List LongTails.Setups.BirchCollections.Event := []
  accepted : List ℕ := []
  frontiers : List ℕ := []

def Controller.append {m : ℕ} (s : Controller m)
    (events : List LongTails.Setups.BirchCollections.Event) : Controller m :=
  {s with trace := events.foldl step s.trace, events := s.events ++ events}

def delayWindow (G M : ℕ) : ℕ := ((G - 1) / M) * M + (M - 1)

def accepts {m : ℕ} (G M : ℕ) (s : Controller m) (w : Fin m) : Prop :=
  (s.rounds - (s.worker w).round) * M < G

instance {m : ℕ} (G M : ℕ) (s : Controller m) (w : Fin m) : Decidable (accepts G M s w) :=
  inferInstanceAs (Decidable (_ < _))

def Enabled {m : ℕ} (K M : ℕ) (s : Controller m) : Event m → Prop
  | .query w => s.rounds < K ∧ (s.worker w).directions.length < M ∧ (s.worker w).pending = none
  | .localReply w => s.rounds < K ∧ (s.worker w).directions.length < M ∧ (s.worker w).pending.isSome
  | .submit w => s.rounds < K ∧ (s.worker w).directions.length = M ∧ (s.worker w).pending = none

def restart {m : ℕ} (s t : Controller m) (w : Fin m) : Controller m :=
  {t with worker := Function.update s.worker w {base := t.main, head := t.main, round := t.rounds}}

def advance {m : ℕ} (B G M : ℕ) (move : ℝ) (s : Controller m) : Event m → Controller m
  | .query w =>
    let worker := s.worker w
    let events := LongTails.Setups.BirchCollections.Event.capture (w.val + 1) worker.head B 1 move ::
      List.replicate B (.issue s.trace.nextCollection (w.val + 1))
    {s.append events with
      worker := Function.update s.worker w
        {worker with pending := some ⟨s.trace.nextCollection, s.trace.nextRaw⟩}}
  | .localReply w =>
    let worker := s.worker w
    match worker.pending with
    | none => s
    | some j =>
      {s.append (localComplete B j) with
        worker := Function.update s.worker w
          {worker with
            head := s.trace.nextState
            directions := worker.directions ++ [s.trace.nextDirection]
            pending := none}}
  | .submit w =>
    let worker := s.worker w
    let t := if accepts G M s w then
      {s.append [.merge 0 s.main worker.head worker.base, .mark s.trace.nextState] with
        main := s.trace.nextState
        rounds := s.rounds + 1
        accepted := s.accepted ++ worker.directions
        frontiers := s.frontiers ++ List.replicate M (M * worker.round)}
      else s
    restart s t w

def LegalFrom {m : ℕ} (K B G M : ℕ) (move : ℝ) :
    Controller m → List (Event m) → Prop
  | _, [] => True
  | s, e :: es => Enabled K M s e ∧ LegalFrom K B G M move (advance B G M move s e) es

def controller {m : ℕ} (B G M : ℕ) (move : ℝ) (events : List (Event m)) : Controller m :=
  events.foldl (advance B G M move) {}

def close {m : ℕ} (B : ℕ) (s : Controller m) : Controller m :=
  (List.finRange m).foldl (fun t w =>
    match (t.worker w).pending with
    | none => t
    | some j =>
      { t.append (localAbort B j) with
        worker := Function.update t.worker w { (t.worker w) with pending := none } }) s

def ordering {m : ℕ} (M : ℕ) (s : Controller m) : LongTails.Setups.BirchCollections.Ordering where
  labels := s.accepted
  cut := fun k => k * M
  frontier := fun n => s.frontiers[n]?.getD 0
  anchor := id
  scale := fun _ _ => 1
  renewalFrontier := fun _ _ => 0


open LongTails.Algorithms.BirchCollectionProfiles (controls divisor resetOrdering)

noncomputable def tuned (p : Params) (m G M : ℕ) : Params :=
  {p with workers := m + 1, controls := controls M M (delayWindow G M) 0}

noncomputable def asyncLocal (p : Params) (m G M : ℕ) (events : List (Event m)) : Params :=
  let q := tuned p m G M
  let W := delayWindow G M
  let B := batchSize q
  let K := horizon q
  let s := controller B G M (1 / (divisor M W : ℝ)) events
  {q with
    controls := controls M M W (s.trace.nextRaw - B * (K * M))
    events := s.events
    ordering := resetOrdering (ordering M s)}

noncomputable abbrev Complete (p : Params) (m G M : ℕ) (events : List (Event m)) : Prop :=
  let q := tuned p m G M
  let W := delayWindow G M
  let B := batchSize q
  let K := horizon q
  let move := 1 / (divisor M W : ℝ)
  LegalFrom K B G M move {} events ∧ (controller B G M move events).rounds = K

end LongTails.Algorithms.BirchCollectionAsyncLocal
