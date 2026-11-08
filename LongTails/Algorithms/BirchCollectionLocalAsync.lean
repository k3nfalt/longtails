import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionLocal

namespace LongTails.Algorithms.BirchCollectionLocalAsync

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round localComplete publish)
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)

def capture {m : ℕ} (group : Fin m → Fin m) (B : ℕ) (movement : ℝ)
    (s : Round m) (w : Fin m) : List Event :=
  .capture (w.val + 1) (s.head (group w)) B 1 movement ::
    List.replicate B (.issue s.trace.nextCollection (w.val + 1))

def complete {m : ℕ} (group : Fin m → Fin m) (B : ℕ) (s : Round m) (w : Fin m)
    (ticket : Ticket) : List Event :=
  let saved := (s.trace.collections ticket.collection).source
  localComplete B ticket ++ [.merge ((group w).val + 1) (s.head (group w)) s.trace.nextState saved]

def advance {m : ℕ} (group : Fin m → Fin m) (B : ℕ) (movement : ℝ) (s : Round m) :
    OriginalEvent m → Round m
  | .query w =>
      { s.append (capture group B movement s w) with
        pending := Function.update s.pending w (some ⟨s.trace.nextCollection, s.trace.nextRaw⟩) }
  | .reply w =>
      match s.pending w with
      | none => s
      | some ticket =>
        { s.append (complete group B s w ticket) with
          head := Function.update s.head (group w) (s.trace.nextState + 1)
          pending := Function.update s.pending w none
          completed := s.completed + 1 }

def LegalFrom {m : ℕ} (group : Fin m → Fin m) (Q B : ℕ) (movement : ℝ) :
    Round m → List (OriginalEvent m) → Prop
  | _, [] => True
  | s, e :: es =>
      LongTails.Algorithms.BirchCollectionLocal.Enabled Q s e ∧
        LegalFrom group Q B movement (advance group B movement s e) es

def runRound {m : ℕ} (group : Fin m → Fin m) (B : ℕ) (movement : ℝ)
    (s : Round m) (events : List (OriginalEvent m)) : Round m :=
  publish B (events.foldl (advance group B movement) s)

def runRounds {m : ℕ} (group : Fin m → Fin m) (B : ℕ) (movement : ℝ)
    (events : List (List (OriginalEvent m))) : Round m :=
  events.foldl (fun s es => runRound group B movement (Round.initial m s.trace s.events) es)
    (Round.initial m {} [])

def CompleteRounds {m : ℕ} (group : Fin m → Fin m) (Q B : ℕ) (movement : ℝ) :
    Round m → List (List (OriginalEvent m)) → Prop
  | _, [] => True
  | s, es :: rest =>
      let start := Round.initial m s.trace s.events
      let privateRound := es.foldl (advance group B movement) start
      LegalFrom group Q B movement start es ∧ privateRound.completed = Q ∧
        CompleteRounds group Q B movement (publish B privateRound) rest

def returns {m : ℕ} : List (Fin m) → List (OriginalEvent m)
  | [] => []
  | [w] => [.reply w]
  | w :: v :: rest => .reply w :: .query w :: returns (v :: rest)

def arrivalWord {m : ℕ} (order : List (Fin m)) : List (OriginalEvent m) :=
  (List.finRange m).map LongTails.Algorithms.BirchNonEuclideanRennala.Event.query ++ returns order

def arrivalRounds {m : ℕ} (orders : List (List (Fin m))) : List (List (OriginalEvent m)) :=
  orders.map arrivalWord


open LongTails.Algorithms.BirchCollectionProfiles (controls divisor resetOrdering)
open LongTails.Algorithms.BirchCollectionLocal (tuned localOrdering)

noncomputable def localAsync (p : Params) (m Q : ℕ) (group : Fin m → Fin m)
    (rounds : List (List (OriginalEvent m))) : Params :=
  let q := tuned p m Q
  let B := batchSize q
  let K := horizon q
  let move := 1 / (divisor Q (Q - 1) : ℝ)
  let s := runRounds group B move rounds
  {q with
    controls := controls Q Q (Q - 1) (s.trace.nextRaw - B * (K * Q))
    events := s.events
    ordering := resetOrdering (localOrdering Q K)}

noncomputable abbrev Complete (p : Params) (m Q : ℕ) (group : Fin m → Fin m)
    (rounds : List (List (OriginalEvent m))) : Prop :=
  let q := tuned p m Q
  rounds.length = horizon q ∧
    CompleteRounds group Q (batchSize q) (1 / (divisor Q (Q - 1) : ℝ)) (Round.initial m {} []) rounds

end LongTails.Algorithms.BirchCollectionLocalAsync
