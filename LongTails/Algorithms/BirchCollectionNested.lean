import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionLocalAsync

namespace LongTails.Algorithms.BirchCollectionNested

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round localAbort abortPending publish)

structure Layout (m : ℕ) where
  group : Fin m → Fin m
  cluster : Fin m → Fin m
  quota : Fin m → Option ℕ

def groups {m : ℕ} (layout : Layout m) (i : Fin m) : List (Fin m) :=
  (List.finRange m).filter (fun g => layout.cluster g = i)

def workers {m : ℕ} (layout : Layout m) (i : Fin m) : List (Fin m) :=
  (List.finRange m).filter (fun w => layout.cluster (layout.group w) = i)

structure Cluster where
  point : ℕ
  completed : ℕ := 0

structure State (m : ℕ) where
  outer : Round m
  cluster : Fin m → Cluster

def start {m : ℕ} (layout : Layout m) (B : ℕ) (move : ℝ) (trace : TraceState)
    (events : List Event) : State m :=
  let root := Round.initial m trace events
  let outer := (List.finRange m).foldl (fun s w =>
    LongTails.Algorithms.BirchCollectionLocalAsync.advance layout.group B move s (.query w)) root
  {outer, cluster := fun _ => ⟨root.base, 0⟩}

def abortCluster {m : ℕ} (layout : Layout m) (B : ℕ) (s : Round m) (i : Fin m) : Round m :=
  (workers layout i).foldl (fun t w =>
    match t.pending w with
    | none => t
    | some j =>
      { t.append (localAbort B j) with pending := Function.update t.pending w none }) s

def collectCluster {m : ℕ} (layout : Layout m) (s : Round m) (i : Fin m) (base : ℕ) :
    Round m × ℕ :=
  (groups layout i).foldl (fun (t, left) g =>
    (t.append [.merge (i.val + 1) left (s.head g) base], t.trace.nextState)) (s, base)

def synchronize {m : ℕ} (layout : Layout m) (B : ℕ) (move : ℝ) (s : State m) (i : Fin m) :
    State m :=
  let t := abortCluster layout B s.outer i
  let (merged, head) := collectCluster layout t i (s.cluster i).point
  let reset := {merged with head := fun g => if layout.cluster g = i then head else merged.head g}
  let out := (workers layout i).foldl (fun t w =>
    LongTails.Algorithms.BirchCollectionLocalAsync.advance layout.group B move t (.query w)) reset
  {outer := out, cluster := Function.update s.cluster i ⟨head, 0⟩}

def advance {m : ℕ} (layout : Layout m) (Q B : ℕ) (move : ℝ) (s : State m) (w : Fin m) :
    State m :=
  let i := layout.cluster (layout.group w)
  let t := LongTails.Algorithms.BirchCollectionLocalAsync.advance layout.group B move s.outer (.reply w)
  let completed := (s.cluster i).completed + 1
  let u : State m := {outer := t, cluster := Function.update s.cluster i {(s.cluster i) with completed}}
  if t.completed = Q then u
  else if layout.quota i = some completed then synchronize layout B move u i
  else {u with outer :=
    LongTails.Algorithms.BirchCollectionLocalAsync.advance layout.group B move t (.query w)}

def collectAll {m : ℕ} (layout : Layout m) (s : State m) (outer : Round m) : Round m :=
  let (out, heads) := (List.finRange m).foldl (fun (t, heads) i =>
    let (t', head) := collectCluster layout t i (s.cluster i).point
    (t', Function.update heads i head)) (outer, fun i => (s.cluster i).point)
  {out with head := heads}

def publishPrefixes {m : ℕ} (layout : Layout m) (B : ℕ) (s : State m) : Round m :=
  publish B (collectAll layout s (abortPending B s.outer))

def runRound {m : ℕ} (layout : Layout m) (Q B : ℕ) (move : ℝ) (s : Round m)
    (arrivals : List (Fin m)) : Round m :=
  let root := start layout B move s.trace s.events
  let completed := arrivals.foldl (advance layout Q B move) root
  publishPrefixes layout B completed

def runRounds {m : ℕ} (layout : Layout m) (Q B : ℕ) (move : ℝ)
    (arrivals : List (List (Fin m))) : Round m :=
  arrivals.foldl (runRound layout Q B move) (Round.initial m {} [])


open LongTails.Algorithms.BirchCollectionProfiles (controls divisor resetOrdering)
open LongTails.Algorithms.BirchCollectionLocal (tuned localOrdering)

noncomputable def nestedLocalAsync (p : Params) (m Q : ℕ) (layout : Layout m)
    (arrivals : List (List (Fin m))) : Params :=
  let q := tuned p m Q
  let B := batchSize q
  let K := horizon q
  let s := runRounds layout Q B (1 / (divisor Q (Q - 1) : ℝ)) arrivals
  {q with
    controls := controls Q Q (Q - 1) (s.trace.nextRaw - B * (K * Q))
    events := s.events
    ordering := resetOrdering (localOrdering Q K)}

end LongTails.Algorithms.BirchCollectionNested
