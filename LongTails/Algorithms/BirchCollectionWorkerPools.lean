import LongTails.Algorithms.BirchCollectionLocal

namespace LongTails.Algorithms.BirchCollectionWorkerPools

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionLocal (localComplete localAbort)

structure Worker where
  base : ℕ := 0
  head : ℕ := 0
  frontier : ℕ := 0
  privateLabels : List ℕ := []
  pending : Option Ticket := none

structure Pool (m : ℕ) where
  main : ℕ := 0
  worker : Fin m → Worker := fun _ => {}
  trace : TraceState := {}
  events : List Event := []
  accepted : List ℕ := []
  cuts : List ℕ := [0]
  frontiers : List ℕ := []

def Pool.append {m : ℕ} (s : Pool m) (events : List Event) : Pool m :=
  {s with trace := events.foldl step s.trace, events := s.events ++ events}

def Pool.put {m : ℕ} (s : Pool m) (w : Fin m) (worker : Worker) : Pool m :=
  {s with worker := Function.update s.worker w worker}

def issue {m : ℕ} (B : ℕ) (move : ℝ) (s : Pool m) (w : Fin m) : Pool m :=
  let worker := s.worker w
  let events := Event.capture (w.val + 1) worker.head B 1 move ::
    List.replicate B (.issue s.trace.nextCollection (w.val + 1))
  (s.append events).put w {worker with pending := some ⟨s.trace.nextCollection, s.trace.nextRaw⟩}

def complete {m : ℕ} (B : ℕ) (s : Pool m) (w : Fin m) : Pool m :=
  let worker := s.worker w
  match worker.pending with
  | none => s
  | some ticket =>
    (s.append (localComplete B ticket)).put w {worker with
      head := s.trace.nextState
      privateLabels := worker.privateLabels ++ [s.trace.nextDirection]
      pending := none}

def discard {m : ℕ} (B : ℕ) (s : Pool m) (w : Fin m) : Pool m :=
  let worker := s.worker w
  match worker.pending with
  | none => s
  | some ticket => (s.append (localAbort B ticket)).put w {worker with pending := none}

def selectedLabels {m : ℕ} (s : Pool m) (workers : List (Fin m)) : List ℕ :=
  workers.flatMap fun w => (s.worker w).privateLabels

def selectedFrontiers {m : ℕ} (s : Pool m) (workers : List (Fin m)) : List ℕ :=
  workers.flatMap fun w =>
    List.replicate (s.worker w).privateLabels.length (s.worker w).frontier

def publishState {m : ℕ} (B : ℕ) (s : Pool m) (workers : List (Fin m)) : Pool m :=
  let pendingClosed := workers.foldl (discard B) s
  let labels := selectedLabels s workers
  if labels.isEmpty then pendingClosed else
    let (merged, head) := workers.foldl (fun (t, left) w =>
      (t.append [.merge 0 left (s.worker w).head (s.worker w).base], t.trace.nextState))
      (pendingClosed, s.main)
    {merged.append [.mark head] with
      main := head
      accepted := s.accepted ++ labels
      cuts := s.cuts ++ [s.accepted.length + labels.length]
      frontiers := s.frontiers ++ selectedFrontiers s workers}

def publish {m : ℕ} (B : ℕ) (s : Pool m) (workers : List (Fin m)) : Pool m :=
  let out := publishState B s workers
  let root : Worker := {base := out.main, head := out.main, frontier := out.accepted.length}
  workers.foldl (fun t w => t.put w root) out

def cycleGroups (workers groupSize : ℕ) : ℕ :=
  if workers = 0 then 0 else (workers - 1) / groupSize + 1

def cycleGroup (workers groupSize tick : ℕ) : List (Fin workers) :=
  (List.finRange workers).filter (fun w => w.val / groupSize = tick % cycleGroups workers groupSize)

def cycleCompute {m : ℕ} (B : ℕ) (move : ℝ) (s : Pool m) : Pool m :=
  (List.finRange m).foldl (fun t w => complete B (issue B move t w) w) s

def cycleStep {m : ℕ} (groupSize B : ℕ) (move : ℝ) (s : Pool m) (tick : ℕ) : Pool m :=
  publish B (cycleCompute B move s) (cycleGroup m groupSize tick)

def cycle (m groupSize B K : ℕ) (move : ℝ) : Pool m :=
  (List.range K).foldl (cycleStep groupSize B move) {}

def remaining {m : ℕ} (s : Pool m) : ℕ :=
  ∑ w : Fin m, (s.worker w).privateLabels.length

def age {m : ℕ} (s : Pool m) (w : Fin m) : ℕ :=
  s.accepted.length - (s.worker w).frontier

def maxAge {m : ℕ} (s : Pool m) : ℕ :=
  Finset.univ.sup (age s)

def hardWorkers {m : ℕ} (s : Pool m) (Q : ℕ) : List (Fin m) :=
  (List.finRange m).filter (fun w => age s w + remaining s = Q)

inductive MetaEvent (m : ℕ) where
  | query (worker : Fin m)
  | reply (worker : Fin m)
  | sync (workers : List (Fin m))

def MetaEnabled {m : ℕ} (Q : ℕ) (s : Pool m) : MetaEvent m → Prop
  | .query w => (s.worker w).pending = none
  | .reply w => (s.worker w).pending.isSome
  | .sync ws => ws.Nodup ∧
    (Q ≤ maxAge s + remaining s → ws.toFinset = (hardWorkers s Q).toFinset)

def metaAdvance {m : ℕ} (Q B : ℕ) (move : ℝ) (s : Pool m) : MetaEvent m → Pool m
  | .query w => issue B move s w
  | .reply w =>
    if maxAge s + remaining s < Q then complete B s w else discard B s w
  | .sync ws => publish B s ws

def MetaLegal {m : ℕ} (Q B : ℕ) (move : ℝ) : Pool m → List (MetaEvent m) → Prop
  | _, [] => True
  | s, e :: es => MetaEnabled Q s e ∧ MetaLegal Q B move (metaAdvance Q B move s e) es

def metaRun {m : ℕ} (Q B : ℕ) (move : ℝ) (events : List (MetaEvent m)) : Pool m :=
  events.foldl (metaAdvance Q B move) {}

def ordering {m : ℕ} (s : Pool m) : LongTails.Setups.BirchCollections.Ordering where
  labels := s.accepted
  cut := fun k => s.cuts[k]?.getD 0
  frontier := fun n => s.frontiers[n]?.getD 0
  anchor := id
  scale := fun _ _ => 1
  renewalFrontier := fun _ _ => 0

end LongTails.Algorithms.BirchCollectionWorkerPools
