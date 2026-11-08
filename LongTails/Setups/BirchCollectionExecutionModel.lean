import LongTails.Setups.BirchCollections

namespace LongTails.Algorithms.BirchNonEuclideanFramework

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (IsBallLMO)

noncomputable def chosenLMO (p : Params) : Point p.d → Point p.d := by
  classical
  exact if h : ∃ lmo : Point p.d → Point p.d, IsBallLMO p.N 1 lmo then Classical.choose h
    else fun _ => 0

end LongTails.Algorithms.BirchNonEuclideanFramework

namespace LongTails.Algorithms.BirchCollections

open LongTails.Setups.BirchCollections
open LongTails.Setups.BirchNonEuclidean (Instruction Program)
open OracleTemplate.Rennala (Point)

structure Registers where
  next : ℕ := 1
  point : ℕ → ℕ := fun _ => 0
  momentum : ℕ → ℕ := fun _ => 0
  raw : ℕ → ℕ := fun _ => 0
  mean : ℕ → ℕ := fun _ => 0
  estimator : ℕ → ℕ := fun _ => 0
  sharp : ℕ → ℕ := fun _ => 0

noncomputable def eventCode (τ : ℝ) (s : TraceState) (r : Registers) : Event → List Instruction
  | .capture worker source _ _ _ =>
      [.sendPoint (s.states source).owner worker (r.point source),
        .sendVector (s.states source).owner worker (r.momentum source)]
  | .issue collection worker =>
      let c := s.collections collection
      [.sendPoint c.owner worker (r.point c.source), .query worker (r.point c.source)]
  | .receive raw =>
      [.sendVector (s.raws raw).worker (s.collections (s.raws raw).collection).owner (r.raw raw)]
  | .finish collection =>
      let c := s.collections collection
      [.mix c.owner (c.delivered.map (fun q => (1 / (c.size : ℝ), r.raw q))),
        .mix c.owner [(c.refresh, r.next), (1 - c.refresh, r.momentum c.source)],
        .sharp c.owner (r.next + 1), .move c.owner (r.point c.source) (r.next + 2) (τ * c.movement)]
  | .merge worker left right common =>
      [.sendPoint (s.states left).owner worker (r.point left),
        .sendVector (s.states left).owner worker (r.momentum left),
        .sendPoint (s.states right).owner worker (r.point right),
        .sendVector (s.states right).owner worker (r.momentum right),
        .sendPoint (s.states common).owner worker (r.point common),
        .sendVector (s.states common).owner worker (r.momentum common),
        .difference worker (r.point right) (r.point common),
        .move worker (r.point left) (r.next + 6) 1,
        .mix worker [(1, r.momentum left), (1, r.momentum right), (-1, r.momentum common)]]
  | .mark source => [.sendPoint (s.states source).owner 0 (r.point source)]
  | .discard _ | .cancel _ => []

noncomputable def registerStep (τ : ℝ) (s : TraceState) (r : Registers) (e : Event) : Registers :=
  let next := r.next + (eventCode τ s r e).length
  match e with
  | .issue _ _ => { r with next, raw := Function.update r.raw s.nextRaw (r.next + 1) }
  | .finish _ =>
      { r with
        next := next
        point := Function.update r.point s.nextState (r.next + 3)
        momentum := Function.update r.momentum s.nextState (r.next + 1)
        mean := Function.update r.mean s.nextDirection r.next
        estimator := Function.update r.estimator s.nextDirection (r.next + 1)
        sharp := Function.update r.sharp s.nextDirection (r.next + 2) }
  | .merge _ _ _ _ =>
      { r with
        next := next
        point := Function.update r.point s.nextState (r.next + 7)
        momentum := Function.update r.momentum s.nextState (r.next + 8) }
  | _ => { r with next }

structure Compilation where
  trace : TraceState := {}
  registers : Registers := {}
  code : List Instruction := []

noncomputable def compileStep (τ : ℝ) (c : Compilation) (e : Event) : Compilation where
  trace := step c.trace e
  registers := registerStep τ c.trace c.registers e
  code := c.code ++ eventCode τ c.trace c.registers e

noncomputable def compile (τ : ℝ) (events : List Event) : Compilation :=
  events.foldl (compileStep τ) {}

noncomputable def program (p : Params) : Program :=
  let c := compile (1 / (20 * p.L)) p.events
  { instructions := c.code
    outputWorker := 0
    outputCount := horizon p - 1
    outputPoint := fun j => c.registers.point (c.trace.markers[j.val]?.getD 0) }

noncomputable def algorithm (p : Params) :=
  LongTails.Setups.BirchNonEuclidean.programAlgorithm (native p) (program p)
    (LongTails.Algorithms.BirchNonEuclideanFramework.chosenLMO (native p))

end LongTails.Algorithms.BirchCollections

namespace LongTails.Algorithms.BirchCollectionBatches

open LongTails.Setups.BirchCollections

def receiveNow (s : TraceState) (collection worker : ℕ) : TraceState :=
  step (step s (.issue collection worker)) (.receive s.nextRaw)

def batchReplies (collection : ℕ) : TraceState → List ℕ → List Event
  | _, [] => []
  | s, worker :: workers =>
      .issue collection worker :: .receive s.nextRaw ::
        batchReplies collection (receiveNow s collection worker) workers

end LongTails.Algorithms.BirchCollectionBatches
