import LongTails.Algorithms.BirchNonEuclideanFamilies
import LongTails.Setups.BirchNonEuclideanComposition

namespace LongTails.Algorithms.BirchCausalPackets

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies

export LongTails.Setups.BirchNonEuclideanComposition (PacketExpr)

abbrev PacketCode := ℕ → ℕ → ℕ → StateM CodeState (ℕ × ℕ)

noncomputable def atom (H round index : ℕ) : PacketCode := fun worker x m => do
  let q ← emit (.query worker x)
  let α := Coefficient.momentum (round * H + index)
  let v ← emit (.mix worker [(α, q), (.add (.constant 1) (.neg α), m)])
  let d ← emit (.sharp worker v)
  let y ← emit (.move worker x d (.mul (.constant (1 / (H : ℝ))) (.step round)))
  return (y, v)

noncomputable def sequence (left right : PacketCode) : PacketCode := fun worker x m => do
  let first ← left worker x m
  right worker first.1 first.2

noncomputable def join (worker x m : ℕ) (left right : ℕ × ℕ) :
    StateM CodeState (ℕ × ℕ) := do
  let dl ← emit (.difference worker left.1 x)
  let dr ← emit (.difference worker right.1 x)
  let d ← emit (.mix worker [(.constant 1, dl), (.constant 1, dr)])
  let y ← emit (.move worker x d (.constant 1))
  let v ← emit (.mix worker
    [(.constant 1, left.2), (.constant 1, right.2), (.constant (-1), m)])
  return (y, v)

def sendState (sender receiver x m : ℕ) : StateM CodeState Unit := do
  let _ ← emit (.sendPoint sender receiver x)
  let _ ← emit (.sendVector sender receiver m)
  return ()

noncomputable def fork (leftWorker rightWorker : ℕ) (left right : PacketCode) : PacketCode :=
  fun worker x m => do
    sendState worker leftWorker x m
    let l ← left leftWorker x m
    sendState leftWorker worker l.1 l.2
    sendState worker rightWorker x m
    let r ← right rightWorker x m
    sendState rightWorker worker r.1 r.2
    join worker x m l r

def sequenceHistories (left right : List (Finset ℕ)) : List (Finset ℕ) :=
  left ++ right.map (fun s => Finset.range left.length ∪ s.image (left.length + ·))

def forkHistories (left right : List (Finset ℕ)) : List (Finset ℕ) :=
  left ++ right.map (fun s => s.image (left.length + ·))

def atomHistories : List (Finset ℕ) := [∅]

noncomputable def nestedPacket (H round leftWorker rightWorker : ℕ) : PacketCode :=
  sequence (atom H round 0)
    (sequence
      (fork leftWorker rightWorker
        (sequence (atom H round 1) (atom H round 2))
        (sequence (atom H round 3) (atom H round 4)))
      (atom H round 5))

def nestedHistories : List (Finset ℕ) :=
  sequenceHistories atomHistories
    (sequenceHistories
      (forkHistories (sequenceHistories atomHistories atomHistories)
        (sequenceHistories atomHistories atomHistories))
      atomHistories)


inductive GraphNode where
  | query (worker source : ℕ)
  | merge (worker left right common : ℕ)
  deriving DecidableEq

def GraphNode.worker : GraphNode → ℕ
  | .query worker _ | .merge worker _ _ _ => worker

def GraphNode.calls : GraphNode → ℕ
  | .query _ _ => 1
  | .merge _ _ _ _ => 0

structure OwnedState where
  worker : ℕ
  point : ℕ
  momentum : ℕ

structure GraphState where
  states : ℕ → OwnedState
  next : ℕ
  atoms : ℕ

noncomputable def graphNodeCode (H round : ℕ) (node : GraphNode)
    (state : GraphState) : StateM CodeState OwnedState :=
  match node with
    | .query worker source => do
      let root := state.states source
      sendState root.worker worker root.point root.momentum
      let result ← atom H round state.atoms worker root.point root.momentum
      pure (OwnedState.mk worker result.1 result.2)
    | .merge worker left right common => do
      let l := state.states left
      let r := state.states right
      let base := state.states common
      sendState l.worker worker l.point l.momentum
      sendState r.worker worker r.point r.momentum
      sendState base.worker worker base.point base.momentum
      let result ← join worker base.point base.momentum
        (l.point, l.momentum) (r.point, r.momentum)
      pure (OwnedState.mk worker result.1 result.2)

noncomputable def graphStep (H round : ℕ) (node : GraphNode)
    (state : GraphState) : StateM CodeState GraphState := do
  let result ← graphNodeCode H round node state
  return {
    states := Function.update state.states state.next result
    next := state.next + 1
    atoms := state.atoms + match node with | .query _ _ => 1 | .merge _ _ _ _ => 0 }

noncomputable def graphCode (H round : ℕ) (nodes : List GraphNode)
    (output : ℕ) : PacketCode := fun coordinator x m => do
  let mut state : GraphState := ⟨fun _ => ⟨coordinator, x, m⟩, 1, 0⟩
  for node in nodes do
    state ← graphStep H round node state
  let result := state.states output
  sendState result.worker coordinator result.point result.momentum
  return (result.point, result.momentum)

structure HistoryState where
  states : ℕ → Finset ℕ := fun _ => ∅
  queryHistory : ℕ → Finset ℕ := fun _ => ∅
  next : ℕ := 1
  atoms : ℕ := 0

def historyStep (node : GraphNode) (state : HistoryState) : HistoryState :=
  match node with
  | .query _ source => {
      states := Function.update state.states state.next (insert state.atoms (state.states source))
      queryHistory := Function.update state.queryHistory state.atoms (state.states source)
      next := state.next + 1
      atoms := state.atoms + 1 }
  | .merge _ left right _ => { state with
      states := Function.update state.states state.next (state.states left ∪ state.states right)
      next := state.next + 1 }

def GraphNode.Valid (workers : ℕ) (state : HistoryState) : GraphNode → Prop
  | .query worker source => worker < workers ∧ source < state.next
  | .merge worker left right common => worker < workers ∧ left < state.next ∧ right < state.next ∧
      common < state.next ∧ state.states common = state.states left ∩ state.states right

def GraphValidFrom (workers : ℕ) : HistoryState → List GraphNode → Prop
  | _, [] => True
  | state, node :: rest => node.Valid workers state ∧
      GraphValidFrom workers (historyStep node state) rest

def graphHistory (nodes : List GraphNode) : HistoryState := nodes.foldl (flip historyStep) {}

def localAsyncNodes (leftWorker rightWorker : ℕ) : List GraphNode :=
  [.query leftWorker 0, .query rightWorker 0, .merge leftWorker 1 2 0,
    .query leftWorker 3, .query rightWorker 2, .merge leftWorker 4 5 2]

def nestedHybridNodes (outer left innerA innerFirst innerSecond innerB right : ℕ) : List GraphNode :=
  [.query outer 0, .query left 1, .query innerFirst 2, .query innerSecond 2,
    .merge innerA 3 4 2, .query innerFirst 3, .merge innerA 5 6 3,
    .query innerB 2, .merge left 7 8 2, .query right 1, .query right 10,
    .merge outer 9 11 1]

structure GraphValues (E : Type*) where
  points : ℕ → E
  momenta : ℕ → E
  queryMomenta : ℕ → E
  queryPoints : ℕ → E
  next : ℕ
  atoms : ℕ

def valueStep {E : Type*} [AddCommGroup E] [Module ℝ E]
    (α γ : ℝ) (raw direction : ℕ → E) (node : GraphNode) (state : GraphValues E) : GraphValues E :=
  match node with
  | .query _ source => {
      points := Function.update state.points state.next
        (state.points source + γ • direction state.atoms)
      momenta := Function.update state.momenta state.next
        (α • raw state.atoms + (1 - α) • state.momenta source)
      queryMomenta := Function.update state.queryMomenta state.atoms (state.momenta source)
      queryPoints := Function.update state.queryPoints state.atoms (state.points source)
      next := state.next + 1
      atoms := state.atoms + 1 }
  | .merge _ left right common => { state with
      points := Function.update state.points state.next
        (state.points left + state.points right - state.points common)
      momenta := Function.update state.momenta state.next
        (state.momenta left + state.momenta right - state.momenta common)
      next := state.next + 1 }

def initialValues {E : Type*} [Zero E] (point momentum : E) : GraphValues E where
  points := fun _ => point
  momenta := fun _ => momentum
  queryMomenta := fun _ => 0
  queryPoints := fun _ => 0
  next := 1
  atoms := 0

noncomputable def graphRun (H round : ℕ) (nodes : List GraphNode) (state : GraphState) :
    StateM CodeState GraphState :=
  forIn nodes state (fun node state => ForInStep.yield <$> graphStep H round node state)

noncomputable def sendPoints (state : GraphState) (main : ℕ → ℕ) :
    List ℕ → StateM CodeState Unit
  | [] => pure ()
  | k :: rest => do
      let point := state.states (main k)
      let _ ← emit (.sendPoint point.worker 0 point.point)
      sendPoints state main rest

noncomputable def sendMainPoints (K : ℕ) (state : GraphState) (main : ℕ → ℕ) :
    StateM CodeState Unit := sendPoints state main (List.range (K + 1))

noncomputable def graphProgramCode (H K B : ℕ) (nodes : List GraphNode)
    (main : ℕ → ℕ) : StateM CodeState (ℕ → ℕ) := do
  let momentum ← localBatch 0 0 B
  let state ← graphRun H 0 nodes ⟨fun _ => ⟨0, 0, momentum⟩, 1, 0⟩
  sendMainPoints K state main
  return fun k => (state.states (main k)).point

noncomputable def graphProgramTemplate (H K B : ℕ) (nodes : List GraphNode)
    (main : ℕ → ℕ) : ProgramTemplate :=
  makeTemplate K (graphProgramCode H K B nodes main)

structure GraphBlock where
  nodes : List GraphNode
  output : ℕ
  next : ℕ

end LongTails.Algorithms.BirchCausalPackets

namespace LongTails.Setups.BirchNonEuclideanComposition.PacketExpr

open LongTails.Algorithms.BirchCausalPackets

def compile : PacketExpr → ℕ → ℕ → GraphBlock
  | .atom worker, root, next => ⟨[.query worker root], next, next + 1⟩
  | .sequence left right, root, next =>
      let l := left.compile root next
      let r := right.compile l.output l.next
      ⟨l.nodes ++ r.nodes, r.output, r.next⟩
  | .fork owner left right, root, next =>
      let l := left.compile root next
      let r := right.compile root l.next
      ⟨l.nodes ++ r.nodes ++ [.merge owner l.output r.output root], r.next, r.next + 1⟩
  | .overlap owner left right afterBoth afterRight, root, next =>
      let l := left.compile root next
      let r := right.compile root l.next
      let a := afterBoth.compile r.next (r.next + 1)
      let b := afterRight.compile r.output a.next
      ⟨l.nodes ++ r.nodes ++ [.merge owner l.output r.output root] ++ a.nodes ++ b.nodes ++
        [.merge owner a.output b.output r.output], b.next, b.next + 1⟩

def joins : PacketExpr → ℕ
  | .atom _ => 0
  | .sequence left right => left.joins + right.joins
  | .fork _ left right => left.joins + right.joins + 1
  | .overlap _ left right afterBoth afterRight =>
      left.joins + right.joins + afterBoth.joins + afterRight.joins + 2

end LongTails.Setups.BirchNonEuclideanComposition.PacketExpr

namespace LongTails.Algorithms.BirchCausalPackets

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies

namespace PacketExpr

export LongTails.Setups.BirchNonEuclideanComposition.PacketExpr (atom sequence fork overlap calls Valid compile joins)

end PacketExpr

def nestedComb (queryWorker mergeWorker : ℕ → ℕ) : ℕ → PacketExpr
  | 0 => .atom (queryWorker 0)
  | depth + 1 => .overlap (mergeWorker depth) (nestedComb queryWorker mergeWorker depth)
      (.atom (queryWorker (3 * depth + 1))) (.atom (queryWorker (3 * depth + 2)))
      (.atom (queryWorker (3 * depth + 3)))

def nestedBalanced (queryWorker mergeWorker : ℕ → ℕ) : ℕ → PacketExpr
  | 0 => .atom (queryWorker 0)
  | depth + 1 =>
      let child := nestedBalanced queryWorker mergeWorker depth
      .overlap (mergeWorker depth) child child child child

structure GraphPlan where
  nodes : List GraphNode := []
  main : ℕ → ℕ := fun _ => 0
  next : ℕ := 1

def planStep (packet : ℕ → PacketExpr) (source : ℕ → ℕ) (k : ℕ) (plan : GraphPlan) : GraphPlan :=
  let root := plan.main (source k)
  let block := (packet k).compile root plan.next
  { nodes := plan.nodes ++ block.nodes ++ [.merge 0 (plan.main k) block.output root]
    main := Function.update plan.main (k + 1) block.next
    next := block.next + 1 }

def planRun (packet : ℕ → PacketExpr) (source : ℕ → ℕ) : ℕ → GraphPlan
  | 0 => {}
  | K + 1 => planStep packet source K (planRun packet source K)

noncomputable def planTemplate (H K B : ℕ) (packet : ℕ → PacketExpr) (source : ℕ → ℕ) :
    ProgramTemplate :=
  let plan := planRun packet source K
  graphProgramTemplate H K B plan.nodes plan.main

end LongTails.Algorithms.BirchCausalPackets
