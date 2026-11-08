import LongTails.Algorithms.BirchNonEuclideanPhysical

namespace LongTails.Algorithms.BirchNonEuclideanEvents

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical

inductive Event (m : ℕ) where
  | query (worker : Fin m)
  | complete (worker : Fin m)
  deriving DecidableEq

abbrev QueryLabel (m : ℕ) := Sum ℕ (Fin m × ℕ × ℕ)

structure EventState (m : ℕ) where
  schedule : PacketSchedule m := {}
  cursor : ℕ := 0
  progress : Fin m → ℕ := fun _ => 0
  live : Finset (Fin m) := Finset.univ
  queries : List (QueryLabel m) := []
  drained : List (Packet m) := []

def Event.Enabled {m : ℕ} (H K : ℕ) (word : ℕ → Fin m) (s : EventState m) : Event m → Prop
  | .query w => w ∈ s.live ∧ s.progress w < H
  | .complete w => w ∈ s.live ∧ s.progress w = H ∧
      (s.schedule.accepted.length < K → w = word s.cursor)

def eventStep {m : ℕ} (K R : ℕ) (s : EventState m) : Event m → EventState m
  | .query w => { s with
      progress := Function.update s.progress w (s.progress w + 1)
      queries := s.queries ++ [Sum.inr (w, s.schedule.serial w, s.progress w)] }
  | .complete w =>
      if s.schedule.accepted.length < K then
        let next := scheduleStep K R w s.schedule
        { s with
          schedule := next
          cursor := s.cursor + 1
          progress := if next.accepted.length < K then Function.update s.progress w 0 else s.progress
          live := if next.accepted.length < K then s.live else s.live.erase w }
      else
        { s with
          live := s.live.erase w
          drained := s.drained ++ [⟨w, s.schedule.source w, s.schedule.serial w⟩] }

def eventRun {m : ℕ} (K R : ℕ) (events : List (Event m)) : EventState m :=
  events.foldl (eventStep K R) {}

def queryLabels {m : ℕ} (H K B : ℕ) (events : List (Event m)) : List (QueryLabel m) :=
  (List.range B).map Sum.inl ++ (eventRun K (packetCutoff H B) events).queries

def packetLabels {m : ℕ} (H : ℕ) (job : Packet m) : List (QueryLabel m) :=
  (List.range H).map (fun h => Sum.inr (job.worker, job.serial, h))

def normalLabels {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) : List (QueryLabel m) :=
  let s := finalSchedule H K B word
  (List.range B).map Sum.inl ++ (s.accepted ++ ignored s).flatMap (packetLabels H)

def LegalFrom {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m) : EventState m → List (Event m) → Prop
  | _, [] => True
  | s, e :: rest => e.Enabled H K word s ∧ LegalFrom H K R word (eventStep K R s e) rest

def CompleteTrace {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (events : List (Event m)) : Prop :=
  LegalFrom H K (packetCutoff H B) word {} events ∧
    (eventRun K (packetCutoff H B) events).schedule.accepted.length = K ∧
      (eventRun K (packetCutoff H B) events).live = ∅

structure Registers (m : ℕ) where
  points : ℕ → ℕ
  momenta : ℕ → ℕ
  launchPoint : Fin m → ℕ
  launchMomentum : Fin m → ℕ
  point : Fin m → ℕ
  momentum : Fin m → ℕ

noncomputable def privateStep (w x v H h : ℕ) : StateM CodeState (ℕ × ℕ) := do
  let q ← emit (.query w x)
  let α := Coefficient.momentum h
  let v' ← emit (.mix w [(α, q), (.add (.constant 1) (.neg α), v)])
  let d ← emit (.sharp w v')
  let x' ← emit (.move w x d (.mul (.constant (1 / (H : ℝ))) (.step 0)))
  return (x', v')

noncomputable def returnCode (w launchPoint launchMomentum point momentum : ℕ) :
    StateM CodeState (ℕ × ℕ) := do
  let dx ← emit (.difference w point launchPoint)
  let dm ← emit (.mix w [(.constant 1, momentum), (.constant (-1), launchMomentum)])
  let _ ← emit (.sendVector w 0 dx)
  let _ ← emit (.sendVector w 0 dm)
  return (dx, dm)

noncomputable def commitCode {m : ℕ} (k dx dm : ℕ) (regs : Registers m) :
    StateM CodeState (Registers m) := do
  let x ← emit (.move 0 (regs.points k) dx (.constant 1))
  let v ← emit (.mix 0 [(.constant 1, regs.momenta k), (.constant 1, dm)])
  return { regs with
    points := Function.update regs.points (k + 1) x
    momenta := Function.update regs.momenta (k + 1) v }

noncomputable def relaunchCode {m : ℕ} (w : Fin m) (k : ℕ) (regs : Registers m) :
    StateM CodeState (Registers m) := do
  let x := regs.points k
  let v := regs.momenta k
  let _ ← emit (.sendPoint 0 (w.val + 1) x)
  let _ ← emit (.sendVector 0 (w.val + 1) v)
  return { regs with
    launchPoint := Function.update regs.launchPoint w x
    launchMomentum := Function.update regs.launchMomentum w v
    point := Function.update regs.point w x
    momentum := Function.update regs.momentum w v }

noncomputable def eventCode {m : ℕ} (H K R : ℕ) (e : Event m)
    (s : EventState m × Registers m) : StateM CodeState (EventState m × Registers m) := do
  let publicState := s.1
  let regs := s.2
  let next := eventStep K R publicState e
  match e with
  | .query w =>
      let pair ← privateStep (w.val + 1) (regs.point w) (regs.momentum w) H (publicState.progress w)
      return (next, { regs with
        point := Function.update regs.point w pair.1
        momentum := Function.update regs.momentum w pair.2 })
  | .complete w =>
      let packet ← returnCode (w.val + 1) (regs.launchPoint w) (regs.launchMomentum w)
        (regs.point w) (regs.momentum w)
      let mut regs := regs
      if publicState.schedule.accepted.length < K then
        let k := publicState.schedule.accepted.length
        if k - publicState.schedule.source w ≤ R then
          regs ← commitCode k packet.1 packet.2 regs
        if next.schedule.accepted.length < K then
          regs ← relaunchCode w next.schedule.accepted.length regs
      return (next, regs)

noncomputable def launchCode (w point momentum : ℕ) : StateM CodeState Unit := do
  let _ ← emit (.sendPoint 0 w point)
  let _ ← emit (.sendVector 0 w momentum)
  return ()

noncomputable def initialCode (m B : ℕ) : StateM CodeState (Registers m) := do
  let initial ← localBatch 0 0 B
  for w in List.finRange m do
    launchCode (w.val + 1) 0 initial
  return {
    points := fun _ => 0
    momenta := fun _ => initial
    launchPoint := fun _ => 0
    launchMomentum := fun _ => initial
    point := fun _ => 0
    momentum := fun _ => initial }

noncomputable def eventsStateCode {m : ℕ} (H K B : ℕ) (events : List (Event m)) :
    StateM CodeState (EventState m × Registers m) := do
  let regs ← initialCode m B
  let mut state : EventState m × Registers m := ({}, regs)
  for e in events do
    state ← eventCode H K (packetCutoff H B) e state
  return state

noncomputable def eventsCode {m : ℕ} (H K B : ℕ) (events : List (Event m)) :
    StateM CodeState (ℕ → ℕ) := do
  let state ← eventsStateCode H K B events
  return state.2.points

noncomputable def eventsProgram {m : ℕ} (H K B : ℕ) (events : List (Event m)) (t : Tuning) : Program :=
  (makeTemplate K (eventsCode H K B events)).instantiate t

end LongTails.Algorithms.BirchNonEuclideanEvents
