import LongTails.Algorithms.BirchNonEuclideanFamilies

namespace LongTails.Algorithms.BirchNonEuclideanRennala

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies

inductive Event (m : ℕ) where
  | query (worker : Fin m)
  | reply (worker : Fin m)
  deriving DecidableEq

abbrev Label (m : ℕ) := Fin m × ℕ

structure State (m : ℕ) where
  round : ℕ := 0
  batch : ℕ := 0
  source : Fin m → ℕ := fun _ => 0
  serial : Fin m → ℕ := fun _ => 0
  live : Finset (Fin m) := Finset.univ
  ready : Finset (Fin m) := ∅
  queries : List (Label m) := []
  accepted : List (Label m) := []
  stale : List (Label m) := []
  drained : List (Label m) := []

def Event.Enabled {m : ℕ} (s : State m) : Event m → Prop
  | .query w => w ∈ s.live ∧ w ∉ s.ready
  | .reply w => w ∈ s.live ∧ w ∈ s.ready

def fresh {m : ℕ} (s : State m) (w : Fin m) : Prop := s.source w = s.round

def commits {m : ℕ} (B : ℕ) (s : State m) (w : Fin m) : Prop := fresh s w ∧ s.batch + 1 = B

instance {m : ℕ} (s : State m) (w : Fin m) : Decidable (fresh s w) := inferInstanceAs (Decidable (_ = _))
instance {m : ℕ} (B : ℕ) (s : State m) (w : Fin m) : Decidable (commits B s w) :=
  inferInstanceAs (Decidable (_ ∧ _))

def step {m : ℕ} (K B : ℕ) (s : State m) : Event m → State m
  | .query w => { s with ready := insert w s.ready, queries := s.queries ++ [(w, s.serial w)] }
  | .reply w =>
      if s.round < K then
        let a := s.round + if commits B s w then 1 else 0
        { s with
          round := a
          batch := if fresh s w then if commits B s w then 0 else s.batch + 1 else s.batch
          source := Function.update s.source w a
          serial := Function.update s.serial w (s.serial w + 1)
          live := if a < K then s.live else s.live.erase w
          ready := s.ready.erase w
          accepted := if fresh s w then s.accepted ++ [(w, s.serial w)] else s.accepted
          stale := if fresh s w then s.stale else s.stale ++ [(w, s.serial w)] }
      else
        { s with
          serial := Function.update s.serial w (s.serial w + 1)
          live := s.live.erase w
          ready := s.ready.erase w
          drained := s.drained ++ [(w, s.serial w)] }

def run {m : ℕ} (K B : ℕ) (events : List (Event m)) : State m := events.foldl (step K B) {}

def LegalFrom {m : ℕ} (K B : ℕ) : State m → List (Event m) → Prop
  | _, [] => True
  | s, e :: events => e.Enabled s ∧ LegalFrom K B (step K B s e) events

def CompleteTrace {m : ℕ} (K B : ℕ) (events : List (Event m)) : Prop :=
  LegalFrom K B {} events ∧ (run K B events).round = K ∧ (run K B events).live = ∅

structure Registers (m : ℕ) where
  points : ℕ → ℕ := fun _ => 0
  sharps : ℕ → ℕ := fun _ => 0
  owner : ℕ → ℕ := fun _ => 0
  point : Fin m → ℕ := fun _ => 0
  reply : Fin m → ℕ := fun _ => 0
  terms : List (Coefficient × ℕ) := []

noncomputable def commitCode {m : ℕ} (k : ℕ) (terms : List (Coefficient × ℕ)) (regs : Registers m) :
    StateM CodeState (Registers m) := do
  let mean ← emit (.mix 0 terms)
  let d ← emit (.sharp 0 mean)
  let x ← emit (.move 0 (regs.points k) d (.step k))
  return { regs with
    points := Function.update regs.points (k + 1) x
    sharps := Function.update regs.sharps k d
    owner := Function.update regs.owner d k
    terms := [] }

noncomputable def relaunchCode {m : ℕ} (w : Fin m) (k : ℕ) (regs : Registers m) :
    StateM CodeState (Registers m) := do
  let _ ← emit (.sendPoint 0 (w.val + 1) (regs.points k))
  return { regs with point := Function.update regs.point w (regs.points k) }

noncomputable def replyCode {m : ℕ} (K B : ℕ) (w : Fin m) (s : State m) (regs : Registers m) :
    StateM CodeState (Registers m) := do
  let _ ← emit (.sendVector (w.val + 1) 0 (regs.reply w))
  let mut out := regs
  if s.round < K then
    if fresh s w then
      let terms := regs.terms ++ [(.constant (1 / (B : ℝ)), regs.reply w)]
      if commits B s w then
        out ← commitCode s.round terms out
      else
        out := { out with terms := terms }
    let a := (step K B s (.reply w)).round
    if a < K then
      out ← relaunchCode w a out
  return out

noncomputable def eventCode {m : ℕ} (K B : ℕ) (e : Event m) (s : State m × Registers m) :
    StateM CodeState (State m × Registers m) := do
  let next := step K B s.1 e
  match e with
  | .query w =>
      let q ← emit (.query (w.val + 1) (s.2.point w))
      return (next, { s.2 with reply := Function.update s.2.reply w q })
  | .reply w =>
      let regs ← replyCode K B w s.1 s.2
      return (next, regs)

noncomputable def launchCode (w : ℕ) : StateM CodeState Unit := do
  let _ ← emit (.sendPoint 0 w 0)
  return ()

noncomputable def initialCode (m : ℕ) : StateM CodeState (Registers m) := do
  for w in List.finRange m do
    launchCode (w.val + 1)
  return {}

noncomputable def eventsStateCode {m : ℕ} (K B : ℕ) (events : List (Event m)) :
    StateM CodeState (State m × Registers m) := do
  let regs ← initialCode m
  let mut state : State m × Registers m := ({}, regs)
  for e in events do
    state ← eventCode K B e state
  return state

noncomputable def eventsCode {m : ℕ} (K B : ℕ) (events : List (Event m)) : StateM CodeState (ℕ → ℕ) := do
  let state ← eventsStateCode K B events
  return state.2.points

noncomputable def eventsProgram {m : ℕ} (K B : ℕ) (events : List (Event m)) (t : Tuning) : Program :=
  (makeTemplate K (eventsCode K B events)).instantiate t

end LongTails.Algorithms.BirchNonEuclideanRennala
