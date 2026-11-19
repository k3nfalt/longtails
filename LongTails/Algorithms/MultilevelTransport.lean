import LongTails.Algorithms.MultilevelWorkerSchedule
import Mathlib.Probability.Distributions.Uniform

namespace LongTails.Algorithms.MultilevelTransport

open DistributedTemplate MeasureTheory
open LongTails.Setups.DistributedMeanSquaredSmooth
open MultilevelWorkerSchedule (wanted)

abbrev Bits := List Bool
abbrev Answers := ℕ → Option Bits
abbrev Selection (p : Params) := Fin (wanted p) × Fin (wanted p)

structure Script (p : Params) where
  count : ℕ
  worker : ℕ → Fin p.n
  start : ℕ → Time
  finish : ℕ → Time
  request : ℕ → (ℕ → Bits) → Bits
  decode : Bits → Query p
  encode : Bits → Query p → Bits
  output : Selection p → (ℕ → Bits) → Point p

def unframe (bs : Bits) : Bits := bs.take (bs.length - clockBits)

structure State (p : Params) where
  seed : Selection p
  next : ℕ := 0
  answers : Answers := fun _ => none
  pending : Fin p.n → Option ℕ := fun _ => none
  input : Bits := []
  action : Option (Action (ComputeQuery p) (p.n + 1)) := none

noncomputable def ready {p : Params} (t : Script p) (s : State p) : Prop :=
  s.next < t.count ∧ s.pending (t.worker s.next) = none ∧
    ∀ j < t.count, t.finish j ≤ t.start s.next → (s.answers j).isSome

noncomputable def visible {p : Params} (t : Script p) (k : ℕ) (a : Answers) (j : ℕ) : Bits :=
  if j < k ∧ t.finish j ≤ t.start k then (a j).getD [] else []

noncomputable def dispatch {p : Params} (t : Script p) (s : State p) :
    Action (ComputeQuery p) (p.n+1) × State p := by
  classical
  exact if ready t s then
    let i := t.worker s.next
    (.communicate (i.succ, t.request s.next (visible t s.next s.answers)),
      {s with next := s.next + 1, pending := Function.update s.pending i (some s.next)})
  else (.advance 0, s)

noncomputable def accept {p : Params} (s : State p) (i : Fin p.n) (bs : Bits) : State p :=
  match s.pending i with
  | none => s
  | some j => {s with answers := Function.update s.answers j (some (unframe bs)),
                      pending := Function.update s.pending i none}

noncomputable def update {p : Params} (t : Script p) (v : Fin (p.n+1)) (s : State p)
    (ev : Event (ComputeReply p) (CommReply p)) : State p :=
  match ev with
  | .wake => s
  | .computed (.computed _ q) => {s with action := some (.communicate (0, t.encode s.input q))}
  | .received (.received source bs) =>
    if v = 0 then Fin.cases s (fun i => accept s i bs) source
    else {s with input := unframe bs, action := some (.compute (.evaluate (t.decode (unframe bs))))}

noncomputable def algorithm (p : Params) (t : Script p) (T : Time) :
    Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) (p.n+1) where
  clock _ := 0
  timer _ := T + 1
  Seed := Selection p
  law := by
    letI : NeZero (wanted p) := ⟨by unfold wanted; omega⟩
    exact ⟨(PMF.uniformOfFintype (Selection p)).toMeasure, inferInstance⟩
  State := State p
  root := 0
  initial _ seed := {seed}
  query v s _ :=
    if v = 0 then dispatch t s
    else (s.action.getD (.advance 0), {s with action := none})
  update v s _ := update t v s
  output s := t.output s.seed (fun j => (s.answers j).getD [])

def ordinal {p : Params} (t : Script p) (k : ℕ) :=
  ((Finset.range k).filter fun j => t.worker j = t.worker k).card

noncomputable def reply {p : Params} (t : Script p) (g : Fin p.n → Point p → p.Ω → Point p)
    (xs : Samples p) (k : ℕ) : Bits :=
  let bs := t.request k (fun j => if _h : j < k ∧ t.finish j ≤ t.start k then reply t g xs j else [])
  let i := t.worker k
  let q := t.decode bs
  let sample := xs i (ordinal t k)
  t.encode bs (g i q.1 sample, g i q.2 sample)
termination_by k

end LongTails.Algorithms.MultilevelTransport
