import LongTails.Algorithms.MultirateTrajectory
import Mathlib.Probability.Distributions.Uniform

namespace LongTails.Algorithms.MultirateProtocol

open DistributedTemplate
open LongTails.Setups.MultirateSmoothNonconvex
open MultirateCalendar MultirateAllocation MultirateTrajectory

inductive Program (p : Params)
  | done (x : Point p)
  | post (i : Fin p.n) (bits : List Bool) (next : Program p)
  | collect (i : Fin p.n) (next : List Bool → Program p)

def sendAll {p : Params} (bits : List Bool) (next : Program p) : List (Fin p.n) → Program p
  | [] => next
  | i :: rest => .post i bits (sendAll bits next rest)

noncomputable def collectAll {p : Params} (next : (Fin p.n → Code p) → Program p) :
    List (Fin p.n) → (Fin p.n → Code p) → Program p
  | [], cache => next cache
  | i :: rest, cache => .collect i fun bits => collectAll next rest (Function.update cache i (read p bits))

noncomputable def due (p : Params) (k : ℕ) : List (Fin p.n) :=
  (List.finRange p.n).filter fun i => k % period p i = 0

noncomputable def schedule (p : Params) (a b : ℕ) : List ℕ → Model p → (Fin p.n → Code p) → Program p
  | [], m, _ => .done (output p m a b)
  | k :: rest, m, cache =>
    collectAll (fun current =>
      sendAll (queryPacket p (m.points k))
        (schedule p a b rest (advance p m k (∑ i, current i)) current)
        ((due p k).filter fun i => k + period p i < steps p)) (due p k) cache

noncomputable def start (p : Params) (a b : ℕ) : Program p :=
  sendAll (queryPacket p p.x0) (schedule p a b (List.range (steps p)) (MultirateTrajectory.initial p)
    (fun _ => 0)) (List.finRange p.n)

inductive Phase (p : Params)
  | idle
  | batch (x : Point p) (used : ℕ) (sum : Point p) (waiting : Bool)

structure State (p : Params) where
  program : Program p
  inbox : Fin p.n → Option (List Bool)
  phase : Phase p
  notified : Bool := false

noncomputable def rootQuery (p : Params) (s : State p) :
    Action (LongTails.Setups.DistributedAggregateSmoothNonconvex.ComputeQuery (aggregate p)) (p.n + 1) × State p :=
  match s.program with
  | .post i bits next => (.communicate (i.succ, bits), {s with program := next})
  | .done _ => (.advance 1, s)
  | .collect i next =>
    match s.inbox i with
    | none => (.advance 1, s)
    | some bits => (.advance 0, {s with program := next bits, inbox := Function.update s.inbox i none})

noncomputable def workerQuery (p : Params) (i : Fin p.n) (s : State p) :
    Action (LongTails.Setups.DistributedAggregateSmoothNonconvex.ComputeQuery (aggregate p)) (p.n + 1) × State p :=
  match s.phase with
  | .idle | .batch _ _ _ true => (.advance 1, s)
  | .batch x j sum false =>
    if j < batch p i then (.compute (.evaluate x), {s with phase := .batch x j sum true})
    else (.communicate (0, replyPacket p ((batch p i : ℝ)⁻¹ • sum)), {s with phase := .idle})

noncomputable def update (p : Params) (v : Fin (p.n + 1)) (s : State p)
    (e : Event (LongTails.Setups.DistributedAggregateSmoothNonconvex.ComputeReply (aggregate p))
      (LongTails.Setups.DistributedAggregateSmoothNonconvex.CommReply (aggregate p))) : State p :=
  match e with
  | .wake => s
  | .computed (.computed _ y) =>
    match s.phase with
    | .idle => s
    | .batch x j sum _ => {s with phase := .batch x (j+1) (sum + y) false}
  | .received (.received source bits) =>
    Fin.cases (Fin.cases s (fun i => {s with inbox := Function.update s.inbox i (some bits)}) source)
      (fun _ => {s with phase := .batch (queryPoint p bits) 0 0 false}) v

noncomputable def algorithm (p : Params) (T : Time) :
    Algorithm (spec.ComputeQuery p) (spec.ComputeReply p) (spec.CommReply p) (Point p) (p.n + 1) where
  clock _ := 0
  timer t := if t = 0 then 0 else T + 1
  Seed := Fin (steps p) × Fin (steps p)
  law := by
    letI : NeZero (steps p) := ⟨(Nat.two_pow_pos _).ne'⟩
    exact ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩
  State := State p
  root := 0
  initial v ab := ⟨if v = 0 then start p ab.1 ab.2 else .done p.x0, fun _ => none, .idle, false⟩
  query v s _ := if s.notified then (.advance 0, {s with notified := false}) else
    Fin.cases (rootQuery p s) (fun i => workerQuery p i s) v
  update v s _ e := match e with
    | .wake => s
    | _ => {update p v s e with notified := true}
  output s := match s.program with | .done x => x | _ => p.x0

end LongTails.Algorithms.MultirateProtocol
