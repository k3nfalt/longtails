import LongTails.Algorithms.LeonTrajectory
import LongTails.Algorithms.LeonAggregate
import Mathlib.Probability.Distributions.Uniform

namespace LongTails.Algorithms.LeonProtocol

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LeonTuning LeonTrajectory LeonExchange

inductive Program (p : Params)
  | finish (x : Point p)
  | sample (q : ComputeQuery p) (next : ComputeReply p → Program p)
  | send (i : Fin p.n) (bits : List Bool) (next : Program p)
  | receive (i : Fin p.n) (next : List Bool → Program p)

def post {p : Params} (packets : Fin p.n → List Bool) (next : Program p) :
    List (Fin p.n) → Program p
  | [] => next
  | i :: rest => .send i (packets i) (post packets next rest)

def collect {p : Params} (next : (Fin p.n → List Bool) → Program p) :
    List (Fin p.n) → (Fin p.n → List Bool) → Program p
  | [], data => next data
  | i :: rest, data => .receive i (fun bits => collect next rest (Function.update data i bits))

def exchange {p : Params} (packets : Fin p.n → List Bool)
    (next : (Fin p.n → List Bool) → Program p) : Program p :=
  post packets (collect next (List.finRange p.n) (fun _ => [])) (List.finRange p.n)

noncomputable def schedule (p : Params) (worker : Fin p.n) (a b : ℕ) :
    List ℕ → Model p → Program p
  | [], model => .finish (LeonTrajectory.output p model a b)
  | l :: rest, model =>
    .sample (model.point, batch p worker l) fun values =>
      let z := LeonAggregate.localCodes (spacing p) (model.anchors (l + 1)) (mean p values)
      exchange (fun i => scatter p l i z) fun chunks =>
        exchange (fun _ => gather p l chunks) fun blocks =>
          schedule p worker a b rest (advance p model l (unpack p l blocks))

structure State (p : Params) where
  program : Program p
  inbox : Fin p.n → List (List Bool)
  busy : Bool

def update (p : Params) (s : State p) (event : Event (ComputeReply p) (CommReply p)) : State p :=
  match event with
  | .computed values =>
    match s.program with
    | .sample _ next => { s with program := next values, busy := false }
    | _ => s
  | .received (source, bits) =>
    { s with inbox := Function.update s.inbox source (s.inbox source ++ [bits]) }
  | .wake => s

def query (p : Params) (s : State p) :
    Action (ComputeQuery p) p.n × State p :=
  match s.program with
  | .finish _ => (.advance 1, s)
  | .send i bits next => (.communicate (i, bits), { s with program := next })
  | .sample q _ =>
    if s.busy then (.advance 1, s) else (.compute q, { s with busy := true })
  | .receive i next =>
    match s.inbox i with
    | [] => (.advance 1, s)
    | bits :: rest =>
      (.advance 0, { s with program := next bits, inbox := Function.update s.inbox i rest })

noncomputable def algorithm (p : Params) (deadline : Time) :
    Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) p.n where
  clock _ := 0
  timer t := if t = 0 then 0 else deadline + 1
  Seed := Fin (iterations p) × Fin (iterations p)
  law := by
    letI : NeZero (iterations p) := ⟨by unfold iterations; positivity⟩
    exact ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩
  State := State p
  root := ⟨0, p.n.pos⟩
  initial i ab := ⟨schedule p i ab.1 ab.2 (LeonCalendar.levels (height p)) (initial p),
    fun _ => [], false⟩
  query _ s _ := query p s
  update _ s _ e := update p s e
  output s :=
    match s.program with
    | .finish x => x
    | _ => p.x0

end LongTails.Algorithms.LeonProtocol
