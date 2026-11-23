import LongTails.Algorithms.LeonProtocol
import LongTails.Algorithms.RobustGradientEstimator
import LongTails.Setups.DistributedContaminatedSmoothNonconvex

namespace LongTails.Algorithms.ContaminatedParallelDescent

open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open OracleTemplate.RobustGradient
open DistributedTemplate

noncomputable def confidence (p : Params) : ℕ := 4 + ⌈Real.log (1 / p.failure)⌉₊

noncomputable def levelConfidence (p : Params) (l : ℕ) : ℕ :=
  8 * (1 + l) + 2 * ⌈(confidence p : ℝ) * min 1 ((16 : ℝ) ^ l / LeonTuning.iterations (network p))⌉₊

def pilotCount (p : Params) (q : ℕ) : ℕ := 8 * (1 + Nat.log2 p.n + q)

noncomputable def freshCount (p : Params) (q : ℕ) (i : Fin p.n) : ℕ :=
  max 1 (16777216 * q * (1 + ⌈(∑ j, (p.h j : ℝ) * p.σ j ^ 2) /
    ((p.n : ℝ) ^ 2 * LeonTuning.resolution (network p) ^ 2 * (p.h i : ℝ))⌉₊))

noncomputable def batch (p : Params) (q : ℕ) (i : Fin p.n) : ℕ+ :=
  ⟨pilotCount p q + freshCount p q i, by unfold pilotCount; omega⟩

noncomputable def clipRadius (σ η cap : ℝ) : ℝ :=
  if 0 < η then min (8 * σ / Real.sqrt η) cap else cap

noncomputable def radius (p : Params) (q : ℕ) (i : Fin p.n) : ℝ :=
  clipRadius (p.σ i) (p.η i)
    ((p.n : ℝ) * LeonTuning.resolution (network p) * freshCount p q i / (2048 * q))

noncomputable def estimate (p : Params) (q : ℕ) (i : Fin p.n)
    (values : List (Point p)) : Point p :=
  let k := pilotCount p q
  let m := freshCount p q i
  let c := pilotCenter (24 * p.σ i) (fun j : Fin k => (values[j.val]?).getD 0)
  (m : ℝ)⁻¹ • ∑ j : Fin m, centeredClip (radius p q i) c ((values[k + j.val]?).getD 0)

noncomputable def aggregate (p : Params) (i : Fin p.n) (x anchor : Point p) (l q : ℕ)
    (next : Point p → LeonProtocol.Program (network p)) : LeonProtocol.Program (network p) :=
  let net := network p
  .sample (x, batch p q i) fun values =>
    let z := LeonAggregate.localCodes (LeonTuning.spacing net) anchor (estimate p q i values)
    LeonProtocol.exchange (fun j => LeonExchange.scatter net l j z) fun chunks =>
      LeonProtocol.exchange (fun _ => LeonExchange.gather net l chunks) fun blocks =>
        next (LeonAggregate.decode p.n (LeonTuning.width net l) (LeonTuning.spacing net)
          (LeonTuning.radius net l) anchor (LeonExchange.unpack net l blocks))

inductive Operation
  | train (level : ℕ)
  | validate (index level : ℕ)

def Operation.level : Operation → ℕ
  | .train l | .validate _ l => l

noncomputable def Operation.precision (p : Params) : Operation → ℕ
  | .train l => levelConfidence p l
  | .validate _ _ => 2 * confidence p

noncomputable def candidateIndices (p : Params)
    (seed : Fin (confidence p) → Fin (LeonTuning.iterations (network p))) :
    List (Fin (LeonTuning.iterations (network p))) :=
  (if LeonTuning.iterations (network p) ≤ confidence p then Finset.univ
    else Finset.univ.image seed).sort (· ≤ ·)

def validationOps {N : ℕ} (height : ℕ) : Option ℕ → List (Fin N) → List Operation
  | _, [] => []
  | prior, j :: js =>
    let l := prior.elim height (fun k => Nat.clog 4 (1 + (j.val - k)))
    .validate j.val l :: validationOps height (some j.val) js

noncomputable def operations (p : Params) (seed : Fin (confidence p) → Fin (LeonTuning.iterations (network p))) :
    List Operation :=
  let height := LeonTuning.height (network p)
  (LeonCalendar.levels height).map Operation.train ++ validationOps height none (candidateIndices p seed)

structure Model (p : Params) where
  training : LeonTrajectory.Model (network p)
  anchor : Point p
  best : Point p × ℝ

noncomputable def initialModel (p : Params) : Model p := ⟨LeonTrajectory.initial (network p), 0, (p.x0,-1)⟩

def location (p : Params) (m : Model p) : Operation → Point p
  | .train _ => m.training.point
  | .validate j _ => (m.training.history[j]?.getD (p.x0, 0)).1

def reference (p : Params) (m : Model p) : Operation → Point p
  | .train l => m.training.anchors (l + 1)
  | .validate _ _ => m.anchor

noncomputable def advance (p : Params) (m : Model p) (op : Operation) (v : Point p) : Model p :=
  match op with
  | .train l => {m with training := LeonTrajectory.applyEstimate (network p) m.training l v}
  | .validate _ _ =>
    let candidate := (location p m op, ‖v‖)
    let best := if 0 ≤ m.best.2 ∧ m.best.2 ≤ ‖v‖ then m.best else candidate
    {m with anchor := v, best := best}

def output (p : Params) (m : Model p) : Point p := m.best.1

noncomputable def schedule (p : Params) (i : Fin p.n) : List Operation → Model p → LeonProtocol.Program (network p)
  | [], m => .finish (output p m)
  | op :: rest, m =>
    aggregate p i (location p m op) (reference p m op) op.level (op.precision p) fun v =>
      schedule p i rest (advance p m op v)

noncomputable def algorithm (p : Params) (deadline : Time) :
    Algorithm (spec.ComputeQuery p) (spec.ComputeReply p) (spec.CommReply p) (Point p) p.n where
  clock _ := 0
  timer t := if t = 0 then 0 else deadline + 1
  Seed := Fin (confidence p) → Fin (LeonTuning.iterations (network p))
  law := by
    letI : NeZero (LeonTuning.iterations (network p)) := ⟨by unfold LeonTuning.iterations; positivity⟩
    exact ⟨MeasureTheory.Measure.pi (fun _ : Fin (confidence p) =>
      (PMF.uniformOfFintype (Fin (LeonTuning.iterations (network p)))).toMeasure), inferInstance⟩
  State := LeonProtocol.State (network p)
  root := ⟨0, p.n.pos⟩
  initial i seed := ⟨schedule p i (operations p seed) (initialModel p), fun _ => [], false⟩
  query _ s _ := LeonProtocol.query (network p) s
  update _ s _ e := LeonProtocol.update (network p) s e
  output := (LeonProtocol.algorithm (network p) deadline).output

end LongTails.Algorithms.ContaminatedParallelDescent
