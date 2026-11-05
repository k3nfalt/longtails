import LongTails.Setups.HigherSmoothBilevel
import LongTails.Algorithms.Accelerated
import LongTails.Algorithms.QueryPlan
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Algorithms.BilevelAccelerated

open OracleTemplate LongTails.Setups.HigherSmoothBilevel

noncomputable section

structure Tuning where
  η : ℝ
  θ : ℝ
  B : ℝ
  lam : ℝ
  K : ℕ
  m : ℕ
  J : ℕ
  N : ℕ

def tuning (p : Params) : Tuning :=
  let κ := p.L / p.μ
  let q := Real.sqrt κ
  let L := 32 * p.L * q ^ 5
  let ρ := 512 * p.L * q ^ 8
  let e := p.ε / 1024
  let η := 1 / (4 * L)
  let B := Real.sqrt (e / ρ)
  let σ := e / 100
  let K := ⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊
  let E := ⌊p.Δ * Real.sqrt ρ / (e * Real.sqrt e)⌋₊ + 1
  let R := E * (2 * B + η * (p.L * (1 + κ) + σ)) + 2 * B
  let lam := 1 + 2 * κ + 16 * p.L * κ ^ 3 / σ
  let τ := σ * p.μ / (10 * lam * p.L)
  let D := (p.G + p.L * R + p.L / lam) / p.μ
  ⟨η, 1 / K, B, lam, K, ⌈8 * q⌉₊, ⌈Real.log (1 + 2 * p.L * D / τ) / Real.log 2⌉₊, K * E⟩

def repeatPlan {Q R S : Type*} {c : ℕ} : (n : ℕ) →
    (S → QueryPlan Q R S c) → S → QueryPlan Q R S (c * n)
  | 0, _, s => .done s
  | n + 1, body, s => QueryPlan.bind (body s) (repeatPlan n body)

def lowerReply (p : Params) (lam : ℝ) (r : Reply p) : p.Y :=
  (InnerProductSpace.toDual ℝ p.Y).symm
    ((r.2.2.2 + lam⁻¹ • r.2.2.1).comp (.inr ℝ p.X p.Y))

def upperReply (p : Params) (A : (p.X × p.Y) →L[ℝ] ℝ) : p.X :=
  (InnerProductSpace.toDual ℝ p.X).symm (A.comp (.inl ℝ p.X p.Y))

def innerSteps (p : Params) (x : p.X) (lam : ℝ) : (m : ℕ) →
    (ℕ × p.Y × p.Y) → QueryPlan (p.X × p.Y) (Reply p) (ℕ × p.Y × p.Y) m
  | 0, s => .done s
  | m + 1, s => .ask (x, Gradient.acceleratedQuery s) (fun r =>
      innerSteps p x lam m ((Gradient.accelerated (2 * p.L, p.y0)).update s (lowerReply p lam r)))

def innerEpoch (p : Params) (x : p.X) (lam : ℝ) (m : ℕ) (y : p.Y) :
    QueryPlan (p.X × p.Y) (Reply p) p.Y m :=
  QueryPlan.map (fun s : ℕ × p.Y × p.Y => s.2.1) (innerSteps p x lam m (0, y, y))

def innerSolve (p : Params) (t : Tuning) (x : p.X) (lam : ℝ) :
    QueryPlan (p.X × p.Y) (Reply p) p.Y (t.m * t.J) :=
  repeatPlan t.J (innerEpoch p x lam t.m) p.y0

def estimatorCalls (t : Tuning) : ℕ := (2 + t.m * t.J) + t.m * t.J

def estimate (p : Params) (t : Tuning) (x : p.X) :
    QueryPlan (p.X × p.Y) (Reply p) p.X (estimatorCalls t) :=
  QueryPlan.bind (innerSolve p t x t.lam) (fun y =>
    QueryPlan.bind (innerSolve p t x 0) (fun z =>
      QueryPlan.ask (x, y) (fun ry => QueryPlan.ask (x, z) (fun rz =>
        QueryPlan.done (upperReply p ry.2.2.1 +
          t.lam • (upperReply p ry.2.2.2 - upperReply p rz.2.2.2))))))

structure OuterState (X : Type*) where
  x : X
  previous : X
  start : X
  index : ℕ
  movement : ℝ
  querySum : X
  bestMovement : ℝ
  bestOutput : X
  finished : Bool
  result : X

def initial {X : Type*} [Zero X] (x : X) : OuterState X :=
  ⟨x, x, x, 0, 0, 0, 0, x, false, x⟩

def context (p : Params) (t : Tuning) (s : OuterState p.X) : p.X :=
  if s.finished then p.x0 else s.x + (1 - t.θ) • (s.x - s.previous)

open Classical in
def advance (p : Params) (t : Tuning) (s : OuterState p.X) (v : p.X) : OuterState p.X :=
  if s.finished then s else
  let w := context p t s
  let x := w - t.η • v
  let movement := ‖x - s.x‖ ^ 2
  let total := s.movement + movement
  let querySum := s.querySum + w
  let best := t.K / 2 ≤ s.index ∧ (s.index = t.K / 2 ∨ movement < s.bestMovement)
  let bestOutput := if best then ((s.index + 1 : ℕ) : ℝ)⁻¹ • querySum else s.bestOutput
  if ((s.index + 1 : ℕ) : ℝ) * total > t.B ^ 2 then initial x else
  { s with
    x := x
    previous := s.x
    index := s.index + 1
    movement := total
    querySum := querySum
    bestMovement := if best then movement else s.bestMovement
    bestOutput := bestOutput
    finished := decide (s.index + 1 = t.K)
    result := bestOutput }

def outerStep (p : Params) (t : Tuning) (s : OuterState p.X) :
    QueryPlan (p.X × p.Y) (Reply p) (OuterState p.X) (estimatorCalls t) :=
  QueryPlan.map (advance p t s) (estimate p t (context p t s))

def outputPlan (p : Params) :
    QueryPlan (p.X × p.Y) (Reply p) p.X (estimatorCalls (tuning p) * (tuning p).N) :=
  QueryPlan.map (fun s => s.result) (repeatPlan (tuning p).N (outerStep p (tuning p)) (initial p.x0))

def initialAlgorithm (p : Params) : Algorithm (p.X × p.Y) (Reply p) p.X :=
  { State := Unit, initial := fun _ => (), query := fun _ => (0, (p.x0, p.y0)),
    update := fun _ _ => (), output := fun _ => p.x0 }

open Classical in
def algorithm (p : Params) : Algorithm (p.X × p.Y) (Reply p) p.X :=
  if 2 * p.L * (p.L / p.μ) ≤ p.ε then initialAlgorithm p
  else QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    (p.x0, p.y0) p.x0 _ (fun _ => outputPlan p)

end

end LongTails.Algorithms.BilevelAccelerated
