import LongTails.Algorithms.MonotoneCurvatureStage
import LongTails.Algorithms.RelativeCurvatureSearch
import LongTails.Algorithms.HessianSnapshot
import LongTails.Algorithms.EnergyHessianReuse
import LongTails.Setups.HessianLipschitzSecondOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Algorithms.MonotoneHessianReuse

open OracleTemplate LongTails.Setups.HessianLipschitzSecondOrder QuarticMetricStage
open scoped RealInnerProductSpace

noncomputable section

def gamma (p : Params) : ℝ := Real.sqrt (p.H * p.ε)
def scale (p : Params) : ℝ := max 1 (⌈p.m ^ (1 / 3 : ℝ)⌉₊ : ℝ)
def delta (p : Params) : ℝ := scale p ^ 2 * gamma p
def progress (p : Params) : ℝ := gamma p * (gamma p / (2 ^ 30 * p.H)) ^ 2
def stages (p : Params) : ℕ := ⌈p.Δ / progress p⌉₊ + 1
def relativeTolerance (p : Params) : ℝ := gamma p / (64 * delta p)
def degree (p : Params) : ℕ :=
  ⌈2 * Real.log (16 * max 1 (Module.finrank ℝ p.E : ℝ) / relativeTolerance p) /
    Real.sqrt (relativeTolerance p)⌉₊
def repetitions (p : Params) : ℕ := ⌈16 * Real.log ((stages p : ℝ) / p.ρ)⌉₊
def stageCalls (p : Params) : ℕ := 2 * MonotoneCurvatureStage.horizon (scale p) + 2
def searchCalls (p : Params) : ℕ := (degree p + 1) * repetitions p

abbrev Sign (p : Params) := Fin (Module.finrank ℝ p.E) → Bool
abbrev Block (p : Params) := Fin (repetitions p) → Sign p

structure Snapshot (p : Params) where
  point : p.E
  coordinates : p.E ≃L[ℝ] p.E

structure State (p : Params) where
  point : Point p.E
  snapshot : Option (Snapshot p)
  done : Bool

def padding (p : Params) (x : p.E) (n : ℕ) {U : Type} (u : U) : Plan p.E U n :=
  (Nat.one_mul n) ▸ (QueryPlan.traverse n (fun _ =>
    QueryPlan.ask ((0 : Fin 2), x) fun (_ : Reply p.E) => .done ())).map (fun _ => u)

def readHessian (p : Params) : Reply p.E → (p.E →L[ℝ] p.E)
  | .inr H => H
  | .inl _ => 0

def negativeDirection (p : Params) (H : p.E →L[ℝ] p.E) : Option p.E := by
  classical
  exact if h : ∃ v : p.E, ‖v‖ = 1 ∧ ⟪v, H v⟫ < -delta p
    then some (Classical.choose h) else none

def detect (p : Params) (S : p.E ≃L[ℝ] p.E) (x : Point p.E) (signs : Block p) :
    Plan p.E (Option p.E) (searchCalls p) :=
  (QueryPlan.traverse (repetitions p) (fun j => RelativeCurvatureSearch.search
    S.symm.toContinuousLinearMap x p.H (relativeTolerance p)
    (RelativeCurvatureSearch.seed (signs j)) (degree p))).map
      (fun results => results.foldl (fun prior next => prior.orElse (fun _ => next)) none)

def prepare (p : Params) (st : State p) : Plan p.E (State p × Option p.E) 1 := by
  classical
  let fresh : Plan p.E (State p × Option p.E) 1 := .ask (1, st.point.x) fun reply =>
    let H := readHessian p reply
    match negativeDirection p H with
    | some v => .done ({ st with snapshot := none }, some v)
    | none => .done ({ st with snapshot := some ⟨st.point.x,
        HessianSnapshot.coordinates (H + (4 * delta p) • ContinuousLinearMap.id ℝ p.E)⟩ }, none)
  exact if st.done then padding p st.point.x 1 (st, none) else
    match st.snapshot with
    | none => fresh
    | some snap => if ‖st.point.x - snap.point‖ ≤ delta p / (4 * p.H)
        then padding p st.point.x 1 (st, none) else fresh

def escape (p : Params) (x : Point p.E) (length : ℝ) (v : p.E) : Plan p.E (Point p.E) 1 :=
  let y := x.x + length • MonotoneCurvatureStage.signedDirection x.gradient v
  .ask (0, y) fun reply => .done (readPoint y reply)

def postStage (p : Params) (st : State p) (snap : Snapshot p) (x : Point p.E) (signs : Block p) :
    Plan p.E (State p) (searchCalls p + 1) := by
  classical
  exact if x.value ≤ st.point.value - progress p then
    padding p x.x (searchCalls p + 1) { st with point := x }
  else (show 1 + searchCalls p = searchCalls p + 1 by omega) ▸
    (detect p snap.coordinates x signs).bind (fun result =>
      match result with
      | none => padding p x.x 1 { st with point := x, done := true }
      | some v => (escape p x (gamma p / (1024 * p.H)) v).map
          (fun y => { st with point := y }))

def body (p : Params) (st : State p) (v : Option p.E) (signs : Block p) :
    Plan p.E (State p) (stageCalls p + searchCalls p + 1) := by
  classical
  exact if st.done then padding p st.point.x _ st else
    match v with
    | some v => (show (stageCalls p + searchCalls p) + 1 = stageCalls p + searchCalls p + 1 by omega) ▸
        (escape p st.point (delta p / p.H) v).bind (fun y =>
          padding p y.x (stageCalls p + searchCalls p) { st with point := y, snapshot := none })
    | none => match st.snapshot with
      | none => padding p st.point.x _ st
      | some snap => (show (searchCalls p + 1) + stageCalls p = stageCalls p + searchCalls p + 1 by omega) ▸
          (MonotoneCurvatureStage.plan
            (MonotoneCurvatureStage.parameters snap.coordinates st.point p.H (gamma p) (scale p))
            (MonotoneCurvatureStage.horizon (scale p))).bind (fun x => postStage p st snap x signs)

def step (p : Params) (st : State p) (signs : Block p) :
    Plan p.E (State p) (stageCalls p + searchCalls p + 2) :=
  (show (stageCalls p + searchCalls p + 1) + 1 = stageCalls p + searchCalls p + 2 by omega) ▸
    (prepare p st).bind (fun ready => body p ready.1 ready.2 signs)

def loop (p : Params) : (n : ℕ) → State p → (Fin n → Block p) →
    Plan p.E (State p) ((stageCalls p + searchCalls p + 2) * n)
  | 0, st, _ => .done st
  | n + 1, st, signs => by
      simpa only [Nat.mul_succ] using
        (step p st (signs 0)).bind (fun next => loop p n next (fun j => signs j.succ))

def plan (p : Params) (signs : Fin (stages p) → Block p) :
    Plan p.E p.E ((stageCalls p + searchCalls p + 2) * stages p + 1) :=
  .ask (0, p.x0) fun reply =>
    (loop p (stages p) ⟨readPoint p.x0 reply, none, false⟩ signs).map (fun st => st.point.x)

def algorithm (p : Params) : Algorithm p.E (Reply p.E) p.E 2 where
  Seed := Fin (stages p) → Block p
  law := ⟨MeasureTheory.Measure.pi fun _ : Fin (stages p) =>
    MeasureTheory.Measure.pi fun _ : Fin (repetitions p) =>
      (PMF.uniformOfFintype (Sign p)).toMeasure, inferInstance⟩
  State := Σ k, Plan p.E p.E k
  initial signs := ⟨_, plan p signs⟩
  query := QueryPlan.query (0, p.x0)
  update := QueryPlan.update
  output := QueryPlan.output p.x0

end

end LongTails.Algorithms.MonotoneHessianReuse
