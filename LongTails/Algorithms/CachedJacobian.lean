import LongTails.Algorithms.EnergyHessianReuse
import LongTails.Setups.LipschitzJacobianMonotone
import Mathlib.Data.Nat.Log

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.CachedJacobian

open OracleTemplate LongTails.Setups.LipschitzJacobianMonotone

noncomputable section

abbrev Reply (p : Params) := p.E ⊕ (p.E →L[ℝ] p.E)
abbrev Plan (p : Params) (U : Type) (n : ℕ) := QueryPlan (Fin 2 × p.E) (Reply p) U n

def initialStep (p : Params) : ℝ := 1 / (16384 * p.m * p.L * p.D)

def outerCount (p : Params) : ℕ := ⌈1024 * Real.sqrt (p.m * p.L * p.D ^ 2 / p.ε)⌉₊ + 1

def innerCount (p : Params) : ℕ := 2 * Nat.log 2 (outerCount p + 1) + 4

def stepSize (p : Params) (t : ℕ) : ℝ := initialStep p * (t + 3) / 3

def cacheRadius (p : Params) : ℝ := 1 / (16 * p.L * stepSize p (outerCount p - 1))

def affinePoint (p : Params) (B : p.E →L[ℝ] p.E) (b : p.E) (μ : ℝ) : p.E := by
  classical
  exact if h : ∃ v ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪b + B v + μ • v, z - v⟫
    then Classical.choose h else p.x0

def readValue (p : Params) : Reply p → p.E
  | .inl g => g
  | .inr _ => 0

def readJacobian (p : Params) : Reply p → (p.E →L[ℝ] p.E)
  | .inl _ => 0
  | .inr B => B

structure State (p : Params) where
  point : p.E
  value : p.E
  normal : p.E
  snapshot : p.E
  matrix : p.E →L[ℝ] p.E

def refresh (p : Params) (a : State p) : Prop := cacheRadius p < ‖a.point - a.snapshot‖

def replaceCache (p : Params) (a : State p) (r : Reply p) : State p := by
  classical
  exact if refresh p a then { a with snapshot := a.point, matrix := readJacobian p r } else a

def nextPoint (p : Params) (t : ℕ) (center : p.E) (a : State p) : p.E :=
  affinePoint p a.matrix
    (a.value - a.matrix a.point - (stepSize p t)⁻¹ • center) (stepSize p t)⁻¹

def move (p : Params) (t : ℕ) (center : p.E) (a : State p) (z value : p.E) : State p where
  point := z
  value := value
  normal := -(a.value + a.matrix (z - a.point) + (stepSize p t)⁻¹ • (z - center))
  snapshot := a.snapshot
  matrix := a.matrix

def innerStep (p : Params) (t : ℕ) (center : p.E) (a : State p) : Plan p (State p) 2 := by
  classical
  exact .ask ((if refresh p a then 1 else 0), a.point) fun r =>
    let b := replaceCache p a r
    let z := nextPoint p t center b
    .ask (0, z) fun rz => .done (move p t center b z (readValue p rz))

def repeatInner (p : Params) (t : ℕ) (center : p.E) :
    (n : ℕ) → State p → Plan p (State p) (2 * n)
  | 0, a => .done a
  | n + 1, a => (innerStep p t center a).bind (repeatInner p t center n)

def center (p : Params) (t : ℕ) (a : State p) : p.E :=
  (1 - 2 / (t + 2 : ℝ)) • a.point + (2 / (t + 2 : ℝ)) • p.x0

def outerStep (p : Params) (t : ℕ) (a : State p) : Plan p (State p) (2 * innerCount p) :=
  repeatInner p t (center p t a) (innerCount p) a

def repeatOuter (p : Params) : (n t : ℕ) → State p →
    Plan p (State p) ((2 * innerCount p) * n)
  | 0, _, a => .done a
  | n + 1, t, a => (outerStep p t a).bind (repeatOuter p n (t + 1))

def plan (p : Params) : Plan p p.E ((2 * innerCount p) * outerCount p + 2) :=
  .ask (0, p.x0) fun r => .ask (1, p.x0) fun j =>
    (repeatOuter p (outerCount p) 0
      { point := p.x0, value := readValue p r, normal := 0,
        snapshot := p.x0, matrix := readJacobian p j }).map State.point

def output (p : Params) : Algorithm p.E (Reply p) p.E 2 :=
  EnergyHessianReuse.channelAlgorithm (0, p.x0) p.x0 (plan p)

end

end LongTails.Algorithms.CachedJacobian
