import LongTails.Setups.UnconstrainedLipschitzJacobianMonotone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.LazyAnchoredExtraProximal

open OracleTemplate LongTails.Setups.UnconstrainedLipschitzJacobianMonotone

noncomputable section

variable (p : Params)

def outerCount : ℕ := ⌈(p.L * p.D ^ 2 / (p.m * p.ε)) ^ (2 / 5 : ℝ)⌉₊ + 1

def scale : ℝ := 4 * p.D / (p.ε * outerCount p * (outerCount p + 1))

def step (k : ℕ) : ℝ := scale p * (k + 1)

def cumulative (k : ℕ) : ℝ := scale p * k * (k + 1) / 2

def radiusBound (k : ℕ) : ℝ := p.D * step p k / cumulative p (k + 1)

def doublings (k : ℕ) : ℕ := Nat.log 2 ⌈p.L * step p k * radiusBound p k⌉₊ + 1

def guess (k j : ℕ) : ℝ := radiusBound p k * 2 ^ j / 2 ^ doublings p k

def condition (k j : ℕ) : ℝ := 5 * p.L * step p k * guess p k j + 1

def innerStep (k j : ℕ) : ℝ := step p k / condition p k j

def iterations (k j : ℕ) : ℕ :=
  ⌈8 / 3 * condition p k j * Real.log (36 * condition p k j ^ 2)⌉₊ + 1

def anchor (k : ℕ) (z : p.E) : p.E :=
  (step p k / cumulative p (k + 1)) • p.x0 + (cumulative p k / cumulative p (k + 1)) • z

def center (k : ℕ) (z Fz : p.E) : p.E :=
  anchor p k z - (step p k * cumulative p k / cumulative p (k + 1)) • Fz

def solve (J : p.E →L[ℝ] p.E) (β τ : ℝ) (r : p.E) : p.E :=
  Function.invFun (β • ContinuousLinearMap.id ℝ p.E + τ • J) r

inductive Phase where
  | jacobian
  | centerValue
  | trial
  | correction
  | finished

structure State where
  phase : Phase
  k : ℕ
  z : p.E
  Fz : p.E
  J : p.E →L[ℝ] p.E
  Fc : p.E
  j : ℕ
  i : ℕ
  zi : p.E
  Azi : p.E
  y : p.E
  Fy : p.E

variable {p}

def State.c (s : State p) : p.E := center p s.k s.z s.Fz

def State.w (s : State p) : p.E := anchor p s.k s.z

def State.a (s : State p) : ℝ := step p s.k

def State.τ (s : State p) : ℝ := innerStep p s.k s.j

def State.trialPoint (s : State p) : p.E :=
  solve p s.J (1 + s.τ / s.a) s.τ
    (s.zi - s.τ • s.Azi - s.τ • (s.Fc - s.J s.c - s.a⁻¹ • s.w))

def State.remainder (s : State p) (u Fu : p.E) : p.E := Fu - s.Fc - s.J (u - s.c)

def State.corrected (s : State p) : p.E := s.y - s.τ • (s.remainder s.y s.Fy - s.Azi)

def State.certificate (s : State p) : p.E := (s.a / s.τ) • (s.zi - s.corrected)

def accepted (s : State p) : Prop := ‖s.certificate‖ ≤ ‖s.y - s.c‖ / 2

def readValue : p.E ⊕ (p.E →L[ℝ] p.E) → p.E
  | .inl v => v
  | .inr _ => 0

def readJacobian : p.E ⊕ (p.E →L[ℝ] p.E) → (p.E →L[ℝ] p.E)
  | .inl _ => 0
  | .inr J => J

def nextPhase (k : ℕ) : Phase := if k = outerCount p then .finished else .jacobian

def outerStart (k : ℕ) (z Fz : p.E) : State p :=
  ⟨nextPhase (p := p) k, k, z, Fz, 0, 0, 0, 0, p.x0, 0, p.x0, 0⟩

def initial : State p := outerStart 0 p.x0 0

def query (s : State p) : Fin 2 × p.E :=
  match s.phase with
  | .jacobian => (1, s.c)
  | .centerValue => (0, s.c)
  | .trial => (0, s.trialPoint)
  | .correction => (0, s.corrected)
  | .finished => (0, p.x0)

def afterTrial (s : State p) (Fy : p.E) : State p := by
  classical
  exact
    let s' : State p := { s with phase := .correction, y := s.trialPoint, Fy := Fy }
    if accepted s' then outerStart (s.k + 1) s'.y Fy else s'

def afterCorrection (s : State p) (Fz1 : p.E) : State p :=
  if s.i + 1 = iterations p s.k s.j then
    ⟨.trial, s.k, s.z, s.Fz, s.J, s.Fc, s.j + 1, 0, s.c, 0, p.x0, 0⟩
  else
    ⟨.trial, s.k, s.z, s.Fz, s.J, s.Fc, s.j, s.i + 1, s.corrected,
      s.remainder s.corrected Fz1, p.x0, 0⟩

def update (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E)) : State p :=
  match s.phase with
  | .jacobian => { s with phase := .centerValue, J := readJacobian reply }
  | .centerValue =>
      ⟨.trial, s.k, s.z, s.Fz, s.J, readValue reply, 0, 0, s.c, 0, p.x0, 0⟩
  | .trial => afterTrial s (readValue reply)
  | .correction => afterCorrection s (readValue reply)
  | .finished => s

def algorithm : Algorithm p.E (p.E ⊕ (p.E →L[ℝ] p.E)) p.E 2 where
  State := State p
  initial := fun _ => initial
  query := query
  update := update
  output := fun s => s.z

end

end LongTails.Algorithms.LazyAnchoredExtraProximal
