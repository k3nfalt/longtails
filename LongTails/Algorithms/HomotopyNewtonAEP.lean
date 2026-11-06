import LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Log

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.HomotopyNewtonAEP

open OracleTemplate LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone

noncomputable section

variable (p : Params)

def outerCount : ℕ := ⌈(p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ)⌉₊ + 1

def scale : ℝ := 4 * p.D / (p.ε * outerCount p * (outerCount p + 1))

def step (k : ℕ) : ℝ := scale p * (k + 1)

def cumulative (k : ℕ) : ℝ := scale p * k * (k + 1) / 2

def stiff : ℝ := 2 * p.H₀ + 250 * p.L * p.D ^ 2

def anchor (k : ℕ) (z : p.E) : p.E :=
  (step p k / cumulative p (k + 1)) • p.x0 + (cumulative p k / cumulative p (k + 1)) • z

def center (k : ℕ) (z Fz : p.E) : p.E :=
  anchor p k z - (step p k * cumulative p k / cumulative p (k + 1)) • Fz

def guess (k : ℕ) (g : ℝ) (j : ℕ) : ℝ := g * 2 ^ j / (1 + step p k * stiff p)

def ratio (k : ℕ) (g : ℝ) (j : ℕ) : ℝ :=
  min 1 (1 / (50 * Real.sqrt (step p k * p.L) * guess p k g j))

def start (k : ℕ) (g : ℝ) (j : ℕ) : ℝ :=
  min (step p k) (step p k * ratio p k g j * 2 ^ j / (1 + step p k * stiff p))

def stages (k : ℕ) (g : ℝ) (j : ℕ) : ℕ :=
  ⌈Real.log (step p k / start p k g j) / Real.log (1 + ratio p k g j)⌉₊

def stageParam (k : ℕ) (g : ℝ) (j i : ℕ) : ℝ :=
  min (step p k) (start p k g j * (1 + ratio p k g j) ^ i)

def extra (k : ℕ) : ℕ := Nat.log2 (⌈step p k * stiff p⌉₊ + 2) + 5

def programLength (k : ℕ) (g : ℝ) (j : ℕ) : ℕ := 3 * (stages p k g j + 1) + extra p k

def stepParam (k : ℕ) (g : ℝ) (j i : ℕ) : ℝ :=
  if i < 3 * (stages p k g j + 1) then stageParam p k g j (i / 3) else step p k

def target (k : ℕ) (z Fz : p.E) (b : ℝ) : p.E :=
  center p k z Fz + (b / step p k) • (anchor p k z - center p k z Fz)

def newtonStep (b : ℝ) (v y Fy : p.E) (J : p.E →L[ℝ] p.E) : p.E :=
  y - Function.invFun (ContinuousLinearMap.id ℝ p.E + b • J) (b • Fy + y - v)

inductive Phase where
  | centerValue
  | newtonValue
  | newtonJac
  | certify
  | finished

structure State where
  phase : Phase
  k : ℕ
  z : p.E
  Fz : p.E
  Fc : p.E
  j : ℕ
  i : ℕ
  y : p.E
  Fy : p.E

variable {p}

def State.a (s : State p) : ℝ := step p s.k

def State.w (s : State p) : p.E := anchor p s.k s.z

def State.c (s : State p) : p.E := center p s.k s.z s.Fz

def State.g (s : State p) : ℝ := ‖s.a • s.Fc + s.c - s.w‖

def State.b (s : State p) : ℝ := stepParam p s.k s.g s.j s.i

def State.next (s : State p) (J : p.E →L[ℝ] p.E) : p.E :=
  newtonStep p s.b (target p s.k s.z s.Fz s.b) s.y s.Fy J

def readValue : p.E ⊕ (p.E →L[ℝ] p.E) → p.E
  | .inl v => v
  | .inr _ => 0

def readJacobian : p.E ⊕ (p.E →L[ℝ] p.E) → (p.E →L[ℝ] p.E)
  | .inl _ => 0
  | .inr J => J

def nextPhase (k : ℕ) : Phase := if k = outerCount p then .finished else .centerValue

def outerStart (k : ℕ) (z Fz : p.E) : State p :=
  ⟨nextPhase (p := p) k, k, z, Fz, 0, 0, 0, p.x0, 0⟩

def initial : State p := outerStart 0 p.x0 0

def query (s : State p) : Fin 2 × p.E :=
  match s.phase with
  | .centerValue => (0, s.c)
  | .newtonValue => (0, s.y)
  | .newtonJac => (1, s.y)
  | .certify => (0, s.y)
  | .finished => (0, p.x0)

def afterCenter (s : State p) (Fc : p.E) : State p := by
  classical
  exact
    let s' : State p :=
      { s with phase := .newtonValue, Fc := Fc, j := 0, i := 0, y := s.c, Fy := 0 }
    if s'.g = 0 then outerStart (s.k + 1) s.c Fc else s'

def afterJacobian (s : State p) (J : p.E →L[ℝ] p.E) : State p :=
  if s.i + 1 = programLength p s.k s.g s.j then
    { s with phase := .certify, i := s.i + 1, y := s.next J, Fy := 0 }
  else
    { s with phase := .newtonValue, i := s.i + 1, y := s.next J, Fy := 0 }

def afterCertify (s : State p) (Fy : p.E) : State p := by
  classical
  exact
    if ‖s.a • Fy + s.y - s.w‖ ≤ ‖s.y - s.c‖ / 2 then outerStart (s.k + 1) s.y Fy
    else { s with phase := .newtonValue, j := s.j + 1, i := 0, y := s.c, Fy := 0 }

def update (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E)) : State p :=
  match s.phase with
  | .centerValue => afterCenter s (readValue reply)
  | .newtonValue => { s with phase := .newtonJac, Fy := readValue reply }
  | .newtonJac => afterJacobian s (readJacobian reply)
  | .certify => afterCertify s (readValue reply)
  | .finished => s

def algorithm : Algorithm p.E (p.E ⊕ (p.E →L[ℝ] p.E)) p.E 2 where
  State := State p
  initial := fun _ => initial
  query := query
  update := update
  output := fun s => s.z

end

end LongTails.Algorithms.HomotopyNewtonAEP
