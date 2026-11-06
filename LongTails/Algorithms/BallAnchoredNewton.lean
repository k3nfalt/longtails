import LongTails.Setups.HessianStableSkewMonotone
import Mathlib.Data.Nat.Log

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.BallAnchoredNewton

open OracleTemplate LongTails.Setups.HessianStableSkewMonotone

noncomputable section

variable (p : Public)

def radius : ℝ := 1 / (8 * p.M)

def stepMax : ℝ := (2 * p.D + radius p) / p.ε

def tolerance (k : ℕ) : ℝ := radius p / (12 * ((k : ℝ) + 1) ^ 2)

def newtonCount (k : ℕ) (a Γ : ℝ) : ℕ :=
  2 * Nat.log2 (k + 1) + 2 * Nat.log2 ⌈1 + 4 * a * Γ⌉₊ + 9

def affinePoint (c : p.E) (B : p.E →L[ℝ] p.E) (b : p.E) : p.E := by
  classical
  exact if h : ∃ y ∈ Metric.closedBall c (radius p),
      ∀ v ∈ Metric.closedBall c (radius p), 0 ≤ ⟪b + B y + (1 : ℝ) • y, v - y⟫
    then Classical.choose h else c

inductive Phase where
  | centerValue
  | centerJac
  | stepValue
  | stepJac
  | finalValue
  | finished

structure State where
  phase : Phase
  k : ℕ
  A : ℝ
  z : p.E
  g : p.E
  h : ℕ
  bis : Bool
  lo : ℝ
  hi : ℝ
  a : ℝ
  Γ : ℝ
  t : ℕ
  u : p.E
  Fu : p.E
  Ju : p.E →L[ℝ] p.E

variable {p}

def State.w (s : State p) : p.E :=
  (s.a / (s.A + s.a)) • p.x0 + (s.A / (s.A + s.a)) • s.z

def State.c (s : State p) : p.E := s.w - (s.a * s.A / (s.A + s.a)) • s.g

def State.T (s : State p) : ℕ := newtonCount s.k s.a s.Γ

def State.newton (s : State p) : p.E :=
  affinePoint p s.c (s.a • s.Ju) (s.a • s.Fu - s.w - s.a • s.Ju s.u)

def readValue : p.E ⊕ (p.E →L[ℝ] p.E) → p.E
  | .inl v => v
  | .inr _ => 0

def readJacobian : p.E ⊕ (p.E →L[ℝ] p.E) → (p.E →L[ℝ] p.E)
  | .inl _ => 0
  | .inr J => J

def trialStart (k : ℕ) (A : ℝ) (z g : p.E) (h : ℕ) (bis : Bool) (lo hi a : ℝ) : State p :=
  ⟨.centerValue, k, A, z, g, h, bis, lo, hi, a, 0, 0, p.x0, 0, 0⟩

def outerStart (k : ℕ) (A : ℝ) (z g : p.E) : State p := by
  classical
  exact if stepMax p ≤ A then ⟨.finished, k, A, z, g, 0, false, 0, 0, 0, 0, 0, p.x0, 0, 0⟩
    else trialStart k A z g 0 false 0 0 (stepMax p)

def initial : State p := outerStart 0 0 p.x0 0

def State.accept (s : State p) : State p := outerStart (s.k + 1) (s.A + s.a) s.u s.Fu

def State.dhat (s : State p) : ℝ := ‖s.u - s.c‖

def State.afterFinal (s : State p) : State p := by
  classical
  exact
    if s.dhat < radius p / 3 then
      if s.bis then
        trialStart s.k s.A s.z s.g s.h true s.a s.hi ((s.a + s.hi) / 2)
      else if s.h = 0 then s.accept
      else trialStart s.k s.A s.z s.g s.h true s.a (2 * s.a) (3 * s.a / 2)
    else if 2 * radius p / 3 ≤ s.dhat then
      if s.bis then
        trialStart s.k s.A s.z s.g s.h true s.lo s.a ((s.lo + s.a) / 2)
      else trialStart s.k s.A s.z s.g (s.h + 1) false 0 0 (s.a / 2)
    else s.accept

def State.advance (s : State p) : State p :=
  if s.t + 1 = s.T then { s with phase := .finalValue, u := s.newton, t := s.t + 1 }
  else { s with phase := .stepValue, u := s.newton, t := s.t + 1 }

def query (s : State p) : Fin 2 × p.E :=
  match s.phase with
  | .centerValue => (0, s.c)
  | .centerJac => (1, s.c)
  | .stepValue => (0, s.u)
  | .stepJac => (1, s.u)
  | .finalValue => (0, s.u)
  | .finished => (0, p.x0)

def update (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E)) : State p :=
  match s.phase with
  | .centerValue => { s with phase := .centerJac, u := s.c, Fu := readValue reply }
  | .centerJac =>
      State.advance { s with Ju := readJacobian reply, Γ := ‖readJacobian reply‖, t := 0 }
  | .stepValue => { s with phase := .stepJac, Fu := readValue reply }
  | .stepJac => State.advance { s with Ju := readJacobian reply }
  | .finalValue => State.afterFinal { s with Fu := readValue reply }
  | .finished => s

def algorithm : Algorithm p.E (p.E ⊕ (p.E →L[ℝ] p.E)) p.E 2 where
  State := State p
  initial := fun _ => initial
  query := query
  update := update
  output := fun s => s.z

end

end LongTails.Algorithms.BallAnchoredNewton
