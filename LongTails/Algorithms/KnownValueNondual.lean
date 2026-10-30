import LongTails.Setups.KnownValueNondualGeneralizedConvex
import LongTails.Algorithms.NondualSelector
import LongTails.Algorithms.NondualLineSearch
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.KnownValueNondual

open LongTails.Setups.KnownValueNondualGeneralizedConvex

abbrev Point (p : Public) := EuclideanSpace ℝ (Fin p.d)

def warmScale (p : Public) : ℝ := 1 + (⌈(p.L1 * p.R) ^ (1 / 3 : ℝ)⌉₊ : ℝ)

def selectorRadius (p : Public) : ℝ := p.R * Real.sqrt ((p.d : ℝ) / (1 + Nat.log 2 p.d))

def midpointCount (p : Public) : ℕ :=
  1 + Nat.log 2 ⌈128 * (1 + 32 * p.L0 * p.R ^ 2 / p.ε + 4 * p.L1 * p.R) ^ 2⌉₊

def lineCalls (p : Public) : ℕ := midpointCount p + 2

def initialBody (p : Public) : Set (Point p) := {u | ∑ i, |u i| ≤ p.R}

def selector (p : Public) (K : Set (Point p)) : Point p :=
  if hd : p.d = 0 then p.x0 else
    letI : NeZero p.d := ⟨hd⟩
    p.x0 + NondualSelector.center K (selectorRadius p)

structure Control (p : Public) where
  body : Set (Point p)
  incumbent : Point p
  target : ℝ
  warm : Bool
  finished : Bool
  phase : ℕ

structure State (p : Public) where
  control : Control p
  line : NondualLineSearch.State (Point p)
  ticks : ℕ

def initialControl (p : Public) : Control p where
  body := initialBody p
  incumbent := p.x0
  target := if 1 < p.L1 * p.R then
    max p.ε (4 * p.L0 * p.R / p.L1 * Real.exp (warmScale p))
    else max p.ε (p.L0 * p.R ^ 2)
  warm := decide (1 < p.L1 * p.R)
  finished := decide (p.L1 * p.R ≤ 1 ∧ 2 * p.L0 * p.R ^ 2 ≤ p.ε)
  phase := 0

def rootCut (p : Public) (c : Control p) (x : Point p) (value : ℝ) (g : Point p) : Set (Point p) :=
  c.body ∩ {u | value + ⟪g, p.x0 + u - x⟫ +
    (if c.warm then warmScale p / (2 * p.L1) * ‖g‖ else 0) ≤ p.fstar}

def finishLine (p : Public) (c : Control p)
    (out : Point p × NondualLineSearch.Reply (Point p) × Bool) : Control p :=
  if out.2.2 then { c with incumbent := out.1, finished := true }
  else
    let x := out.1
    let value := out.2.1.1
    let g := out.2.1.2
    let H := p.L0 + p.L1 * ‖g‖
    let next := x - (1 / (4 * H)) • g
    let upper := value - 5 * ‖g‖ ^ 2 / (24 * H)
    if upper - p.fstar ≤ p.ε then { c with incumbent := next, finished := true }
    else if upper - p.fstar ≤ c.target then
      { c with incumbent := next, target := max p.ε (c.target / 2), warm := false, phase := c.phase + 1 }
    else { c with body := rootCut p c x value g, incumbent := next }

def query (p : Public) (s : State p) : Point p :=
  if s.control.finished then p.x0
  else NondualLineSearch.query (selector p s.control.body) s.control.incumbent s.line

def update (p : Public) (s : State p) (reply : NondualLineSearch.Reply (Point p)) : State p :=
  if s.control.finished then s
  else
    let z := selector p s.control.body
    let line := NondualLineSearch.update (4 * p.R) (p.ε / 2) z s.control.incumbent s.line reply
    if s.ticks + 1 = lineCalls p then
      { control := finishLine p s.control (NondualLineSearch.output z s.control.incumbent line)
        line := .first
        ticks := 0 }
    else { s with line := line, ticks := s.ticks + 1 }

def algorithm (p : Public) : OracleTemplate.Algorithm (Point p)
    (NondualLineSearch.Reply (Point p)) (Point p) where
  State := State p
  initial _ := ⟨initialControl p, .first, 0⟩
  query s := (0, query p s)
  update := update p
  output s := s.control.incumbent

end LongTails.Algorithms.KnownValueNondual
