import LongTails.Algorithms.SplitBrox
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox (Query Reply mix)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

inductive Stage where
  | init0
  | init1
  | run
  | check
  | frozen

structure State (E : Type*) where
  stage : Stage
  f0 : ℝ
  g0 : E
  lb : ℝ
  ub : ℝ
  best : E
  Lh : ℝ
  inner : SplitBrox.State E
  calls : ℕ
  zval : ℝ
  zpt : E
  zg : E
  phases : ℕ
  doublings : ℕ

def horizon (R Lh gap : ℝ) : ℕ := ⌈Real.sqrt (40 * Lh * R ^ 2 / gap)⌉₊ + 1

def base (R Lh gap : ℝ) : ℝ := R / Real.sqrt (horizon R Lh gap)

def level (s : State E) : ℝ := (s.ub + s.lb) / 2

def gap (s : State E) : ℝ := s.ub - s.lb

def phaseK (R : ℝ) (s : State E) : ℕ := horizon R s.Lh (gap s)

def phaseB (R : ℝ) (s : State E) : ℝ := base R s.Lh (gap s)

def startPhase (ε : ℝ) (x0 : E) (s : State E) : State E :=
  if gap s ≤ ε then { s with stage := .frozen }
  else { s with stage := .run, inner := ⟨0, 0, x0, x0, .first⟩, calls := 0 }

def query (R : ℝ) (x0 : E) (s : State E) : Query E :=
  match s.stage with
  | .init0 => .inl x0
  | .init1 => .inr (x0, R, s.g0)
  | .run => SplitBrox.query (phaseK R s) (phaseB R s) s.inner
  | .check => .inl s.inner.primal
  | .frozen => .inl x0

def runUpdate (R ε : ℝ) (x0 : E) (s : State E) (reply : Reply E) : State E :=
  let K := phaseK R s
  let t := SplitBrox.update K (level s) s.inner reply
  let s1 : State E := match s.inner.phase, reply with
    | .first, .inl (value, g) =>
      { s with zval := value, zpt := mix s.inner.completed s.inner.primal s.inner.momentum, zg := g }
    | _, _ => s
  if s.inner.completed < t.completed then { s1 with stage := .check, inner := t, calls := s.calls + 1 }
  else if 4 * K ≤ s.calls + 1 then
    startPhase ε x0 { s1 with lb := level s, phases := s.phases + 1, calls := s.calls + 1 }
  else { s1 with inner := t, calls := s.calls + 1 }

def checkUpdate (R ε : ℝ) (x0 : E) (s : State E) (value : ℝ) : State E :=
  let K := phaseK R s
  let y := s.inner.primal
  if s.zval + ⟪s.zg, y - s.zpt⟫ + s.Lh / 2 * ‖y - s.zpt‖ ^ 2 < value then
    startPhase ε x0 { s with Lh := 2 * s.Lh, doublings := s.doublings + 1, calls := s.calls + 1 }
  else if K ≤ s.inner.completed then
    if value ≤ level s + gap s / 4 then
      startPhase ε x0 { s with ub := value, best := y, phases := s.phases + 1, calls := s.calls + 1 }
    else startPhase ε x0 { s with lb := level s, phases := s.phases + 1, calls := s.calls + 1 }
  else if 4 * K ≤ s.calls + 1 then
    startPhase ε x0 { s with lb := level s, phases := s.phases + 1, calls := s.calls + 1 }
  else { s with stage := .run, calls := s.calls + 1 }

def update (R ε : ℝ) (x0 : E) (s : State E) (reply : Reply E) : State E :=
  match s.stage, reply with
  | .init0, .inl (value, g) => { s with stage := .init1, f0 := value, g0 := g, ub := value, best := x0 }
  | .init1, .inr v =>
    startPhase ε x0 { s with lb := s.f0 + ⟪s.g0, v - x0⟫, Lh := ε / R ^ 2 }
  | .run, r => runUpdate R ε x0 s r
  | .check, .inl (value, _) => checkUpdate R ε x0 s value
  | _, _ => s

def algorithm (R ε : ℝ) (x0 : E) : Algorithm (Query E) (Reply E) E where
  State := State E
  initial _ := ⟨.init0, 0, 0, 0, 0, x0, 0, ⟨0, 0, x0, x0, .first⟩, 0, 0, x0, 0, 0, 0⟩
  query s := (0, query R x0 s)
  update := update R ε x0
  output s := s.best

end OracleTemplate.CertifiedLevelBrox
