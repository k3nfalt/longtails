import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.StrongGrowthRestartedAgd

open OracleTemplate

structure Config where
  η : ℝ
  θ : ℝ
  B : ℝ
  ηf : ℝ
  thr : ℝ
  K : ℕ
  b : ℕ
  m : ℕ
  N1 : ℕ

def Config.Eb (cfg : Config) : ℕ := cfg.K + 1 + cfg.m

noncomputable def pW (K : ℕ) : ℝ := ∑ k ∈ Finset.range K, (k : ℝ) * ((K : ℝ) - k)

noncomputable def pw (K k : ℕ) : ℝ := (k : ℝ) * ((K : ℝ) - k) / pW K

structure State (E : Type) where
  t : ℕ
  i : ℕ
  acc : E
  xPrev : E
  x : E
  xStart : E
  glast : E
  S : ℝ
  ybar : E
  trig : Bool
  vCount : ℕ
  out : E
  done : Bool

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def initState (x0 : E) : State E :=
  { t := 0, i := 0, acc := 0, xPrev := x0, x := x0, xStart := x0, glast := 0, S := 0,
    ybar := 0, trig := false, vCount := 0, out := x0, done := false }

def Config.pos (cfg : Config) (t : ℕ) : ℕ := t % cfg.Eb

noncomputable def ypoint (cfg : Config) (s : State E) : E := s.x + (1 - cfg.θ) • (s.x - s.xPrev)

noncomputable def queryPoint (cfg : Config) (s : State E) : E :=
  if cfg.pos s.t < cfg.K then (if s.trig then s.x else ypoint cfg s)
  else if cfg.pos s.t = cfg.K then s.x
  else s.ybar

noncomputable def restart (cfg : Config) (x0 : E) (s : State E) : State E :=
  let xs := if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else s.x
  { s with
    t := s.t + 1
    xPrev := xs
    x := xs
    xStart := xs
    glast := 0
    S := 0
    ybar := 0
    trig := false
    vCount := 0 }

noncomputable def batchUpdate (cfg : Config) (x0 : E) (s : State E) (g : E) : State E :=
  let j := cfg.pos s.t
  if j < cfg.K then
    if s.trig then { s with t := s.t + 1 }
    else
      let y := ypoint cfg s
      let xNew := y - cfg.η • g
      let S' := s.S + ‖xNew - s.x‖ ^ 2
      let ybar' := s.ybar + pw cfg.K j • y
      let fire : Bool := decide (cfg.B ^ 2 < ((j + 1 : ℕ) : ℝ) * S')
      { s with
        t := s.t + 1
        xPrev := s.x
        x := xNew
        glast := g
        S := S'
        ybar := ybar'
        trig := fire }
  else if j = cfg.K then
    { s with t := s.t + 1, xPrev := s.x - cfg.ηf • g, x := s.x - cfg.ηf • g }
  else
    let vCount' := if s.trig then s.vCount else s.vCount + (if ‖g‖ ≤ cfg.thr then 1 else 0)
    if j + 1 < cfg.Eb then { s with t := s.t + 1, vCount := vCount' }
    else if ¬ s.trig ∧ 2 * vCount' > cfg.m then
      { s with t := s.t + 1, done := true, out := s.ybar }
    else restart cfg x0 s

noncomputable def update (cfg : Config) (x0 : E) (s : State E) (r : E) : State E :=
  if s.done then s
  else
    let acc := s.acc + r
    if s.i + 1 < cfg.b then { s with i := s.i + 1, acc := acc }
    else batchUpdate cfg x0 { s with i := 0, acc := 0 } ((1 / (cfg.b : ℝ)) • acc)

noncomputable def method (cfg : Config) (x0 : E) : Algorithm E E E where
  State := State E
  initial _ := initState x0
  query s := (0, queryPoint cfg s)
  update := update cfg x0
  output s := s.out

end LongTails.Algorithms.StrongGrowthRestartedAgd
