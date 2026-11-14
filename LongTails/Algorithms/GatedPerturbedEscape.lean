import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.ProductMeasure

namespace LongTails.Algorithms.GatedPerturbedEscape

open OracleTemplate MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

structure Config where
  η : ℝ
  r : ℝ
  s0 : ℝ
  gth : ℝ
  θ : ℝ
  τg : ℝ
  τ0 : ℝ
  τq : ℝ
  M : ℕ
  T : ℕ
  k : ℕ
  b : ℕ

inductive Phase where
  | test
  | grad0
  | init
  | traj
  | ray
  deriving DecidableEq

structure State (E : Type) where
  i : ℕ
  acc : E
  t : ℕ
  ph : Phase
  j : ℕ
  x : E
  store : ℕ → E
  g0 : E
  v : E
  w : E
  att : ℕ
  found : Bool
  dx : E
  done : Bool
  zs : ℕ → E

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def votes {α : Type} [NormedAddCommGroup α] (M : ℕ) (τ : ℝ) (s : ℕ → α) (a : ℕ) : ℕ :=
  ((Finset.range M).filter (fun c => ‖s a - s c‖ ≤ 2 * τ)).card

lemma pick_exists {α : Type} [NormedAddCommGroup α] (M : ℕ) (τ : ℝ) (s : ℕ → α) :
    ∃ n, (n < M ∧ M < 2 * votes M τ s n) ∨ n = M := ⟨M, Or.inr rfl⟩

noncomputable def pick {α : Type} [NormedAddCommGroup α] (M : ℕ) (τ : ℝ) (s : ℕ → α) : ℕ :=
  Nat.find (pick_exists M τ s)

noncomputable def select {α : Type} [NormedAddCommGroup α] (M : ℕ) (τ : ℝ) (s : ℕ → α) : α :=
  s (pick M τ s)

noncomputable def clip (r : ℝ) (u : E) : E := if ‖u‖ ≤ r then u else (r / ‖u‖) • u

noncomputable def queryPoint (cfg : Config) (s : State E) : E :=
  match s.ph with
  | .test => s.x
  | .grad0 => s.x
  | .init => s.x
  | .traj => s.x + s.v
  | .ray => s.x + cfg.r • s.w

noncomputable def endAttempt (cfg : Config) (s : State E) : State E :=
  if s.att + 1 < cfg.k then { s with att := s.att + 1, ph := .grad0, j := 0 }
  else if s.found then { s with x := s.x + s.dx, ph := .test, j := 0, found := false }
  else { s with done := true }

noncomputable def blockUpdate (cfg : Config) (d : ℕ) (s : State E) (gb z : E) : State E :=
  match s.ph with
  | .test =>
    let st := Function.update s.store s.j gb
    if s.j + 1 < cfg.M then { s with store := st, j := s.j + 1 }
    else
      let gh := select cfg.M cfg.τg st
      if cfg.gth < ‖gh‖ then { s with store := st, j := 0, x := s.x - cfg.η • gh }
      else { s with store := st, j := 0, ph := .grad0, att := 0, found := false }
  | .grad0 =>
    let st := Function.update s.store s.j gb
    if s.j + 1 < cfg.M then { s with store := st, j := s.j + 1 }
    else
      { s with store := st, j := 0, ph := .init, g0 := select cfg.M cfg.τ0 st }
  | .init => { s with ph := .traj, v := clip cfg.r ((cfg.s0 / Real.sqrt d) • z) }
  | .traj =>
    let v' := clip cfg.r (s.v - cfg.η • (gb - s.g0))
    if s.j + 1 < cfg.T then { s with v := v', j := s.j + 1 }
    else { s with v := v', j := 0, ph := .ray, w := (1 / ‖v'‖) • v' }
  | .ray =>
    let st := Function.update s.store s.j gb
    if s.j + 1 < cfg.M then { s with store := st, j := s.j + 1 }
    else
      let qh := select cfg.M cfg.τq (fun c => ⟪s.w, st c - s.g0⟫ / cfg.r)
      let sg : ℝ := if 0 ≤ ⟪s.g0, s.w⟫ then 1 else -1
      if s.found = false ∧ cfg.r / 2 ≤ ‖s.v‖ ∧ qh ≤ -2 * cfg.θ then
        endAttempt cfg { s with store := st, j := 0, found := true, dx := -((sg * cfg.r) • s.w) }
      else endAttempt cfg { s with store := st, j := 0 }

noncomputable def stepBlock (cfg : Config) (d : ℕ) (s : State E) (gb z : E) : State E :=
  let s' := blockUpdate cfg d s gb z
  { s' with t := s.t + 1 }

noncomputable def update (cfg : Config) (d : ℕ) (s : State E) (rep : E) : State E :=
  if s.done then s
  else
    let acc := s.acc + rep
    if s.i + 1 < cfg.b then { s with i := s.i + 1, acc := acc }
    else stepBlock cfg d { s with i := 0, acc := 0 } ((1 / (cfg.b : ℝ)) • acc) (s.zs s.t)

noncomputable def initState (x0 : E) (zs : ℕ → E) : State E :=
  { i := 0, acc := 0, t := 0, ph := .test, j := 0, x := x0, store := fun _ => 0,
    g0 := 0, v := 0, w := 0, att := 0, found := false, dx := 0, done := false,
    zs := zs }

noncomputable def method [FiniteDimensional ℝ E] [MeasurableSpace E]
    (cfg : Config) (x0 : E) : Algorithm E E E where
  Seed := ℕ → E
  law := ⟨Measure.infinitePi (fun _ : ℕ => stdGaussian E), inferInstance⟩
  State := State E
  initial zs := initState x0 zs
  query s := (0, queryPoint cfg s)
  update := update cfg (Module.finrank ℝ E)
  output s := s.x

end LongTails.Algorithms.GatedPerturbedEscape
