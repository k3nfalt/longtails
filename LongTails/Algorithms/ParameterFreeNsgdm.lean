import LongTails.Setups.ParameterFreeHeavyTailedSmooth
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory

namespace LongTails.Algorithms.ParameterFreeNsgdm

open OracleTemplate
open LongTails.Setups.ParameterFreeHeavyTailedSmooth

def horizon (k : ℕ) : ℕ := 2 ^ k

def momentumCount (k : ℕ) : ℕ := 2 * k + 1

def stepCount (k : ℕ) : ℕ := 5 * k + 1

def candidates (k : ℕ) : ℕ := momentumCount k * stepCount k

noncomputable def momentum (k c : ℕ) : ℝ := Real.exp (-((c / stepCount k : ℕ) : ℝ) / 2)

noncomputable def stepSize (k c : ℕ) : ℝ := Real.exp ((k : ℝ) - ((c % stepCount k : ℕ) : ℝ) / 2)

instance (k : ℕ) : NeZero (horizon k) := ⟨by unfold horizon; positivity⟩

abbrev Seed := (k : ℕ) → Fin (candidates k) → Fin (horizon k)

noncomputable def seedLaw : Measure Seed :=
  Measure.infinitePi fun k => Measure.pi fun _ : Fin (candidates k) =>
    (PMF.uniformOfFintype (Fin (horizon k))).toMeasure

instance : IsProbabilityMeasure seedLaw := by
  unfold seedLaw; infer_instance

structure State (d : Public) where
  seed : Seed
  phase : ℕ
  cand : ℕ
  step : ℕ
  validating : Bool
  x : d.E
  m : d.E
  cands : ℕ → d.E
  acc : d.E
  bestNorm : ℝ
  best : d.E
  out : d.E

variable {d : Public}

noncomputable def initial (d : Public) (s : Seed) : State d :=
  ⟨s, 0, 0, 0, false, d.x0, 0, fun _ => d.x0, 0, 0, d.x0, d.x0⟩

def chosen (s : Seed) (k c : ℕ) : ℕ :=
  if h : c < candidates k then (s k ⟨c, h⟩).val else 0

noncomputable def query (s : State d) : d.E :=
  if s.validating then s.cands s.cand else s.x

noncomputable def move (k c : ℕ) (x m : d.E) : d.E := x - (stepSize k c / ‖m‖) • m

noncomputable def mix (k c : ℕ) (t : ℕ) (m r : d.E) : d.E :=
  if t = 0 then r else (1 - momentum k c) • m + momentum k c • r

noncomputable def runUpdate (d : Public) (s : State d) (r : d.E) : State d :=
  let m' := mix s.phase s.cand s.step s.m r
  let cands' := if s.step = chosen s.seed s.phase s.cand
    then Function.update s.cands s.cand s.x else s.cands
  if s.step + 1 < horizon s.phase then
    { s with step := s.step + 1, x := move s.phase s.cand s.x m', m := m', cands := cands' }
  else if s.cand + 1 < candidates s.phase then
    { s with cand := s.cand + 1, step := 0, x := d.x0, m := 0, cands := cands' }
  else
    { s with validating := true, cand := 0, step := 0, x := d.x0, m := 0, acc := 0, cands := cands' }

noncomputable def validateUpdate (d : Public) (s : State d) (r : d.E) : State d :=
  let acc' := s.acc + r
  if s.step + 1 < horizon s.phase then
    { s with step := s.step + 1, acc := acc' }
  else
    let v := ‖((horizon s.phase : ℕ) : ℝ)⁻¹ • acc'‖
    let improve := s.cand = 0 ∨ v < s.bestNorm
    let best' := if improve then s.cands s.cand else s.best
    let norm' := if improve then v else s.bestNorm
    if s.cand + 1 < candidates s.phase then
      { s with cand := s.cand + 1, step := 0, acc := 0, best := best', bestNorm := norm' }
    else
      { s with phase := s.phase + 1, cand := 0, step := 0, validating := false, x := d.x0, m := 0, acc := 0, best := best', bestNorm := norm', out := best' }

noncomputable def update (d : Public) (s : State d) (r : d.E) : State d :=
  if s.validating then validateUpdate d s r else runUpdate d s r

noncomputable def algorithm (d : Public) : Algorithm d.E d.E d.E where
  Seed := Seed
  law := ⟨seedLaw, inferInstance⟩
  State := State d
  initial := initial d
  query s := (0, query s)
  update := update d
  output := State.out

end LongTails.Algorithms.ParameterFreeNsgdm
