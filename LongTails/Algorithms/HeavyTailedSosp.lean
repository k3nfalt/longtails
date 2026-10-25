import LongTails.Algorithms.HeavyTailedFreshTape
import LongTails.Algorithms.HeavyTailedEnergyProbe
import LongTails.Algorithms.HeavyTailedRayleighMedian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Algorithms.HeavyTailedSosp

open LongTails.Setups.HeavyTailedHessianVector

structure Config where
  cycles : ℕ
  epoch : ℕ
  resetBatch : ℕ
  transportBatch : ℕ
  probeSteps : ℕ
  repeats : ℕ
  meanBatch : ℕ
  groups : ℕ
  ncSegments : ℕ
  h : ℝ
  s : ℝ
  η : ℝ
  shift : ℝ
  γ : ℝ

abbrev Aux (p : Params) (c : Config) :=
  ℝ × Bool × (Fin p.d → Bool) × Fin (max 1 c.probeSteps)

noncomputable def auxLaw (p : Params) (c : Config) : ProbabilityMeasure (Aux p c) := by
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let : NeZero (max 1 c.probeSteps) := ⟨by omega⟩
  exact ⟨U.prod ((PMF.uniformOfFintype Bool).toMeasure.prod
    ((PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod
      (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure)), inferInstance⟩

inductive Resume (p : Params) where
  | startCycle
  | detect
  | ncRest (remaining : ℕ) (segment : Space p)

inductive Phase (p : Params) where
  | reset (index : ℕ) (sum : Space p) (after : Resume p)
  | transport (segment : Space p) (index : ℕ) (sum : Space p) (after : Resume p)
  | probeInit (trial : ℕ) (accepted : Option (Space p))
  | probe (trial : ℕ) (accepted : Option (Space p)) (state : HeavyTailedEnergyProbe.State p.d)
  | validate (trial : ℕ) (accepted : Option (Space p)) (candidate : Space p) (values : List ℝ)
  | ncInit (candidate : Space p)
  | done

structure State (p : Params) where
  point : Space p
  estimate : Space p
  virtualIndex : ℕ
  cycleIndex : ℕ
  target : ℕ
  selected : Space p
  phase : Phase p

noncomputable def startCycle (p : Params) (c : Config) (state : State p) : State p :=
  if state.cycleIndex < c.cycles then
    { state with
      selected := if state.cycleIndex = state.target then state.point else state.selected
      phase := .transport (-(c.h • (‖state.estimate‖⁻¹ • state.estimate))) 0 0 .detect }
  else { state with phase := .done }

noncomputable def resume (p : Params) (c : Config) (state : State p) (after : Resume p) : State p :=
  match after with
  | .startCycle => startCycle p c state
  | .detect => { state with phase := .probeInit 0 none }
  | .ncRest remaining segment =>
    if remaining = 0 then startCycle p c { state with cycleIndex := state.cycleIndex + 1 }
    else { state with phase := .transport segment 0 0 (.ncRest (remaining - 1) segment) }

noncomputable def completeTransport (p : Params) (c : Config) (state : State p)
    (segment sum : Space p) (after : Resume p) : State p :=
  let next := { state with
    point := state.point + segment
    estimate := state.estimate + ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ • sum
    virtualIndex := state.virtualIndex + 1 }
  if next.virtualIndex % max 1 c.epoch = 0 then
    { next with phase := .reset 0 0 after }
  else resume p c next after

noncomputable def transportReply (p : Params) (c : Config) (state : State p)
    (segment : Space p) (index : ℕ) (sum reply : Space p) (after : Resume p) : State p :=
  if index + 1 < max 1 c.transportBatch then
    { state with phase := .transport segment (index + 1) (sum + reply) after }
  else completeTransport p c state segment (sum + reply) after

noncomputable def signedSegment (p : Params) (c : Config) (a : Aux p c)
    (v : Space p) : Space p :=
  ((if a.2.1 then (1 : ℝ) else -1) * c.s / (max 1 c.ncSegments : ℕ)) • v

noncomputable def query (p : Params) (c : Config) (state : State p) (a : Aux p c) :
    Space p × Option (Space p) :=
  match state.phase with
  | .reset .. => (state.point, none)
  | .transport segment .. => (state.point + a.1 • segment, some segment)
  | .probeInit .. => (state.point, some (HeavyTailedEnergyProbe.initialVector a.2.2.1))
  | .probe _ _ probe => (state.point, some probe.vector)
  | .validate _ _ candidate _ => (state.point, some candidate)
  | .ncInit candidate =>
      let segment := signedSegment p c a candidate
      (state.point + a.1 • segment, some segment)
  | .done => (state.point, none)

noncomputable def probeReply (p : Params) (c : Config) (state : State p)
    (trial : ℕ) (accepted : Option (Space p)) (probe : HeavyTailedEnergyProbe.State p.d)
    (reply : Space p) : State p :=
  let next := HeavyTailedEnergyProbe.step c.shift c.η probe reply
  if next.index < max 1 c.probeSteps then
    { state with phase := .probe trial accepted next }
  else { state with phase := .validate trial accepted next.selected [] }

noncomputable def update (p : Params) (c : Config) (state : State p)
    (a : Aux p c) (reply : Space p) : State p :=
  match state.phase with
  | .reset index sum after =>
    if index + 1 < max 1 c.resetBatch then
      { state with phase := .reset (index + 1) (sum + reply) after }
    else resume p c { state with estimate := ((max 1 c.resetBatch : ℕ) : ℝ)⁻¹ • (sum + reply) } after
  | .transport segment index sum after => transportReply p c state segment index sum reply after
  | .probeInit trial accepted => probeReply p c state trial accepted
      (HeavyTailedEnergyProbe.initialState a.2.2.1 a.2.2.2.val) reply
  | .probe trial accepted probe => probeReply p c state trial accepted probe reply
  | .validate trial accepted candidate values =>
    let next := ⟪candidate, reply⟫ :: values
    if next.length < max 1 c.meanBatch * max 1 c.groups then
      { state with phase := .validate trial accepted candidate next }
    else
      let accepted := if HeavyTailedRayleighMedian.output (max 1 c.meanBatch) (max 1 c.groups)
          next.reverse ≤ -2 * c.γ then accepted.or (some candidate) else accepted
      if trial + 1 < max 1 c.repeats then
        { state with phase := .probeInit (trial + 1) accepted }
      else match accepted with
        | none => startCycle p c { state with cycleIndex := state.cycleIndex + 1 }
        | some v => { state with phase := .ncInit v }
  | .ncInit candidate =>
    let segment := signedSegment p c a candidate
    transportReply p c state segment 0 0 reply (.ncRest (max 1 c.ncSegments - 1) segment)
  | .done => state

noncomputable def initial (p : Params) (target : ℕ) : State p :=
  { point := p.x0
    estimate := 0
    virtualIndex := 0
    cycleIndex := 0
    target := target
    selected := p.x0
    phase := .reset 0 0 .startCycle }

noncomputable def algorithm (p : Params) (c : Config) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) := by
  let : NeZero (max 1 c.cycles) := ⟨by omega⟩
  exact HeavyTailedFreshTape.algorithm
    ⟨(PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure, inferInstance⟩ (auxLaw p c)
    (fun target => initial p target.val) (query p c) (update p c) (fun state => state.selected)

end LongTails.Algorithms.HeavyTailedSosp
