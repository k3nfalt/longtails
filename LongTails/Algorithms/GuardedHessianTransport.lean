import LongTails.Algorithms.HeavyTailedFreshTape
import LongTails.Algorithms.MultiplicativeRobustEstimator
import LongTails.Setups.GeneralizedAffineHessianVector
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory

namespace LongTails.Algorithms.GuardedHessianTransport

open LongTails.Setups.GeneralizedAffineHessianVector

structure Config where
  steps : ℕ
  epoch : ℕ
  resetBatch : ℕ
  guardBatch : ℕ
  groups : ℕ
  η : ℝ
  threshold : ℝ

inductive Phase (p : Params) (c : Config) where
  | reset (index : ℕ) (sum : Space p)
  | transport
  | guard (group : Fin (c.groups + 1)) (index : ℕ) (sum : Space p)
      (values : Fin (c.groups + 1) → Space p)
  | done

structure State (p : Params) (c : Config) where
  point : Space p
  estimate : Space p
  index : ℕ
  target : Fin (c.steps + 1)
  selected : Space p
  alive : Bool
  phase : Phase p c

noncomputable def displacement (p : Params) (c : Config) (s : State p c) : Space p :=
  -(c.η • (‖s.estimate‖⁻¹ • s.estimate))

noncomputable def beginStep (p : Params) (c : Config) (s : State p c) : State p c :=
  { s with selected := if s.index = s.target.val then s.point else s.selected
           phase := .transport }

noncomputable def nextStep (p : Params) (c : Config) (s : State p c) : State p c :=
  if s.index < c.steps then
    let next := { s with index := s.index + 1 }
    if next.index % (c.epoch + 1) = 0 then { next with phase := .reset 0 0 }
    else beginStep p c next
  else { s with phase := .done }

noncomputable def query (p : Params) (c : Config) (s : State p c) (u : ℝ) :
    Space p × Option (Space p) :=
  match s.phase with
  | .transport =>
      let v := if s.alive then displacement p c s else 0
      (s.point + u • v, some v)
  | _ => (s.point, none)

noncomputable def update (p : Params) (c : Config) (s : State p c) (_u : ℝ)
    (reply : Space p) : State p c :=
  match s.phase with
  | .reset i sum =>
      if i < c.resetBatch then { s with phase := .reset (i + 1) (sum + reply) }
      else beginStep p c { s with
        estimate := if s.alive then ((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply) else 0 }
  | .transport =>
      { s with
        point := if s.alive then s.point + displacement p c s else p.x0
        estimate := if s.alive then s.estimate + reply else 0
        phase := .guard 0 0 0 (fun _ => 0) }
  | .guard j i sum values =>
      if i < c.guardBatch then
        { s with phase := .guard j (i + 1) (sum + reply) values }
      else
        let values := Function.update values j
          (((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply))
        if hj : j.val + 1 < c.groups + 1 then
          { s with phase := .guard ⟨j.val + 1, hj⟩ 0 0 values }
        else
          let accepted := s.alive && decide
            (‖OracleTemplate.MultiplicativeRobustEstimator.medoid values‖ ≤ c.threshold)
          nextStep p c { s with
            alive := accepted
            point := if accepted then s.point else p.x0
            selected := if accepted then s.selected else p.x0 }
  | .done => s

noncomputable def uniformLaw : ProbabilityMeasure ℝ := by
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  exact ⟨U, inferInstance⟩

noncomputable def trial (p : Params) (c : Config) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) :=
  HeavyTailedFreshTape.algorithm
    ⟨(PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure, inferInstance⟩ uniformLaw
    (fun target => (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c))
    (query p c) (update p c) (fun s => if s.alive then s.selected else p.x0)

def trialCalls (c : Config) : ℕ :=
  (c.steps / (c.epoch + 1) + 1) * (c.resetBatch + 1) +
    (c.steps + 1) * (1 + (c.groups + 1) * (c.guardBatch + 1))

noncomputable def guardRadius (p : Params) : ℝ :=
  65536 * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε)

noncomputable def transportScale (p : Params) : ℝ :=
  p.L0 + p.L1 * guardRadius p + p.σh + p.αh * guardRadius p + p.ε / guardRadius p

noncomputable def batchCount (p : Params) : ℕ :=
  ⌈(65536 * (p.σg + p.αg * guardRadius p) / p.ε) ^ (p.p / (p.p - 1))⌉₊ + 1

noncomputable def stepSize (p : Params) : ℝ :=
  p.ε / (1048576 * transportScale p * (batchCount p : ℝ) ^ p.q⁻¹)

noncomputable def stepCount (p : Params) : ℕ :=
  ⌈1024 * p.Δ / (stepSize p * p.ε)⌉₊ + 1

noncomputable def guardBatchCount (p : Params) : ℕ :=
  ⌈(1048576 * (p.σg / guardRadius p + p.αg)) ^ (p.p / (p.p - 1))⌉₊ + 1

noncomputable def guardGroupCount (p : Params) : ℕ :=
  ⌈Real.log (128 * (stepCount p : ℝ)) / Real.log 2⌉₊ + 1

noncomputable def tunedConfig (p : Params) : Config where
  steps := stepCount p - 1
  epoch := batchCount p - 1
  resetBatch := batchCount p - 1
  guardBatch := guardBatchCount p - 1
  groups := guardGroupCount p - 1
  η := stepSize p
  threshold := 3 * guardRadius p / 2

noncomputable def bestEstimate {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (estimates : Fin (n + 1) → E) : Fin (n + 1) :=
  OracleTemplate.AdaptiveHeavyTailSimplex.minimumIndex (Nat.succ_pos n) (fun i => ‖estimates i‖)

end LongTails.Algorithms.GuardedHessianTransport
