import LongTails.Algorithms.GuardedHessianTransport
import LongTails.Algorithms.SplitRobustAcceleration
import LongTails.Proofs.Clipping

open MeasureTheory

namespace LongTails.Algorithms.HystereticHessianTransport

open LongTails.Setups.GeneralizedAffineHessianVector

structure Config where
  macros : ℕ
  epoch : ℕ
  resetBatch : ℕ
  pilotBatch : ℕ
  groups : ℕ
  transportBatch : ℕ
  radius : ℝ
  accuracy : ℝ
  guardThreshold : ℝ
  fineStep : ℝ
  coarseCap : ℝ
  clipThreshold : ℝ

def pilotCalls (c : Config) : ℕ := (c.groups + 1) * (c.pilotBatch + 1)

def resetCalls (c : Config) : ℕ := (c.groups + 1) * (c.resetBatch + 1)

def macroCalls (c : Config) : ℕ :=
  resetCalls c + (c.epoch + 2) * pilotCalls c + (c.epoch + 1) * (c.transportBatch + 1)

def trialCalls (c : Config) : ℕ := (c.macros + 1) * macroCalls c

inductive Phase (p : Params) (c : Config) where
  | gradient (refresh : Bool) (group : Fin (c.groups + 1)) (index : ℕ)
      (sum : Space p) (values : Fin (c.groups + 1) → Space p)
  | transport (index : ℕ) (sum : Space p)
  | padding

structure State (p : Params) (c : Config) where
  point : Space p
  estimate : Space p
  move : Space p
  inner : ℕ
  slot : ℕ
  fine : Bool
  active : Bool
  success : Bool
  phase : Phase p c

noncomputable def fineDisplacement (p : Params) (c : Config) (s : State p c) : Space p :=
  -(c.fineStep • (‖s.estimate‖⁻¹ • s.estimate))

noncomputable def coarseDisplacement (p : Params) (c : Config) (v : Space p) : Space p :=
  -((min c.coarseCap (‖v‖ / (64 * (p.L0 + p.L1 * ‖v‖)))) • (‖v‖⁻¹ • v))

noncomputable def beginFineStep (p : Params) (c : Config) (s : State p c) : State p c :=
  if ‖s.estimate‖ ≤ c.accuracy / 2 then
    { s with active := false, success := true, phase := .padding }
  else { s with move := fineDisplacement p c s, phase := .transport 0 0 }

noncomputable def finishPilot (p : Params) (c : Config) (s : State p c) (v : Space p) : State p c :=
  if c.guardThreshold < ‖v‖ then
    { s with point := p.x0, active := false, success := false, phase := .padding }
  else if s.fine then
    if 3 * c.radius ≤ ‖v‖ then { s with fine := false, phase := .padding }
    else if s.inner = 0 then { s with phase := .gradient true 0 0 0 (fun _ => 0) }
    else beginFineStep p c s
  else if ‖v‖ ≤ c.radius / 4 then { s with fine := true, phase := .padding }
  else { s with point := s.point + coarseDisplacement p c v, phase := .padding }

noncomputable def query (p : Params) (c : Config) (s : State p c) (u : ℝ) :
    Space p × Option (Space p) :=
  if s.active then
    match s.phase with
    | .transport _ _ => (s.point + u • s.move, some s.move)
    | .gradient _ _ _ _ _ => (s.point, none)
    | .padding => (p.x0, none)
  else (p.x0, none)

noncomputable def rawUpdate (p : Params) (c : Config) (s : State p c)
    (reply : Space p) : State p c :=
  if s.active then
    match s.phase with
    | .gradient refresh j i sum values =>
        let batch := if refresh then c.resetBatch else c.pilotBatch
        if i < batch then { s with phase := .gradient refresh j (i + 1) (sum + reply) values }
        else
          let values := Function.update values j (((batch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply))
          if hj : j.val + 1 < c.groups + 1 then
            { s with phase := .gradient refresh ⟨j.val + 1, hj⟩ 0 0 values }
          else
            let v := OracleTemplate.MultiplicativeRobustEstimator.medoid values
            if refresh then beginFineStep p c { s with estimate := v }
            else finishPilot p c s v
    | .transport i sum =>
        let sum := sum + OracleTemplate.clip c.clipThreshold reply
        if i < c.transportBatch then { s with phase := .transport (i + 1) sum }
        else
          { s with point := s.point + s.move
                   estimate := s.estimate + ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ • sum
                   inner := s.inner + 1
                   phase := if s.inner < c.epoch then .gradient false 0 0 0 (fun _ => 0)
                     else .padding }
    | .padding => s
  else s

noncomputable def update (p : Params) (c : Config) (s : State p c) (_u : ℝ)
    (reply : Space p) : State p c :=
  let next := rawUpdate p c s reply
  if s.slot + 1 < macroCalls c then { next with slot := s.slot + 1 }
  else { next with slot := 0, inner := 0, phase := .gradient false 0 0 0 (fun _ => 0) }

noncomputable def initial (p : Params) (c : Config) : State p c :=
  ⟨p.x0, 0, 0, 0, 0, false, true, false, .gradient false 0 0 0 (fun _ => 0)⟩

noncomputable def output (p : Params) (c : Config) (s : State p c) : Space p :=
  if s.success then s.point else p.x0

noncomputable def trial (p : Params) (c : Config) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) :=
  HeavyTailedFreshTape.algorithm ⟨Measure.dirac (), inferInstance⟩ GuardedHessianTransport.uniformLaw
    (fun _ : Unit => initial p c) (query p c) (update p c) (output p c)

noncomputable def boundedTrial (p : Params) (c : Config) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) :=
  OracleTemplate.SplitRobustAcceleration.capped (trial p c) (trialCalls c)

noncomputable def targetAccuracy (p : Params) : ℝ := p.ε / 2

noncomputable def tailPower (p : Params) : ℝ := p.p / (p.p - 1)

noncomputable def relativeNoise (p : Params) : ℝ := 1 + p.αg

noncomputable def noiseLevel (p : Params) : ℝ := 1 + p.σg / targetAccuracy p + p.αg

noncomputable def localRadius (p : Params) : ℝ := targetAccuracy p + p.σg / relativeNoise p

noncomputable def localScale (p : Params) : ℝ := p.L0 + p.σh + (p.L1 + p.αh) * localRadius p

noncomputable def epochCount (p : Params) : ℕ :=
  ⌊min ((noiseLevel p) ^ (tailPower p * (p.q - 1) / p.q))
    ((noiseLevel p / relativeNoise p) ^ tailPower p)⌋₊

noncomputable def macroCount (p : Params) : ℕ :=
  ⌈8388608 * p.Δ * localScale p / ((targetAccuracy p) ^ 2 * (epochCount p : ℝ)) +
    16384 * p.Δ * localScale p / (localRadius p) ^ 2⌉₊ + 2

noncomputable def guardRadius (p : Params) : ℝ :=
  16 * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + localRadius p)

noncomputable def logicalBlocks (p : Params) : ℕ := macroCount p * (2 * epochCount p + 3)

noncomputable def momentBound (p : Params) : ℝ := (2 + 4 * (logicalBlocks p : ℝ)) * (guardRadius p) ^ 2

noncomputable def confidence (p : Params) : ℝ :=
  1 + Real.log (1 + ((logicalBlocks p + macroCount p : ℕ) : ℝ) * momentBound p / (targetAccuracy p) ^ 2)

noncomputable def pilotBatchCount (p : Params) : ℕ := ⌈((2 : ℝ) ^ 24 * relativeNoise p) ^ tailPower p⌉₊ + 1

noncomputable def resetBatchCount (p : Params) : ℕ := ⌈((2 : ℝ) ^ 24 * noiseLevel p) ^ tailPower p⌉₊ + 1

noncomputable def transportBatchCount (p : Params) : ℕ :=
  ⌈256 * confidence p * (256 * (epochCount p : ℝ)) ^ (1 / (p.q - 1))⌉₊ + 1

noncomputable def groupCount (p : Params) : ℕ := ⌈2 * confidence p⌉₊ + 1

noncomputable def tunedConfig (p : Params) : Config where
  macros := macroCount p - 1
  epoch := epochCount p - 1
  resetBatch := resetBatchCount p - 1
  pilotBatch := pilotBatchCount p - 1
  groups := groupCount p - 1
  transportBatch := transportBatchCount p - 1
  radius := localRadius p
  accuracy := targetAccuracy p
  guardThreshold := 3 * guardRadius p / 2
  fineStep := targetAccuracy p / (524288 * localScale p)
  coarseCap := guardRadius p / (256 * (p.L0 + p.L1 * guardRadius p))
  clipThreshold := (targetAccuracy p / 256) * (transportBatchCount p : ℝ) / (128 * confidence p)

noncomputable def tunedAlgorithm (p : Params) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) := boundedTrial p (tunedConfig p)

end LongTails.Algorithms.HystereticHessianTransport
