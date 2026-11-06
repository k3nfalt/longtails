import LongTails.Algorithms.SampledQueryPlan
import LongTails.Algorithms.StochasticEqualityDirection
import LongTails.Algorithms.StochasticEnvelopeProgram
import LongTails.Algorithms.RobustGradientEstimator
import LongTails.Setups.StochasticRegularEqualities
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace LongTails.Algorithms.StochasticEquality

open OracleTemplate
open LongTails.Setups.StochasticRegularEqualities
open LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.StochasticEnvelopeProgram

noncomputable section

structure Config where
  gradientCap : ℝ
  constraintCap : ℝ
  step : ℝ
  restoreCap : ℝ
  restoreStep : ℝ
  restoreTolerance : ℝ
  validationTolerance : ℝ
  restoreSteps : ℕ+
  restoreBatch : ℕ+
  restoreGroups : ℕ+
  steps : ℕ+
  epoch : ℕ+
  resetBatch : ℕ+
  incrementBatch : ℕ+
  trials : ℕ+
  validationBatch : ℕ+
  validationGroups : ℕ+

noncomputable def positiveCeil (x : ℝ) : ℕ+ :=
  ⟨max 1 ⌈x⌉₊, by omega⟩

noncomputable def tuning (p : Public) : Config :=
  let S := 2 + p.Lf + p.Lc + p.LJ + p.ν + 1 / p.ν + p.Δ + p.C0 + p.Lnoise
  let ℓ := 1 + Real.log (S / p.ε)
  let B := positiveCeil (10 ^ 32 * S ^ 48 * p.σ ^ 2 / p.ε ^ 2)
  let q := positiveCeil (S ^ 2 * Real.sqrt (B : ℝ) / 10)
  { gradientCap := 4000 * S ^ 6, constraintCap := 1 / (10 * S ^ 7)
    step := 1 / (10 ^ 12 * S ^ 26)
    restoreCap := p.C0 + 1, restoreStep := 1 / (64 * S ^ 2)
    restoreTolerance := 1 / (10 ^ 8 * S ^ 9)
    validationTolerance := p.ε / (10 ^ 6 * S ^ 7)
    restoreSteps := positiveCeil (4096 * S ^ 4 * (1 + Real.log S))
    restoreBatch := positiveCeil (10 ^ 19 * S ^ 18 * p.σ ^ 2)
    restoreGroups := positiveCeil (100 * (1 + Real.log S))
    steps := positiveCeil (10 ^ 24 * S ^ 38 / p.ε ^ 2)
    epoch := q, resetBatch := B, incrementBatch := positiveCeil (100 * (q : ℝ) / S ^ 4)
    trials := positiveCeil (200 * ℓ)
    validationBatch := positiveCeil (10 ^ 15 * S ^ 14 * p.σ ^ 2 / p.ε ^ 2)
    validationGroups := positiveCeil (300 * ℓ) }

abbrev Plan (p : Public) (U : Type) (n : ℕ) := QueryPlan (Point p.d) (Reply p) U n

def pairedSample (p : Public) (x : Point p.d) : Plan p (Reply p) 2 :=
  .ask x fun v => .ask x fun _ => .done v

def pairedDifference (p : Public) (x y : Point p.d) : Plan p (Reply p) 2 :=
  .ask x fun v => .ask y fun w => .done (v - w)

def meanPlan (p : Public) (n : ℕ) (sample : Plan p (Reply p) 2) : Plan p (Reply p) (2 * n) :=
  (collectPlans n (fun _ => sample)).map (fun values => (n : ℝ)⁻¹ • ∑ i, values i)

def robustPlan (p : Public) (t : ℝ) (n k : ℕ) (x : Point p.d) :
    Plan p (Reply p) ((2 * n) * k) :=
  (collectPlans k (fun _ => meanPlan p n (pairedSample p x))).map fun values =>
    (RobustGradient.pilotCenter (2 * t) (fun i => (values i).1),
      RobustGradient.pilotCenter (2 * t) (fun i => (values i).2.1),
      RobustGradient.pilotCenter (2 * t) (fun i => (values i).2.2))

def clipReply (p : Public) (G M : ℝ) (v : Reply p) : Reply p :=
  (OracleTemplate.clip G v.1, OracleTemplate.clip M v.2.1, OracleTemplate.clip p.Lc v.2.2)

def restoreUpdate (p : Public) (cfg : Config) (x : Point p.d) (v : Reply p) : Point p.d :=
  x - cfg.restoreStep • (operatorEquiv p.d p.m (OracleTemplate.clip p.Lc v.2.2)
    (OracleTemplate.clip cfg.restoreCap v.2.1))

def restoreUnitCalls (cfg : Config) : ℕ := 2 * cfg.restoreBatch * cfg.restoreGroups

def restoreCalls (cfg : Config) : ℕ := slotCalls (fun _ => restoreUnitCalls cfg) cfg.restoreSteps 0

def restorePrefixPlan (p : Public) (cfg : Config) (n : ℕ) :
    Plan p (Point p.d) (slotCalls (fun _ => restoreUnitCalls cfg) n 0) :=
  slotPlan (fun _ => restoreUnitCalls cfg)
    (fun _ x => (robustPlan p cfg.restoreTolerance cfg.restoreBatch cfg.restoreGroups x).map
      (restoreUpdate p cfg x)) n 0 p.x0

def restorePlan (p : Public) (cfg : Config) : Plan p (Point p.d) (restoreCalls cfg) :=
  restorePrefixPlan p cfg cfg.restoreSteps

def restorationTrace {Ω : Type*} (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (offset n : ℕ) : Point p.d :=
  QueryPlan.sampledEval g (fun i => ξ (i / 2)) (restorePrefixPlan p cfg n) (2 * offset)

def restorationEstimate {Ω : Type*} (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (offset n : ℕ) : Reply p :=
  QueryPlan.sampledEval g (fun i => ξ (i / 2))
    (robustPlan p cfg.restoreTolerance cfg.restoreBatch cfg.restoreGroups
      (restorationTrace p cfg g ξ offset n))
    (2 * offset + slotCalls (fun _ => restoreUnitCalls cfg) n 0)

structure TrainingState (p : Public) where
  point : Point p.d
  previous : Point p.d
  estimate : Reply p
  selected : Point p.d

def batchSize (cfg : Config) (k : ℕ) : ℕ :=
  if k % cfg.epoch = 0 then cfg.resetBatch else cfg.incrementBatch

def estimatorPlan (p : Public) (cfg : Config) (k : ℕ) (s : TrainingState p) :
    Plan p (Reply p) (2 * batchSize cfg k) := by
  classical
  exact if h : k % cfg.epoch = 0 then
    castPlan (by simp [batchSize, h]) (meanPlan p cfg.resetBatch (pairedSample p s.point))
  else castPlan (by simp [batchSize, h])
    ((meanPlan p cfg.incrementBatch (pairedDifference p s.point s.previous)).map
      (fun v => s.estimate + v))

def trainingUpdate (p : Public) (cfg : Config) (k index : ℕ) (s : TrainingState p)
    (v : Reply p) : TrainingState p :=
  let estimate := clipReply p cfg.gradientCap cfg.constraintCap v
  { point := s.point + cfg.step • StochasticEqualityDirection.direction p.ν
      (operatorEquiv p.d p.m estimate.2.2) estimate.1 estimate.2.1
    previous := s.point, estimate := estimate
    selected := if k = index then s.point else s.selected }

def trainingCalls (cfg : Config) : ℕ := slotCalls (fun k => 2 * batchSize cfg k) cfg.steps 0

def trainingPrefixPlan (p : Public) (cfg : Config) (index n : ℕ) (x : Point p.d) :
    Plan p (TrainingState p) (slotCalls (fun k => 2 * batchSize cfg k) n 0) :=
  slotPlan (fun k => 2 * batchSize cfg k)
    (fun k s => (estimatorPlan p cfg k s).map (trainingUpdate p cfg k index s))
    n 0 { point := x, previous := x, estimate := 0, selected := x }

def trainingPlan (p : Public) (cfg : Config) (index : Fin cfg.steps) (x : Point p.d) :
    Plan p (Point p.d) (trainingCalls cfg) :=
  (trainingPrefixPlan p cfg index cfg.steps x).map TrainingState.selected

def trainingTrace {Ω : Type*} (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (x : Point p.d) (offset n : ℕ) : TrainingState p :=
  QueryPlan.sampledEval g (fun i => ξ (i / 2)) (trainingPrefixPlan p cfg 0 n x) (2 * offset)

def batchOffset (cfg : Config) (offset n : ℕ) : ℕ :=
  offset + ∑ k ∈ Finset.range n, batchSize cfg k

def validate (p : Public) (cfg : Config) (x : Point p.d) (v : Reply p) : Option (Point p.d × Point p.m) := by
  classical
  let J := operatorEquiv p.d p.m (OracleTemplate.clip p.Lc v.2.2)
  let multiplier := StochasticEqualityDirection.thresholdedMultiplier p.ν J
    (OracleTemplate.clip cfg.gradientCap v.1)
  exact if StochasticEqualityDirection.regular (p.ν / 2) J ∧
      ‖v.1 + J multiplier‖ ^ 2 + ‖v.2.1‖ ^ 2 ≤ p.ε ^ 2 / 16 then
    some (x, multiplier) else none

def validationCalls (cfg : Config) : ℕ := 2 * cfg.validationBatch * cfg.validationGroups

def trialCalls (cfg : Config) : ℕ := validationCalls cfg + trainingCalls cfg + restoreCalls cfg

def trialSamples (cfg : Config) : ℕ :=
  cfg.validationBatch * cfg.validationGroups + (∑ k ∈ Finset.range cfg.steps, batchSize cfg k) +
    cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps

def trialPlan (p : Public) (cfg : Config) (index : Fin cfg.steps) :
    Plan p (Option (Point p.d × Point p.m)) (trialCalls cfg) :=
  (restorePlan p cfg).bind fun x => (trainingPlan p cfg index x).bind fun y =>
    (robustPlan p cfg.validationTolerance cfg.validationBatch cfg.validationGroups y).map
      (validate p cfg y)

def trainingOffset (cfg : Config) (offset : ℕ) : ℕ :=
  offset + cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps

def validationOffset (cfg : Config) (offset : ℕ) : ℕ :=
  batchOffset cfg (trainingOffset cfg offset) cfg.steps

def trialPoint {Ω : Type*} (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (index : Fin cfg.steps) (offset : ℕ) : Point p.d :=
  QueryPlan.sampledEval g (fun i => ξ (i / 2))
    (trainingPlan p cfg index (restorationTrace p cfg g ξ offset cfg.restoreSteps))
    (2 * trainingOffset cfg offset)

def trialEstimate {Ω : Type*} (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (ξ : ℕ → Ω) (index : Fin cfg.steps) (offset : ℕ) : Reply p :=
  QueryPlan.sampledEval g (fun i => ξ (i / 2))
    (robustPlan p cfg.validationTolerance cfg.validationBatch cfg.validationGroups
      (trialPoint p cfg g ξ index offset)) (2 * validationOffset cfg offset)

def firstAccepted {p : Public} (fallback : Point p.d × Point p.m) : List (Option (Point p.d × Point p.m)) →
    Point p.d × Point p.m
  | [] => fallback
  | none :: rest => firstAccepted fallback rest
  | some value :: _ => value

abbrev Seed (cfg : Config) := Fin cfg.trials → Fin cfg.steps

def seedLaw (cfg : Config) : MeasureTheory.ProbabilityMeasure (Seed cfg) :=
  ⟨MeasureTheory.Measure.pi (fun _ : Fin cfg.trials => (PMF.uniformOfFintype (Fin cfg.steps)).toMeasure), inferInstance⟩

def calls (cfg : Config) : ℕ := trialCalls cfg * cfg.trials

def plan (p : Public) (cfg : Config) (seed : Seed cfg) :
    Plan p (Point p.d × Point p.m) (calls cfg) :=
  (QueryPlan.traverse cfg.trials (fun i => trialPlan p cfg (seed i))).map (firstAccepted (p.x0, 0))

def algorithm (p : Public) : Algorithm (Point p.d) (Reply p) (Point p.d × Point p.m) :=
  let cfg := tuning p
  QueryPlan.algorithm (seedLaw cfg)
    p.x0 (p.x0, 0) (calls cfg) (plan p cfg)

def output (p : Public) (oracle : Oracle (Point p.d) (Reply p)) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → oracle.Seed k) : Point p.d × Point p.m :=
  execute oracle (algorithm p) (fun _ => K) seed ξ

end

end LongTails.Algorithms.StochasticEquality
