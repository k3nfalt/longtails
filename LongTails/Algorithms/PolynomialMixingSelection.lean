import LongTails.Setups.PolynomialMixingSubgradient
import LongTails.Algorithms.StochasticEnvelopeProgram
import LongTails.Algorithms.QueryLayers
import LongTails.Algorithms.RobustGradientEstimator
import LongTails.Algorithms.MatrixGeneralizedZO

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Algorithms.PolynomialMixingSelection

open LongTails.Setups.PolynomialMixingSubgradient
open OracleTemplate LongTails.Algorithms.StochasticEnvelopeProgram

noncomputable section

abbrev Point (q : Params) := ↥(Domain q)

def origin (q : Params) : Point q :=
  ⟨0, by simpa only [Domain, Metric.mem_closedBall, dist_self] using q.hR⟩

def project (q : Params) (x : Space q) : Point q :=
  ⟨clip q.R x, by simpa [Domain] using norm_clip_le q.hR x⟩

structure Schedule where
  samples : ℕ
  trials : ℕ
  innerSkip : ℕ
  outerSkip : ℕ

def schedule (q : Params) : Schedule :=
  let n := ⌈(32768 * q.G * q.R / q.ε) ^ (q.p / (q.p - 1))⌉₊
  let k := ⌈8 * Real.log (8 / q.δ)⌉₊
  ⟨n, k, ⌈q.τ * (256 * (n : ℝ)) ^ (1 / q.β)⌉₊,
    ⌈q.τ * (4 * (k : ℝ) * (k + 1) / q.δ) ^ (1 / q.β)⌉₊⟩

abbrev Plan (q : Params) (U : Type) (n : ℕ) := QueryPlan (Point q) (Space q) U n

def spacedQuery (q : Params) (gap : ℕ) (x : Point q) : Plan q (Space q) (gap + 1) :=
  .ask x (fun r => QueryLayers.paddingPlan (origin q) r gap)

structure TrainState (q : Params) where
  x : Point q
  total : Space q
  energy : ℝ

def trainStep (q : Params) (s : TrainState q) (r : Space q) : TrainState q :=
  let energy := s.energy + ‖r‖ ^ 2
  ⟨project q (s.x.val - (2 * q.R / Real.sqrt energy) • r), s.total + s.x.val, energy⟩

def train (q : Params) (gap : ℕ) : (n : ℕ) → Plan q (TrainState q) ((gap + 1) * n)
  | 0 => .done ⟨origin q, 0, q.G ^ 2⟩
  | n + 1 => castPlan (Nat.add_comm _ _)
      ((train q gap n).bind (fun s => (spacedQuery q gap s.x).map (trainStep q s)))

def candidatePlan (q : Params) (c : Schedule) :
    Plan q (Point q) (c.outerSkip + (c.innerSkip + 1) * c.samples) :=
  QueryLayers.paddedPlan (origin q)
    ((train q c.innerSkip c.samples).map (fun s => project q ((c.samples : ℝ)⁻¹ • s.total))) c.outerSkip

def chordPoint (q : Params) (x : Point q) (n i : ℕ) : Point q :=
  project q (((i : ℝ) / n) • x.val)

def scorePlan (q : Params) (c : Schedule) (x : Point q) :
    Plan q ℝ (c.outerSkip + (c.innerSkip + 1) * c.samples) :=
  let samples := collectPlans c.samples fun i =>
    spacedQuery q c.innerSkip (chordPoint q x c.samples i.val)
  QueryLayers.paddedPlan (origin q) (samples.map
    (fun r => (c.samples : ℝ)⁻¹ * ∑ i, ⟪r i, x.val⟫)) c.outerSkip

def trialPlan (q : Params) (c : Schedule) :
    Plan q (Point q × ℝ) ((c.outerSkip + (c.innerSkip + 1) * c.samples) * (c.trials + 1)) :=
  (candidatePlan q c).bind (fun x =>
    (collectPlans c.trials (fun _ => scorePlan q c x)).map
      (fun r => (x, RobustGradient.pilotCenter (q.ε / 2) r)))

def output (q : Params) (c : Schedule) :
    Plan q (Point q) (((c.outerSkip + (c.innerSkip + 1) * c.samples) * (c.trials + 1)) * c.trials) :=
  (collectPlans c.trials (fun _ => trialPlan q c)).map
    (fun choices => MatrixGeneralizedZO.selectBest (origin q) (List.ofFn choices))

def method (q : Params) : Algorithm (Point q) (Space q) (Point q) :=
  QueryPlan.algorithm (⟨Measure.dirac (), inferInstance⟩ : ProbabilityMeasure Unit)
    (origin q) (origin q) _ (fun _ => output q (schedule q))

end

end LongTails.Algorithms.PolynomialMixingSelection
