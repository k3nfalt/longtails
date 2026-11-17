import LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
import LongTails.Algorithms.DashaCyclic
import Mathlib.Probability.Distributions.Uniform

namespace LongTails.Algorithms.DashaScaling

open MeasureTheory
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex

structure Choice (p : Params) where
  block : Fin p.d
  precision : ℕ

noncomputable def variance (p : Params) (c : Choice p) : ℝ :=
  (1 + 2 / (4 : ℝ) ^ c.precision) * DashaCyclic.multiplier c.block - 1

noncomputable def denominator (p : Params) (c : Choice p) : ℝ :=
  min p.L p.Lhat + p.Lhat * Real.sqrt (variance p c * (2 * variance p c + 1) / p.n)

noncomputable def stepSize (p : Params) (c : Choice p) : ℝ := 1 / (8 * denominator p c)

noncomputable def momentum (p : Params) (c : Choice p) : ℝ := 1 / (2 * variance p c + 1)

noncomputable def spacing (p : Params) (c : Choice p) : ℝ :=
  p.ε * Real.sqrt ((p.n : ℝ) / (p.d * (variance p c + 1))) / 16

noncomputable def iterations (p : Params) (c : Choice p) : ℕ+ :=
  ⟨1 + ⌈32 * p.Δ * denominator p c / p.ε ^ 2⌉₊, by omega⟩

abbrev WorkerSample (p : Params) := DashaCyclic.Seed p.d
abbrev Sample (p : Params) := Fin p.n → WorkerSample p

noncomputable def sampleLaw (p : Params) : ProbabilityMeasure (Sample p) :=
  ⟨Measure.pi (fun _ : Fin p.n => (DashaCyclic.law p.d : Measure _)), inferInstance⟩

structure Iterate (p : Params) where
  point : Point p
  localGradient : Fin p.n → Point p
  localCode : Fin p.n → Fin p.d → ℤ

noncomputable def estimate (p : Params) (c : Choice p) (s : Iterate p) : Point p :=
  (1 / (p.n : ℝ)) • DashaQuantization.reconstruct (spacing p c) (fun j => ∑ i, s.localCode i j)

noncomputable def initialIterate (p : Params) (c : Choice p) (f : Functions p)
    (seed : Sample p) : Iterate p where
  point := p.x0
  localGradient i := gradient (f i) p.x0
  localCode i := DashaQuantization.indices p.d false (spacing p c) (gradient (f i) p.x0) (seed i).2

noncomputable def sparseInitialIterate (p : Params) (c initializer : Choice p) (f : Functions p)
    (seed : Sample p) : Iterate p where
  point := p.x0
  localGradient i := gradient (f i) p.x0
  localCode i := DashaCyclic.compressedIndex initializer.block (seed i).1 initializer.precision
    (spacing p c) (gradient (f i) p.x0) (seed i).2

noncomputable def initialPenalty (p : Params) (c initializer : Choice p) : ℝ :=
  (4 * variance p c + 1) * variance p initializer * p.G ^ 2 / p.n

noncomputable def sparseIterations (p : Params) (c initializer : Choice p) : ℕ+ :=
  ⟨1 + ⌈(32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2⌉₊, by omega⟩

noncomputable def nextIterate (p : Params) (c : Choice p) (f : Functions p)
    (s : Iterate p) (seed : Sample p) : Iterate p :=
  let xnext := s.point - stepSize p c • estimate p c s
  let hnext := fun i => gradient (f i) xnext
  { point := xnext
    localGradient := hnext
    localCode := fun i j => s.localCode i j + DashaCyclic.compressedIndex c.block (seed i).1
      c.precision (spacing p c)
      (hnext i - s.localGradient i - momentum p c •
        (DashaQuantization.reconstruct (spacing p c) (s.localCode i) - s.localGradient i))
      (seed i).2 j }

noncomputable def trajectory (p : Params) (c : Choice p) (f : Functions p)
    (seed : ℕ → Sample p) : ℕ → Iterate p
  | 0 => initialIterate p c f (seed 0)
  | k + 1 => nextIterate p c f (trajectory p c f seed k) (seed (k + 1))

noncomputable def sparseTrajectory (p : Params) (c initializer : Choice p) (f : Functions p)
    (seed : ℕ → Sample p) : ℕ → Iterate p
  | 0 => sparseInitialIterate p c initializer f (seed 0)
  | k + 1 => nextIterate p c f (sparseTrajectory p c initializer f seed k) (seed (k + 1))

noncomputable def sparseOutput (p : Params) (c initializer : Choice p) (f : Functions p)
    (seed : Fin (sparseIterations p c initializer) × (ℕ → Sample p)) : Point p :=
  (sparseTrajectory p c initializer f seed.2 seed.1.val).point

noncomputable def sparseSeedLaw (p : Params) (c initializer : Choice p) :
    ProbabilityMeasure (Fin (sparseIterations p c initializer) × (ℕ → Sample p)) :=
  ⟨(PMF.uniformOfFintype (Fin (sparseIterations p c initializer))).toMeasure.prod
    (Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)), inferInstance⟩

noncomputable def output (p : Params) (c : Choice p) (f : Functions p)
    (seed : Fin (iterations p c) × (ℕ → Sample p)) : Point p :=
  (trajectory p c f seed.2 seed.1.val).point

noncomputable def seedLaw (p : Params) (c : Choice p) :
    ProbabilityMeasure (Fin (iterations p c) × (ℕ → Sample p)) :=
  ⟨(PMF.uniformOfFintype (Fin (iterations p c))).toMeasure.prod
    (Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)), inferInstance⟩

abbrev Reduced (p : Params) := Point p × (Fin p.n → Fin p.d → ℤ)

noncomputable def lift (p : Params) (f : Functions p) (s : Reduced p) : Iterate p where
  point := s.1
  localGradient i := gradient (f i) s.1
  localCode := s.2

def reduce (p : Params) (s : Iterate p) : Reduced p := (s.point, s.localCode)

noncomputable def reducedStep (p : Params) (c : Choice p) (f : Functions p)
    (s : Reduced p) (seed : Sample p) : Reduced p :=
  reduce p (nextIterate p c f (lift p f s) seed)

noncomputable def initialReduced (p : Params) (c : Choice p) (f : Functions p)
    (seed : Sample p) : Reduced p := reduce p (initialIterate p c f seed)

noncomputable def idle (p : Params) :
    DistributedTemplate.Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) (p.n + 1) where
  clock _ := 0
  timer _ := 1
  State := Unit
  root := 0
  initial _ _ := ()
  query _ _ _ := (.advance 0, ())
  update _ _ _ _ := ()
  output _ := p.x0

end LongTails.Algorithms.DashaScaling
