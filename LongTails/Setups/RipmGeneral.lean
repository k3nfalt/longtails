import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Setups.RipmGeneral

noncomputable section

namespace Core

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Problem (d m : ℕ) where
  Sample : Type
  [sampleSpace : MeasurableSpace Sample]
  law : ProbabilityMeasure Sample
  component : Sample → Vec d → ℝ
  grad : Sample → Vec d → Vec d
  average : Vec d → ℝ
  regularizers : Fin m → Vec d → ℝ

attribute [instance] Problem.sampleSpace

def meanGradient {d m : ℕ} (I : Problem d m) (x : Vec d) : Vec d :=
  ∫ i, I.grad i x ∂(I.law : Measure I.Sample)

def regularizer {d m : ℕ} (I : Problem d m) (x : Vec d) : ℝ :=
  ∑ j, I.regularizers j x

def objective {d m : ℕ} (I : Problem d m) (x : Vec d) : ℝ :=
  I.average x + regularizer I x

def solutionSet {d m : ℕ} (I : Problem d m) : Set (Vec d) :=
  {x | IsMinOn (objective I) Set.univ x}

def distanceSq {d m : ℕ} (I : Problem d m) (x : Vec d) : ℝ :=
  Metric.infDist x (solutionSet I) ^ 2

def proxObjective {d : ℕ} (q : Vec d → ℝ) (a : ℝ) (y u : Vec d) : ℝ :=
  a * q u + ‖u - y‖ ^ 2 / 2

def prox {d : ℕ} (q : Vec d → ℝ) (a : ℝ) (y : Vec d) : Vec d :=
  by
    classical
    exact if h : ∃ u, IsMinOn (proxObjective q a y) Set.univ u then Classical.choose h else 0

structure SourceAssumptions {d m : ℕ} (I : Problem d m)
    (L Lg : ℝ) (xs : Vec d) (sigmaSq : ℝ) : Prop where
  countPos : 0 < m
  smoothPos : 0 < L
  regularizerNonneg : 0 ≤ Lg
  componentConvex : ∀ i, ConvexOn ℝ Set.univ (I.component i)
  componentGradient : ∀ i x, HasGradientAt (I.component i) (I.grad i x) x
  componentSmooth : ∀ i x y, ‖I.grad i x - I.grad i y‖ ≤ L * ‖x - y‖
  componentMeasurable : ∀ x, Measurable (fun i => I.component i x)
  componentIntegrable : ∀ x, Integrable (fun i => I.component i x) (I.law : Measure I.Sample)
  averageEq : ∀ x, I.average x = ∫ i, I.component i x ∂(I.law : Measure I.Sample)
  gradientMeasurable : Measurable (fun z : I.Sample × Vec d => I.grad z.1 z.2)
  regularizerConvex : ∀ j, ConvexOn ℝ Set.univ (I.regularizers j)
  regularizerLipschitz : ∀ j x y, |I.regularizers j x - I.regularizers j y| ≤ Lg * ‖x - y‖
  minimizer : IsMinOn (objective I) Set.univ xs
  solutionMoment : ∃ z, IsMinOn (objective I) Set.univ z ∧
    Integrable (fun i => ‖I.grad i z‖ ^ 2) (I.law : Measure I.Sample) ∧
    (∫ i, ‖I.grad i z‖ ^ 2 ∂(I.law : Measure I.Sample)) = sigmaSq

def trajectory {d m : ℕ} {Ω : Type*} (I : Problem d m) (eta : ℝ) (x0 : Vec d)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m) : ℕ → Ω → Vec d
  | 0, _ => x0
  | t + 1, omega =>
    prox (I.regularizers (j t omega)) (eta * m)
      (trajectory I eta x0 i j t omega - eta • I.grad (i t omega) (trajectory I eta x0 i j t omega))

abbrev iterateHistory {d m : ℕ} {Ω : Type*} (I : Problem d m) (eta : ℝ) (x0 : Vec d)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun omega (s : Fin (t + 1)) => trajectory I eta x0 i j s omega) inferInstance

def uniformMeasure (m : ℕ) (hm : 0 < m) : ProbabilityMeasure (Fin m) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact ⟨(PMF.uniformOfFintype (Fin m)).toMeasure, inferInstance⟩

def Sampling {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (I : Problem d m)
    (P : ProbabilityMeasure Ω) (eta : ℝ) (x0 : Vec d)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m) : Prop :=
  LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID i
      (I.law : Measure I.Sample) (P : Measure Ω) ∧
  ∀ t, Measurable (j t) ∧
    Indep (MeasurableSpace.comap (i t) inferInstance) (iterateHistory I eta x0 i j t)
      (P : Measure Ω) ∧
    Indep (MeasurableSpace.comap (j t) inferInstance) (iterateHistory I eta x0 i j t)
      (P : Measure Ω) ∧
    ∃ hm : 0 < m, (P : Measure Ω).map (j t) = (uniformMeasure m hm : Measure (Fin m))

def weight (T : ℕ) (mu : ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => weight T mu t * ((T - t : ℕ) + 1) / ((T - t : ℕ) + mu)

def mixing (T : ℕ) (mu : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 else ((T - t : ℕ) + 1 + mu) / ((T - t : ℕ) + 2)

def anchor {d : ℕ} {Ω : Type*} (T : ℕ) (mu : ℝ) (xs : Vec d)
    (x : ℕ → Ω → Vec d) : ℕ → Ω → Vec d
  | 0, _ => xs
  | t + 1, omega =>
    (1 - mixing T mu (t + 1)) • x (t + 1) omega +
      mixing T mu (t + 1) • anchor T mu xs x t omega

structure Public where
  d : ℕ
  m : ℕ
  x0 : Vec d
  eta : ℝ

structure State (d : ℕ) where
  point : Vec d
  work : Vec d
  proximalPhase : Bool

def method (p : Public) : OracleTemplate.Algorithm (ℝ × Vec p.d) (Vec p.d) (Vec p.d) 2 where
  State := State p.d
  initial := fun _ => ⟨p.x0, p.x0, false⟩
  query := fun s => if s.proximalPhase then (1, (p.eta * p.m, s.work)) else (0, (0, s.point))
  update := fun s y => if s.proximalPhase then ⟨y, y, false⟩
    else ⟨s.point, s.point - p.eta • y, true⟩
  output := fun s => s.point

def OracleExact {d m : ℕ} (I : Problem d m)
    (O : OracleTemplate.Oracle (ℝ × Vec d) (Vec d) 2)
    (decodeI : (k : ℕ) → O.Seed k → I.Sample)
    (decodeJ : (k : ℕ) → O.Seed k → Fin m) : Prop :=
  (∀ k, Measurable (decodeI k) ∧ Measurable (decodeJ k)) ∧
  ∀ history q seed,
    (q.1 = 0 → O.answer history q seed = I.grad (decodeI history.length seed) q.2.2) ∧
    (q.1 = 1 → 0 < q.2.1 →
      O.answer history q seed = prox (I.regularizers (decodeJ history.length seed)) q.2.1 q.2.2)

def OracleSamples {d m : ℕ} (I : Problem d m)
    (O : OracleTemplate.Oracle (ℝ × Vec d) (Vec d) 2)
    (eta : ℝ) (x0 : Vec d)
    (decodeI : (k : ℕ) → O.Seed k → I.Sample)
    (decodeJ : (k : ℕ) → O.Seed k → Fin m) : Prop :=
  Sampling I O.law eta x0 (fun t omega => decodeI (2 * t) (omega (2 * t)))
    (fun t omega => decodeJ (2 * t + 1) (omega (2 * t + 1)))

end Core

structure Params where
  d : ℕ
  m : ℕ
  x0 : Core.Vec d
  xstar : Core.Vec d
  L : ℝ
  Lg : ℝ
  D2 : ℝ
  Delta : ℝ
  S : ℝ
  epsilon : ℝ
  C : ℝ

def valid (p : Params) : Prop :=
  0 < p.m ∧ 0 < p.L ∧ 0 ≤ p.Lg ∧ 0 ≤ p.D2 ∧ 0 ≤ p.Delta ∧
    0 ≤ p.S ∧ 0 < p.epsilon ∧ 4 < p.C

def boundScale (p : Params) : ℝ :=
  p.C * p.L * p.D2 + 2 * p.Delta +
    (4 * p.S / (p.C - 2) + 16 * (p.m : ℝ) ^ 2 * p.Lg ^ 2 / p.C) / p.L

def horizon (p : Params) : ℕ :=
  ⌈(64 * (1 + 3 * boundScale p / p.epsilon) *
    (1 + Real.log (1 + 3 * boundScale p / p.epsilon))) ^ 2⌉₊

def step (p : Params) : ℝ :=
  1 / (p.C * p.L * Real.sqrt (horizon p))

def publicInput (p : Params) : Core.Public :=
  ⟨p.d, p.m, p.x0, step p⟩

def admissible (p : Params) (I : Core.Problem p.d p.m)
    (O : OracleTemplate.Oracle (ℝ × Core.Vec p.d) (Core.Vec p.d) 2) : Prop :=
  ∃ sigmaSq decodeI decodeJ,
    Core.SourceAssumptions I p.L p.Lg p.xstar sigmaSq ∧ sigmaSq ≤ p.S ∧
    ‖p.x0 - p.xstar‖ ^ 2 ≤ p.D2 ∧ Core.objective I p.x0 - Core.objective I p.xstar ≤ p.Delta ∧
    Core.OracleExact I O decodeI decodeJ ∧ Core.OracleSamples I O (step p) p.x0 decodeI decodeJ

def spec : OracleTemplate.Setup where
  numOracles := 2
  Params := Params
  Public := Core.Public
  Instance p := Core.Problem p.d p.m
  Query p := ℝ × Core.Vec p.d
  Reply p := Core.Vec p.d
  Output p := Core.Vec p.d
  publicInput := publicInput
  valid := valid
  admissible := admissible
  successful := fun p I output P =>
    Measurable output ∧
    Integrable (fun omega => Core.objective I (output omega) - Core.objective I p.xstar)
      (P : Measure _) ∧
    (∫ omega, Core.objective I (output omega) - Core.objective I p.xstar ∂(P : Measure _)) ≤ p.epsilon
  allowedAlgorithm := fun p A => A = Core.method p

end

end LongTails.Setups.RipmGeneral
