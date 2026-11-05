import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import LongTails.Template

open MeasureTheory

namespace LongTails.Setups.WassersteinSmoothComposite

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

instance (d : ℕ) : MeasurableSpace (Space d) := borel (Space d)

instance (d : ℕ) : BorelSpace (Space d) := ⟨rfl⟩

structure Distribution (d : ℕ) where
  law : ProbabilityMeasure (Space d)
  secondMoment : Integrable (fun x => ‖x‖ ^ 2) (law : Measure (Space d))

structure Coupling {d : ℕ} (μ ν : Distribution d) where
  law : ProbabilityMeasure (Space d × Space d)
  first : (law : Measure (Space d × Space d)).map Prod.fst = μ.law
  second : (law : Measure (Space d × Space d)).map Prod.snd = ν.law
  finiteCost : Integrable (fun z => ‖z.1 - z.2‖ ^ 2)
    (law : Measure (Space d × Space d))

noncomputable def couplingCost {d : ℕ} {μ ν : Distribution d} (π : Coupling μ ν) : ℝ :=
  ∫ z, ‖z.1 - z.2‖ ^ 2 ∂(π.law : Measure (Space d × Space d))

noncomputable def squaredDistance {d : ℕ} (μ ν : Distribution d) : ℝ :=
  sInf (Set.range (couplingCost (μ := μ) (ν := ν)))

structure Transport {d : ℕ} (μ ν : Distribution d) where
  toFun : Space d → Space d
  measurable : Measurable toFun
  pushforward : (μ.law : Measure (Space d)).map toFun = ν.law
  finiteCost : Integrable (fun x => ‖x - toFun x‖ ^ 2) (μ.law : Measure (Space d))

structure OptimalTransport {d : ℕ} (μ ν : Distribution d) extends Transport μ ν where
  optimal : ∀ π : Coupling μ ν,
    (∫ x, ‖x - toFun x‖ ^ 2 ∂(μ.law : Measure (Space d))) ≤ couplingCost π

structure JointPlan {d : ℕ} (base μ ν : Distribution d) where
  law : ProbabilityMeasure (Space d × Space d × Space d)
  baseMarginal : (law : Measure (Space d × Space d × Space d)).map
    (fun z => z.1) = base.law
  firstMarginal : (law : Measure (Space d × Space d × Space d)).map
    (fun z => z.2.1) = μ.law
  secondMarginal : (law : Measure (Space d × Space d × Space d)).map
    (fun z => z.2.2) = ν.law

structure OptimalJointPlan {d : ℕ} (base μ ν : Distribution d)
    extends JointPlan base μ ν where
  firstOptimal : (∫ z, ‖z.1 - z.2.1‖ ^ 2 ∂(law : Measure (Space d × Space d × Space d))) =
    squaredDistance base μ
  secondOptimal : (∫ z, ‖z.1 - z.2.2‖ ^ 2 ∂(law : Measure (Space d × Space d × Space d))) =
    squaredDistance base ν

def GeneralizedGeodesicConvex {d : ℕ} (Q : Set (Distribution d))
    (H : Distribution d → ℝ) : Prop :=
  ∀ (base μ ν : Distribution d), μ ∈ Q → ν ∈ Q →
    ∃ π : OptimalJointPlan base μ ν, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ∃ ρ : Distribution d,
        (ρ.law : Measure (Space d)) = (π.law : Measure (Space d × Space d × Space d)).map
          (fun z => (1 - θ) • z.2.1 + θ • z.2.2) ∧
        ρ ∈ Q ∧ H ρ ≤ (1 - θ) * H μ + θ * H ν

structure Public where
  d : ℕ
  L : ℝ
  R : ℝ
  ε : ℝ
  initial : Distribution d

structure Params extends Public where

structure Instance (p : Public) where
  Q : Set (Distribution p.d)
  H : Distribution p.d → ℝ
  V : Space p.d → ℝ
  gradient : Space p.d → Space p.d
  minimizer : Distribution p.d

noncomputable def objective {p : Public} (I : Instance p) (μ : Distribution p.d) : ℝ :=
  (∫ x, I.V x ∂(μ.law : Measure (Space p.d))) + I.H μ

inductive Query (d : ℕ) where
  | forward (h : ℝ) (μ : Distribution d)
  | proximal (h : ℝ) (μ : Distribution d)
  | transport (μ ν : Distribution d)

inductive Reply (d : ℕ) where
  | distribution (μ : Distribution d)
  | transport (μ ν : Distribution d) (T : Transport μ ν)

def CorrectReply (p : Public) (I : Instance p) : Query p.d → Reply p.d → Prop
  | .forward h μ, r => ∃ b, r = .distribution b ∧
      (μ.law : Measure (Space p.d)).map (fun x => x - h • I.gradient x) = b.law
  | .proximal h b, r => 0 < h → ∃ u, r = .distribution u ∧ u ∈ I.Q ∧
      ∀ ρ ∈ I.Q, 2 * h * I.H u + squaredDistance b u ≤
        2 * h * I.H ρ + squaredDistance b ρ
  | .transport μ ν, r => μ ∈ I.Q → ∃ T : OptimalTransport μ ν,
      r = .transport μ ν T.toTransport

structure Admissible (p : Params) (I : Instance p.toPublic)
    (oracle : OracleTemplate.Oracle (Query p.d) (Reply p.d)) : Prop where
  convex : ConvexOn ℝ Set.univ I.V
  gradient : ∀ x, HasGradientAt I.V (I.gradient x) x
  smooth : ∀ x y, ‖I.gradient x - I.gradient y‖ ≤ p.L * ‖x - y‖
  regular : ∀ μ ∈ I.Q, (μ.law : Measure (Space p.d)) ≪ volume
  generalizedConvex : GeneralizedGeodesicConvex I.Q I.H
  initialFeasible : p.initial ∈ I.Q
  minimizerFeasible : I.minimizer ∈ I.Q
  minimal : ∀ μ ∈ I.Q, objective I I.minimizer ≤ objective I μ
  initialDistance : squaredDistance p.initial I.minimizer ≤ p.R ^ 2
  replies : ∀ history seed q, CorrectReply p.toPublic I q (oracle.answer history (0, q) seed)

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := Query p.d
  Reply p := Reply p.d
  Output p := Distribution p.d
  publicInput := Params.toPublic
  valid p := 0 < p.L ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible := Admissible
  successful p I output P := ∀ᵐ ω ∂(P : Measure _),
    output ω ∈ I.Q ∧ objective I (output ω) - objective I I.minimizer ≤ p.ε

end LongTails.Setups.WassersteinSmoothComposite
