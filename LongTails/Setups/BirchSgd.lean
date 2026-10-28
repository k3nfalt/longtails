import LongTails.Template
import LongTails.Setups.StochasticSmoothAndConvex
import LongTails.Algorithms.BirchSgd

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.BirchSgd

open OracleTemplate OracleTemplate.BirchSgd
open OracleTemplate.Rennala (Instance Point)

def SmoothObjective {d : ℕ} (f : Point d → ℝ) (L : ℝ) : Prop :=
  (∀ x, HasGradientAt f (gradient f x) x) ∧
    ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

def LowerBounded {d : ℕ} (f : Point d → ℝ) (lower : ℝ) : Prop :=
  ∀ x, lower ≤ f x

def ReprContained (T : Tree) (m : ℕ → ℕ) : Prop :=
  ∀ k, T.repr (T.auxNode m k) ≤ T.repr (m k)

def DistanceBounded (T : Tree) (m : ℕ → ℕ) (R : ℝ) : Prop :=
  ∀ k, (T.dist (m k) (T.auxNode m k) : ℝ) ≤ R

def SampleIndependent {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (m : ℕ → ℕ)
    (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d) (P : Measure (ℕ → Ω)) : Prop :=
  ∀ k, IndepFun (fun η : ℕ → Ω => η (T.auxSample m k))
    (fun η : ℕ → Ω => fun i : Fin k =>
      (T.vertex gamma x0 g η (m (i.val + 1)), T.vertex gamma x0 g η (T.auxNode m (i.val + 1)),
        η (T.auxSample m i.val))) P

structure Params where
  d : ℕ
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  R : ℝ
  x0 : Point d
  tree : Tree
  branch : ℕ → ℕ

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  gamma := stepSize p.L p.σ p.ε p.R
  x0 := p.x0
  tree := p.tree
  branch := p.branch
  K := horizon p.L p.σ p.ε p.Δ p.R

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ 0 ≤ p.R ∧ p.tree.WellFormed ∧
    p.tree.IsMainBranch p.branch ∧ ReprContained p.tree p.branch ∧
    DistanceBounded p.tree p.branch p.R
  admissible p I O :=
    SmoothObjective I.f p.L ∧ LowerBounded I.f I.lower ∧ I.f p.x0 - I.lower ≤ p.Δ ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Point p.d → Ω → Point p.d),
        (∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω)) ∧
        LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
          (μ : Measure Ω) I.f g p.σ ∧
        SampleIndependent p.tree p.branch (stepSize p.L p.σ p.ε p.R) p.x0 g
          (P : Measure (ℕ → Ω)) ∧
        O = gradientOracle P g
  successful p I output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm q A := A = birch q

end LongTails.Setups.BirchSgd
