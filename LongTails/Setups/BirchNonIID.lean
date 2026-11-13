import LongTails.Setups.BirchSgd
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate
open OracleTemplate.Rennala (Point)
open OracleTemplate.BirchSgd (Tree Hist State)
open LongTails.Setups.BirchSgd (SmoothObjective LowerBounded)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

inductive Similarity where
  | unrestricted
  | firstOrder
  | secondOrder
  | firstAndSecondOrder

structure Params (workers : ℕ) where
  d : ℕ
  L : ℝ
  σ : Fin workers → ℝ
  ε : ℝ
  Δ : ℝ
  ζ : ℝ
  δ : ℝ
  similarity : Similarity
  x0 : Point d

structure Instance (workers d : ℕ) where
  localObjective : Fin workers → Point d → ℝ
  lower : ℝ

noncomputable def objective {workers d : ℕ} (I : Instance workers d) (x : Point d) : ℝ :=
  (workers : ℝ)⁻¹ * ∑ i, I.localObjective i x

def FirstOrderSimilarity {workers d : ℕ} (I : Instance workers d) (ζ : ℝ) : Prop :=
  ∀ i x, ‖gradient (I.localObjective i) x - gradient (objective I) x‖ ^ 2 ≤ ζ ^ 2

def SecondOrderSimilarity {workers d : ℕ} (I : Instance workers d) (δ : ℝ) : Prop :=
  (∀ i, Differentiable ℝ (gradient (I.localObjective i))) ∧
  Differentiable ℝ (gradient (objective I)) ∧
  ∀ i x, ‖fderiv ℝ (gradient (I.localObjective i)) x -
    fderiv ℝ (gradient (objective I)) x‖ ≤ δ

def GradientDifferenceSimilarity {workers d : ℕ} (I : Instance workers d)
    (δ : ℝ) : Prop :=
  ∀ i x y, ‖(gradient (I.localObjective i) x - gradient (objective I) x) -
    (gradient (I.localObjective i) y - gradient (objective I) y)‖ ≤ δ * ‖x - y‖

def Similarity.Holds {workers d : ℕ} (s : Similarity) (I : Instance workers d)
    (ζ δ : ℝ) : Prop :=
  match s with
  | .unrestricted => True
  | .firstOrder => FirstOrderSimilarity I ζ
  | .secondOrder => SecondOrderSimilarity I δ
  | .firstAndSecondOrder => FirstOrderSimilarity I ζ ∧ SecondOrderSimilarity I δ

def Valid {workers : ℕ} (p : Params workers) : Prop :=
  0 < workers ∧ 0 < p.d ∧ 0 < p.L ∧ (∀ i, 0 ≤ p.σ i) ∧
  0 < p.ε ∧ 0 ≤ p.Δ ∧ 0 ≤ p.ζ ∧ 0 ≤ p.δ

def ObjectiveClass {workers : ℕ} (p : Params workers) (I : Instance workers p.d) : Prop :=
  (∀ i x, HasGradientAt (I.localObjective i) (gradient (I.localObjective i) x) x) ∧
  SmoothObjective (objective I) p.L ∧ LowerBounded (objective I) I.lower ∧
  objective I p.x0 - I.lower ≤ p.Δ ∧ p.similarity.Holds I p.ζ p.δ

noncomputable def workerOracle {workers d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Fin workers → Point d → Ω → Point d) :
    Oracle (Point d) (Point d) workers where
  Seed := fun _ => Ω
  law := P
  answer := fun _ q seed => g q.1 q.2 seed

def Admissible {workers : ℕ} (p : Params workers) (I : Instance workers p.d)
    (O : Oracle (Point p.d) (Point p.d) workers) : Prop :=
  ObjectiveClass p I ∧
  ∃ (Ω : Type) (m : MeasurableSpace Ω),
    letI := m
    ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
      (g : Fin workers → Point p.d → Ω → Point p.d),
      IID (fun k (η : ℕ → Ω) => η k) (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
      (∀ i, IsStochasticGradient (Point p.d) Ω (μ : Measure Ω)
        (I.localObjective i) (g i) (p.σ i)) ∧
      O = workerOracle P g

noncomputable abbrev spec (workers : ℕ) : Setup where
  numOracles := workers
  Params := Params workers
  Public := Params workers
  Instance p := Instance workers p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput p := p
  valid := Valid
  admissible := Admissible
  successful p I output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient (objective I) (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient (objective I) (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε

structure BirchPolicy (workers : ℕ) where
  tree : Tree
  worker : ℕ → Fin workers
  step : ℕ → ℝ
  calls : ℕ
  branch : ℕ → ℕ
  outputCount : ℕ
  outputIndex : Fin (outputCount + 1) → ℕ

def BirchPolicy.Legal {workers : ℕ} (a : BirchPolicy workers) : Prop :=
  a.tree.WellFormed ∧ a.tree.IsMainBranch a.branch ∧
  (∀ k, 0 ≤ a.step k) ∧ ∀ j, a.branch (a.outputIndex j) ≤ a.calls

def BirchPolicy.oracleCalls {workers : ℕ} (a : BirchPolicy workers) (i : Fin workers) : ℕ :=
  ((Finset.range a.calls).filter (fun k => a.worker k = i)).card

def BirchPolicy.HasGeometry {workers : ℕ} (a : BirchPolicy workers) (R : ℝ) : Prop :=
  LongTails.Setups.BirchSgd.ReprContained a.tree a.branch ∧
  LongTails.Setups.BirchSgd.DistanceBounded a.tree a.branch R

noncomputable def birch {workers : ℕ} (p : Params workers) (a : BirchPolicy workers) :
    Algorithm (Point p.d) (Point p.d) (Point p.d) workers where
  Seed := Fin (a.outputCount + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (a.outputCount + 1))).toMeasure, inferInstance⟩
  State := State p.d
  initial j := ⟨0, ⟨fun _ => p.x0, fun _ => 0⟩, a.branch (a.outputIndex j)⟩
  query s := (a.worker s.count, s.hist.nodes (a.tree.point s.count))
  update s reply :=
    if s.count < a.calls then
      ⟨s.count + 1, s.hist.step a.tree (a.step s.count) s.count reply, s.chosen⟩
    else s
  output s := s.hist.nodes s.chosen

noncomputable abbrev birchSpec (workers : ℕ) : Setup :=
  { spec workers with
    allowedAlgorithm := fun p A => ∃ a : BirchPolicy workers, a.Legal ∧ A = birch p a }

end LongTails.Setups.BirchNonIID
