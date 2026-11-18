import LongTails.Setups.FiniteSumNondualSmoothConvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.PolynomialMixingSubgradient

open OracleTemplate

structure Params where
  d : ℕ
  R : ℝ
  hR : 0 ≤ R
  G : ℝ
  p : ℝ
  β : ℝ
  τ : ℝ
  ε : ℝ
  δ : ℝ

abbrev Space (q : Params) := EuclideanSpace ℝ (Fin q.d)

abbrev Domain (q : Params) := Metric.closedBall (0 : Space q) q.R

abbrev Path := ℕ → ℝ

def past (n : ℕ) (z : Path) : Fin n → ℝ := fun i => z i.val

def future (n : ℕ) (z : Path) : Path := fun k => z (n + k)

def AbsolutelyRegular (P : ProbabilityMeasure Path) (τ β : ℝ) : Prop :=
  (∀ t, (P : Measure Path).map (future t) = (P : Measure Path)) ∧
  ∀ n t : ℕ, ∀ B : Set ((Fin (n + 1) → ℝ) × Path), MeasurableSet B →
    |(P : Measure Path).real {z | (past (n + 1) z, future (n + t) z) ∈ B} -
      (((P : Measure Path).map (past (n + 1))).prod (P : Measure Path)).real B| ≤
      (1 + (t : ℝ) / τ) ^ (-β)

structure SubgradientOracle (q : Params) (f : Space q → ℝ)
    (g : Domain q → ℝ → Space q) (π : Measure ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) π
  momentIntegrable : ∀ x, Integrable (fun z => ‖g x z‖ ^ q.p) π
  moment : ∀ x, (∫ z, ‖g x z‖ ^ q.p ∂π) ≤ q.G ^ q.p
  support : ∀ x y : Domain q, f x + inner ℝ (∫ z, g x z ∂π) (y.val - x.val) ≤ f y

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Space q → ℝ
  Query q := Domain q
  Reply q := Space q
  Output q := Domain q
  publicInput q := q
  valid q := 0 < q.d ∧ 0 < q.R ∧ 0 < q.G ∧ 1 < q.p ∧ q.p ≤ 2 ∧
    0 < q.β ∧ 1 ≤ q.τ ∧ 0 < q.ε ∧ 8 * q.ε ≤ q.G * q.R ∧ 0 < q.δ ∧ q.δ ≤ 1 / 32
  admissible q f O :=
    ∃ (g : Domain q → ℝ → Space q) (P : ProbabilityMeasure Path),
      O = { Seed := fun _ => ℝ, law := P, answer := fun _ (_, x) z => g x z } ∧
      AbsolutelyRegular P q.τ q.β ∧ ConvexOn ℝ (Domain q) f ∧
      (∃ x ∈ Domain q, IsMinOn f (Domain q) x) ∧
      SubgradientOracle q f g ((P : Measure Path).map (fun z => z 0))
  successful q f output P :=
    Measurable output ∧ ∃ x ∈ Domain q, IsMinOn f (Domain q) x ∧
      (P : Measure _).real {w | f (output w) - f x ≤ q.ε} ≥ 1 - q.δ

end LongTails.Setups.PolynomialMixingSubgradient
