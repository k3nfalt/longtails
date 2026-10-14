import LongTails.Template
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory

namespace LongTails.Setups.BoundedScalarConvex

open OracleTemplate

abbrev Samples (O : Oracle ℝ ℝ) := (k : ℕ) → O.Seed k

@[instance_reducible]
def past (O : Oracle ℝ ℝ) (n : ℕ) : MeasurableSpace (Samples O) :=
  ⨆ k : Fin n, MeasurableSpace.comap (fun ω : Samples O => ω k)
    (inferInstance : MeasurableSpace (O.Seed k))

structure Params where
  lower : ℝ
  upper : ℝ
  H : ℝ
  R : ℝ
  ε : ℝ
  x0 : ℝ

def IsBoundedSubgradientOracle (q : Params) (f : ℝ → ℝ) (O : Oracle ℝ ℝ) : Prop :=
  (∀ n, Measurable (Function.uncurry (fun x seed => O.answer n (0, x) seed))) ∧
    ∀ n (x : Samples O → ℝ), Measurable[past O n] x →
      (∀ ω, x ω ∈ Set.Icc q.lower q.upper) →
      (∀ᵐ ω ∂(O.law : Measure _), |O.answer n (0, (x ω)) (ω n)| ≤ q.H) ∧
      (∀ᵐ ω ∂(O.law : Measure _), ∀ y ∈ Set.Icc q.lower q.upper,
        f (x ω) + ((O.law : Measure _)[fun ξ => O.answer n (0, (x ξ)) (ξ n) | past O n]) ω *
          (y-x ω) ≤ f y)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance _ := ℝ → ℝ
  Query _ := ℝ
  Reply _ := ℝ
  Output _ := ℝ
  publicInput q := q
  valid q := q.lower ≤ q.upper ∧ 0 < q.H ∧ 0 ≤ q.R ∧ 0 < q.ε ∧
    q.x0 ∈ Set.Icc q.lower q.upper
  admissible q f O :=
    ConvexOn ℝ (Set.Icc q.lower q.upper) f ∧
    (∀ x ∈ Set.Icc q.lower q.upper, ∀ y ∈ Set.Icc q.lower q.upper,
      |f x-f y| ≤ q.H*|x-y|) ∧
    (∃ xstar ∈ Set.Icc q.lower q.upper,
      IsMinOn f (Set.Icc q.lower q.upper) xstar ∧ |q.x0-xstar| ≤ q.R) ∧
    IsBoundedSubgradientOracle q f O
  successful q f output P :=
    Measurable output ∧
    (∀ ω, output ω ∈ Set.Icc q.lower q.upper) ∧
    ∃ xstar ∈ Set.Icc q.lower q.upper, IsMinOn f (Set.Icc q.lower q.upper) xstar ∧
      Integrable (fun ω => f (output ω)-f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω)-f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.BoundedScalarConvex
