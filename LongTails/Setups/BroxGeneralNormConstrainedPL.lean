import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set MeasureTheory

namespace LongTails.Setups.BroxGeneralNormConstrainedPL

open OracleTemplate

abbrev BroxQuery (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E ⊕ (E × ℝ × (E →L[ℝ] ℝ))

abbrev BroxReply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E →L[ℝ] ℝ) ⊕ E

def normalCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (x : E) :
    Set (E →L[ℝ] ℝ) :=
  {n | ∀ z ∈ C, n (z - x) ≤ 0}

noncomputable def stationarity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (C : Set E) (x : E) : ℝ :=
  sInf ((fun n => ‖fderiv ℝ f x + n‖) '' normalCone C x)

noncomputable def optimalValue {E : Type*} (f : E → ℝ) (C : Set E) : ℝ :=
  sInf (f '' C)

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [spaceE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  L : ℝ
  r : ℝ
  x0 : E

attribute [instance] Public.normedE Public.spaceE Public.finiteE

structure Params extends Public where
  μ : ℝ
  Δ : ℝ
  ε : ℝ

structure Instance (p : Public) where
  f : p.E → ℝ
  C : Set p.E

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Public
  Instance := Instance
  Query p := BroxQuery p.E
  Reply p := BroxReply p.E
  Output p := p.E
  publicInput p := p.toPublic
  valid p := 0 < p.L ∧ 0 < p.μ ∧ 0 < p.ε ∧ 0 < p.r
  admissible p I O :=
    Convex ℝ I.C ∧ IsClosed I.C ∧ p.x0 ∈ I.C ∧
    (∀ x ∈ I.C, DifferentiableAt ℝ I.f x) ∧
    (∀ x ∈ I.C, ∀ y ∈ I.C, ‖fderiv ℝ I.f y - fderiv ℝ I.f x‖ ≤ p.L * ‖y - x‖) ∧
    BddBelow (I.f '' I.C) ∧
    (∀ x ∈ I.C, p.μ * (I.f x - optimalValue I.f I.C) ≤ stationarity I.f I.C x ^ 2 / 2) ∧
    I.f p.x0 - optimalValue I.f I.C ≤ p.Δ ∧
    (∀ history seed x, x ∈ I.C →
      O.answer history (0, .inl x) seed = .inl (fderiv ℝ I.f x)) ∧
    (∀ history seed x r g, x ∈ I.C → 0 ≤ r →
      ∃ v ∈ I.C, ‖v - x‖ ≤ r ∧ (∀ z ∈ I.C, ‖z - x‖ ≤ r → g v ≤ g z) ∧
        O.answer history (1, .inr (x, r, g)) seed = .inr v)
  successful p I output P :=
    ∀ᵐ ω ∂(P : Measure _), output ω ∈ I.C ∧ I.f (output ω) - optimalValue I.f I.C ≤ p.ε

end LongTails.Setups.BroxGeneralNormConstrainedPL
