import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticSurjectiveInequalities

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  m : ℕ
  H : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE
  Params.borelE Params.measurableΩ

abbrev Constraint (p : Params) := EuclideanSpace ℝ (Fin p.m)
abbrev Jacobian (p : Params) := PiLp 2 (fun _ : Fin p.m => p.E)
abbrev Primitive (p : Params) := p.E × Constraint p × Jacobian p

instance (p : Params) : MeasurableSpace (Constraint p) := borel (Constraint p)
instance (p : Params) : BorelSpace (Constraint p) := ⟨rfl⟩
instance (p : Params) : MeasurableSpace (Jacobian p) := borel (Jacobian p)
instance (p : Params) : BorelSpace (Jacobian p) := ⟨rfl⟩

structure Problem (p : Params) where
  f : p.E → ℝ
  c : p.E → Constraint p
  J : p.E → Jacobian p

def transposeAction (p : Params) (J : Jacobian p) (ℓ : Constraint p) : p.E :=
  ∑ i, ℓ i • J i

def penalty (p : Params) (I : Problem p) (x : p.E) : ℝ :=
  I.f x + 4 * p.H * (p.H + 1) * ∑ i, max (I.c x i) 0

structure Regularity (q : Params) (I : Problem q) : Prop where
  hasGradient : ∀ x, HasGradientAt I.f (gradient I.f x) x
  constraintGradient : ∀ x i, HasGradientAt (fun y => I.c y i) (I.J x i) x
  gradientBound : ∀ x, ‖gradient I.f x‖ ≤ q.H
  jacobianBound : ∀ x, ‖I.J x‖ ≤ q.H
  gradientLipschitz : ∀ x y, ‖gradient I.f x - gradient I.f y‖ ≤ q.H * ‖x - y‖
  jacobianLipschitz : ∀ x y, ‖I.J x - I.J y‖ ≤ q.H * ‖x - y‖
  surjective : ∀ x ℓ, ‖ℓ‖ ≤ q.H * ‖transposeAction q (I.J x) ℓ‖
  initialGap : ∀ x, penalty q I q.x0 - penalty q I x ≤ q.Δ

structure OracleConditions (q : Params) (I : Problem q)
    (g : q.E → q.Ω → q.E) (v : q.E → q.Ω → Constraint q)
    (D : q.E → q.Ω → Jacobian q) (p : ProbabilityMeasure q.Ω) : Prop where
  gradientMeasurable : Measurable (Function.uncurry g)
  valueMeasurable : Measurable (Function.uncurry v)
  jacobianMeasurable : Measurable (Function.uncurry D)
  integrable : ∀ x, Integrable (g x) p ∧ Integrable (v x) p ∧ Integrable (D x) p
  gradientMean : ∀ x, ∫ ω, g x ω ∂p = gradient I.f x
  valueMean : ∀ x, ∫ ω, v x ω ∂p = I.c x
  jacobianMean : ∀ x, ∫ ω, D x ω ∂p = I.J x
  varianceIntegrable : ∀ x, Integrable (fun ω => ‖g x ω - gradient I.f x‖ ^ 2 +
    ‖v x ω - I.c x‖ ^ 2 + ‖D x ω - I.J x‖ ^ 2) p
  variance : ∀ x, ∫ ω, (‖g x ω - gradient I.f x‖ ^ 2 +
    ‖v x ω - I.c x‖ ^ 2 + ‖D x ω - I.J x‖ ^ 2) ∂p ≤ q.σ ^ 2
  differenceIntegrable : ∀ x y, Integrable (fun ω => ‖g x ω - g y ω‖ ^ 2 +
    ‖v x ω - v y ω‖ ^ 2 + ‖D x ω - D y ω‖ ^ 2) p
  meanSquaredSmooth : ∀ x y, ∫ ω, (‖g x ω - g y ω‖ ^ 2 + ‖v x ω - v y ω‖ ^ 2 +
    ‖D x ω - D y ω‖ ^ 2) ∂p ≤ q.H ^ 2 * ‖x - y‖ ^ 2

def accurate (p : Params) (I : Problem p) (out : p.E × Constraint p) : Prop :=
  (∀ i, 0 ≤ out.2 i) ∧
  ‖gradient I.f out.1 + transposeAction p (I.J out.1) out.2‖ ≤ p.ε ∧
  ‖(WithLp.toLp 2 (fun i => max (I.c out.1 i) 0) : Constraint p)‖ ≤ p.ε ∧
  ∑ i, |out.2 i * I.c out.1 i| ≤ p.ε

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Problem p
  Query p := p.E × p.E
  Reply p := Primitive p × Primitive p
  Output p := p.E × Constraint p
  publicInput p := p
  valid p := 0 < p.m ∧ 1 ≤ p.H ∧ 0 ≤ p.σ ∧ 0 ≤ p.Δ ∧ 0 < p.ε ∧ p.ε ≤ 1
  admissible q I O :=
    ∃ (g : q.E → q.Ω → q.E) (v : q.E → q.Ω → Constraint q)
      (D : q.E → q.Ω → Jacobian q)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, z) ω =>
              ((g z.1 ω, v z.1 ω, D z.1 ω), (g z.2 ω, v z.2 ω, D z.2 ω)) } ∧
      Regularity q I ∧ OracleConditions q I g v D p
  successful q I output P :=
    Measurable output ∧ ENNReal.ofReal (3 / 4) ≤ (P : Measure _) {ω | accurate q I (output ω)}

end LongTails.Setups.StochasticSurjectiveInequalities
