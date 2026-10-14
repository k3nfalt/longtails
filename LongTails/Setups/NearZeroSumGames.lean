import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LongTails.Template

open scoped RealInnerProductSpace

open OracleTemplate

namespace LongTails.Setups.NearZeroSumGames

structure Public where
  E : Type
  F : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [normedF : NormedAddCommGroup F]
  [innerF : InnerProductSpace ℝ F]
  [finiteF : FiniteDimensional ℝ F]
  X : Set E
  Y : Set F
  L : ℝ
  μ : ℝ
  ν : ℝ
  δ : ℝ
  D : ℝ
  ε : ℝ
  x0 : E
  y0 : F

attribute [instance] Public.normedE Public.innerE Public.finiteE
  Public.normedF Public.innerF Public.finiteF

abbrev Space (p : Public) := WithLp 2 (p.E × p.F)

def domain (p : Public) : Set (Space p) := {z | z.fst ∈ p.X ∧ z.snd ∈ p.Y}

def initialPoint (p : Public) : Space p := WithLp.toLp 2 (p.x0, p.y0)

structure Problem (p : Public) where
  h : Space p → ℝ
  g : Space p → ℝ

def IsEquilibrium {p : Public} (I : Problem p) (z : Space p) : Prop :=
  z ∈ domain p ∧
    (∀ x ∈ p.X, I.h z + I.g z ≤
      I.h (WithLp.toLp 2 (x, z.snd)) + I.g (WithLp.toLp 2 (x, z.snd))) ∧
    (∀ y ∈ p.Y, I.g z - I.h z ≤
      I.g (WithLp.toLp 2 (z.fst, y)) - I.h (WithLp.toLp 2 (z.fst, y)))

def ownGradient {p : Public} (H G : Space p → Space p) (z : Space p) : Space p :=
  WithLp.toLp 2 ((H z).fst + (G z).fst, -(H z).snd + (G z).snd)

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance := Problem
  Query p := Space p ⊕ Space p
  Reply p := Space p
  Output p := Space p
  publicInput := id
  valid p :=
    IsCompact p.X ∧ IsCompact p.Y ∧ Convex ℝ p.X ∧ Convex ℝ p.Y ∧
    p.x0 ∈ p.X ∧ p.y0 ∈ p.Y ∧
    (∀ z ∈ domain p, ∀ w ∈ domain p, ‖z - w‖ ≤ p.D) ∧
    0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.ν ∧ p.ν ≤ p.L ∧
    0 ≤ p.δ ∧ p.δ ≤ p.L ∧ 0 < p.D ∧ 0 < p.ε
  admissible p I oracle :=
    (∀ y ∈ p.Y, StrongConvexOn p.X p.μ (fun x => I.h (WithLp.toLp 2 (x, y)))) ∧
    (∀ x ∈ p.X, StrongConvexOn p.Y p.ν (fun y => -I.h (WithLp.toLp 2 (x, y)))) ∧
    ConvexOn ℝ (domain p) I.g ∧
    (∃ zstar, IsEquilibrium I zstar) ∧
    ∃ H G P : Space p → Space p,
      (∀ z ∈ domain p, HasGradientWithinAt I.h (H z) (domain p) z) ∧
      (∀ z ∈ domain p, HasGradientWithinAt I.g (G z) (domain p) z) ∧
      (∀ z ∈ domain p, ∀ w ∈ domain p,
        ‖(H z + G z) - (H w + G w)‖ ≤ p.L * ‖z - w‖) ∧
      (∀ z ∈ domain p, ∀ w ∈ domain p,
        ‖(H z - G z) - (H w - G w)‖ ≤ p.L * ‖z - w‖) ∧
      (∀ z ∈ domain p, ∀ w ∈ domain p, ‖G z - G w‖ ≤ p.δ * ‖z - w‖) ∧
      (∀ z, P z ∈ domain p ∧ ∀ w ∈ domain p, ⟪z - P z, w - P z⟫ ≤ 0) ∧
      (∀ k seed z, z ∈ domain p →
        oracle.answer k (0, Sum.inl z) seed = ownGradient H G z) ∧
      (∀ k seed z, oracle.answer k (0, Sum.inr z) seed = P z)
  successful p I output law :=
    ∃ zstar, IsEquilibrium I zstar ∧
      ∀ᵐ ω ∂(law : MeasureTheory.Measure _),
        output ω ∈ domain p ∧ ‖output ω - zstar‖ ^ 2 ≤ p.ε

end LongTails.Setups.NearZeroSumGames
