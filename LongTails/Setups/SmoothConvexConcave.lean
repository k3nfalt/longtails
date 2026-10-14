import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

open MeasureTheory

namespace LongTails.Setups.SmoothConvexConcave

open OracleTemplate

noncomputable def gap (E F : Type*) (X : Set E) (Y : Set F) (φ : E → F → ℝ) (z : E × F) : ℝ :=
  sSup ((fun y => φ z.1 y) '' Y) - sInf ((fun x => φ x z.2) '' X)

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  F : Type u
  [normedF : NormedAddCommGroup F]
  [linearF : InnerProductSpace ℝ F]
  [completeF : CompleteSpace F]
  [measurableF : MeasurableSpace F]
  L : ℝ
  D : ℝ
  ε : ℝ
  X : Set E
  Y : Set F

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.normedF Params.linearF Params.completeF Params.measurableF

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → p.F → ℝ
  Query p := p.E × p.F
  Reply p := p.E × p.F
  Output p := p.E × p.F
  publicInput p := p
  valid q :=
    0 < q.L ∧ 0 ≤ q.D ∧ 0 < q.ε ∧
    q.X.Nonempty ∧ q.Y.Nonempty ∧ IsCompact q.X ∧ IsCompact q.Y ∧
    Convex ℝ q.X ∧ Convex ℝ q.Y ∧
    (∀ z ∈ q.X ×ˢ q.Y, ∀ w ∈ q.X ×ˢ q.Y, ‖z - w‖ ≤ q.D)
  admissible q φ O :=
    (∀ y ∈ q.Y, ConvexOn ℝ q.X (fun x => φ x y)) ∧
    (∀ x ∈ q.X, ConcaveOn ℝ q.Y (φ x)) ∧
    (∀ k seed z, HasGradientAt (fun x => φ x z.2) (O.answer k (0, z) seed).1 z.1 ∧
      HasGradientAt (φ z.1) (-(O.answer k (0, z) seed).2) z.2) ∧
    (∀ k seed z w, ‖O.answer k (0, z) seed - O.answer k (0, w) seed‖ ≤ q.L * ‖z - w‖)
  successful q φ output P :=
    Measurable output ∧
    (∀ᵐ ω ∂(P : Measure _), output ω ∈ q.X ×ˢ q.Y) ∧
    Integrable (fun ω => gap q.E q.F q.X q.Y φ (output ω)) (P : Measure _) ∧
    (∫ ω, gap q.E q.F q.X q.Y φ (output ω) ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.SmoothConvexConcave
