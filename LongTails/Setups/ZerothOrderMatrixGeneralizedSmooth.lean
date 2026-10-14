import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

open OracleTemplate

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Params where
  d : ℕ
  L0 : ℝ
  L1 : ℝ
  r : ℝ
  R : ℝ
  Δ : ℝ
  ε : ℝ
  δ : ℝ
  x0 : Point d

def Certifies {d : ℕ} (H : Point d →L[ℝ] Point d) (g : Point d) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ w, ⟪g, w⟫ ≤ c * Real.sqrt ⟪H w, w⟫

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p.d → ℝ
  Query p := Point p.d
  Reply _ := ℝ
  Output p := Point p.d
  publicInput p := p
  valid q := 0 < q.d ∧ 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.r ∧ 0 < q.R ∧ 0 < q.Δ ∧
    0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q f O :=
    (∀ k x seed, O.answer k (0, x) seed = f x) ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    Differentiable ℝ (gradient f) ∧
    ∃ H : Point q.d →L[ℝ] Point q.d,
      (∀ v w, ⟪H v, w⟫ = ⟪v, H w⟫) ∧
      (∃ μ, 0 < μ ∧ ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪H v, v⟫) ∧
      (∀ v, ⟪H v, v⟫ ≤ ‖v‖ ^ 2) ∧
      (∑ i, ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫ ≤ q.r) ∧
      (∀ x c, Certifies H (gradient f x) c → ∀ v w,
        ⟪fderiv ℝ (gradient f) x v, w⟫ ≤
          (q.L0 + q.L1 * c) * Real.sqrt ⟪H v, v⟫ * Real.sqrt ⟪H w, w⟫) ∧
      (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧ f q.x0 - f xstar ≤ q.Δ)
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f xstar} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth
