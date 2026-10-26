import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import LongTails.Template

open Set Matrix
open scoped RealInnerProductSpace

namespace LongTails.Setups.LinearPredictorBFGS

open OracleTemplate

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure Public where
  d : ℕ
  m : ℕ
  x0 : Space d
  L : ℝ

structure Params extends Public where
  Lh : ℝ
  μ : ℝ
  c1 : ℝ
  c2 : ℝ
  R : ℝ
  ε : ℝ

structure Instance (p : Public) where
  A : Space p.d →L[ℝ] Space p.m
  h : Space p.m → ℝ

def objective {p : Public} (I : Instance p) (x : Space p.d) : ℝ := I.h (I.A x)

noncomputable def bfgsUpdate {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (s y : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  B - (s ⬝ᵥ (B *ᵥ s))⁻¹ • vecMulVec (B *ᵥ s) (B *ᵥ s) + (y ⬝ᵥ s)⁻¹ • vecMulVec y y

noncomputable def direction {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (g : Space d) : Space d :=
  WithLp.toLp 2 (-(B⁻¹ *ᵥ WithLp.ofLp g))

structure State (d : ℕ) where
  x : Space d
  g : Space d
  B : Matrix (Fin d) (Fin d) ℝ
  started : Bool

noncomputable def bfgs {d : ℕ} (c : ℝ) (x0 : Space d) :
    Algorithm (Space d × Space d) (ℝ × Space d) (Space d) where
  State := State d
  initial _ := ⟨x0, 0, c • 1, false⟩
  query st := (0, (st.x, if st.started then direction st.B st.g else 0))
  update st r :=
    if st.started then
      ⟨st.x + r.1 • direction st.B st.g, r.2,
        bfgsUpdate st.B (WithLp.ofLp (r.1 • direction st.B st.g)) (WithLp.ofLp (r.2 - st.g)), true⟩
    else ⟨st.x, r.2, st.B, true⟩
  output st := st.x

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := Space p.d × Space p.d
  Reply p := ℝ × Space p.d
  Output p := Space p.d
  publicInput := Params.toPublic
  valid q := 0 < q.μ ∧ q.μ ≤ q.Lh ∧ 0 < q.c1 ∧ q.c1 < q.c2 ∧ q.c2 < 1 ∧ 0 < q.L ∧
    0 ≤ q.R ∧ 0 < q.ε
  admissible q I oracle :=
    ConvexOn ℝ univ I.h ∧
    (∃ gradH : Space q.m → Space q.m, (∀ z, HasGradientAt I.h (gradH z) z) ∧
      ∀ z w, ‖gradH z - gradH w‖ ≤ q.Lh * ‖z - w‖) ∧
    q.Lh * ‖I.A‖ ^ 2 ≤ q.L ∧
    (∃ xstar, IsMinOn (objective I) univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      ∀ x, objective I x ≤ objective I q.x0 →
        q.μ / 2 * ‖I.A x - I.A xstar‖ ^ 2 ≤ objective I x - objective I xstar) ∧
    (∀ k seed x v, HasGradientAt (objective I) (oracle.answer k (0, (x, v)) seed).2
      (x + (oracle.answer k (0, (x, v)) seed).1 • v)) ∧
    (∀ k seed x v, ⟪gradient (objective I) x, v⟫ < 0 →
      0 < (oracle.answer k (0, (x, v)) seed).1 ∧
      objective I (x + (oracle.answer k (0, (x, v)) seed).1 • v) ≤
        objective I x + q.c1 * (oracle.answer k (0, (x, v)) seed).1 *
          ⟪gradient (objective I) x, v⟫ ∧
      q.c2 * ⟪gradient (objective I) x, v⟫ ≤ ⟪(oracle.answer k (0, (x, v)) seed).2, v⟫)
  successful q I output P :=
    ∃ xstar, IsMinOn (objective I) univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), objective I (output ω) - objective I xstar ≤ q.ε
  allowedAlgorithm p algorithm := ∃ c : ℝ, 0 < c ∧ algorithm = bfgs c p.x0

end LongTails.Setups.LinearPredictorBFGS
