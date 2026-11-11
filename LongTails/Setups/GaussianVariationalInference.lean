import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Matrix.Mul

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.GaussianVariationalInference

open OracleTemplate

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Location (d : ℕ) := Fin d → ℝ

abbrev Scale (d : ℕ) := Fin d → Fin d → ℝ

noncomputable def noiseLaw (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance noiseLaw_isProbability (d : ℕ) : IsProbabilityMeasure (noiseLaw d) := by
  unfold noiseLaw
  infer_instance

noncomputable def sample {d : ℕ} (m : Location d) (C : Scale d) (ξ : Fin d → ℝ) : Point d :=
  WithLp.toLp 2 (m + Matrix.mulVec C ξ)

def IsCholesky {d : ℕ} (C : Scale d) : Prop :=
  (∀ i j, i < j → C i j = 0) ∧ ∀ i, 0 < C i i

noncomputable def objective {d : ℕ} (V : Point d → ℝ) (m : Location d) (C : Scale d) : ℝ :=
  (∫ ξ, V (sample m C ξ) ∂noiseLaw d) - ∑ i, Real.log (C i i)

def sqDist {d : ℕ} (m m' : Location d) (C C' : Scale d) : ℝ :=
  (∑ i, (m i - m' i) ^ 2) + ∑ i, ∑ j, (C i j - C' i j) ^ 2

structure Params where
  d : ℕ
  L : ℝ
  μ : ℝ
  R : ℝ
  ε : ℝ
  m0 : Location d
  C0 : Scale d

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p.d → ℝ
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Location p.d × Scale p.d
  publicInput p := p
  valid q := 0 < q.μ ∧ q.μ ≤ q.L ∧ 0 ≤ q.R ∧ 0 < q.ε ∧ IsCholesky q.C0
  admissible q V O :=
    O = { answer := fun _ (_, x) _ => gradient V x } ∧
    (∀ x, HasGradientAt V (gradient V x) x) ∧
    (∀ x y, ‖gradient V x - gradient V y‖ ≤ q.L * ‖x - y‖) ∧
    (∀ x y, q.μ * ‖x - y‖ ^ 2 ≤ ⟪gradient V x - gradient V y, x - y⟫) ∧
    ∃ mstar Cstar, IsCholesky Cstar ∧
      (∀ m C, IsCholesky C → objective V mstar Cstar ≤ objective V m C) ∧
      sqDist q.m0 mstar q.C0 Cstar ≤ q.R ^ 2
  successful q V output P :=
    Measurable output ∧ (∀ ω, IsCholesky (output ω).2) ∧
    ∃ mstar Cstar, IsCholesky Cstar ∧
      (∀ m C, IsCholesky C → objective V mstar Cstar ≤ objective V m C) ∧
      Integrable (fun ω => objective V (output ω).1 (output ω).2 - objective V mstar Cstar)
        (P : Measure _) ∧
      (∫ ω, objective V (output ω).1 (output ω).2 - objective V mstar Cstar ∂(P : Measure _))
        ≤ q.ε

end LongTails.Setups.GaussianVariationalInference
