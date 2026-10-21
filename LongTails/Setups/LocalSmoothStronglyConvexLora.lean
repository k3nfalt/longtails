import LongTails.Algorithms.LoraGd
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.LocalSmoothStronglyConvexLora

open OracleTemplate LongTails.Algorithms.LoraGd

structure Params where
  m : ℕ
  n : ℕ
  r : ℕ
  μ : ℝ
  ρ : ℝ
  s : ℝ
  R : ℝ
  ε : ℝ
  x₀ : Factors m n r

def gdFamily (p : Params)
    (A : Algorithm (MatrixSpace p.m p.n) (MatrixSpace p.m p.n) (Factors p.m p.n p.r)) : Prop :=
  ∃ (point : A.State → Factors p.m p.n p.r) (step : A.State → MatrixSpace p.m p.n → ℝ),
    (∀ seed, point (A.initial seed) = p.x₀) ∧
    (∀ state G, 0 < step state G) ∧
    (∀ state, A.query state = (0, product (point state))) ∧
    (∀ state G, point (A.update state G) =
      point state - step state G • pullback (point state) G) ∧
    (∀ state, A.output state = point state)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance p := MatrixSpace p.m p.n → ℝ
  Query p := MatrixSpace p.m p.n
  Reply p := MatrixSpace p.m p.n
  Output p := Factors p.m p.n p.r
  publicInput := id
  valid p := 0 < p.r ∧ p.r < p.m ∧ p.r < p.n ∧
    0 < p.μ ∧ p.μ ≤ p.ρ ∧ 0 < p.s ∧ p.s ≤ p.R ∧ 0 < p.ε
  admissible p f O :=
    (∀ X, HasGradientAt f (gradient f X) X) ∧
    (∀ X Y, f X + ⟪gradient f X, Y - X⟫ + p.μ / 2 * ‖Y - X‖ ^ 2 ≤ f Y) ∧
    (∀ X Y, ‖gradient f X - gradient f Y‖ ≤ p.ρ * ‖X - Y‖) ∧
    (∀ k X seed, O.answer k (0, X) seed = gradient f X) ∧
    ∃ v : Factors p.m p.n p.r,
      IsMinOn f Set.univ (product v) ∧
      (∀ h, ‖linearization v h‖ ≤ p.R * ‖h‖) ∧
      (∀ w, p.s * ‖w‖ ≤ ‖leftAction v w‖) ∧
      (∀ w, p.s * ‖w‖ ≤ ‖rightTransposeAction v w‖) ∧
      ‖p.x₀ - v‖ ≤ p.μ * p.s ^ 2 / (256 * p.ρ * p.R)
  successful p f output P :=
    ∃ Xstar, IsMinOn f Set.univ Xstar ∧
      ∀ᵐ ω ∂(P : Measure _), f (product (output ω)) - f Xstar ≤ p.ε
  allowedAlgorithm := gdFamily

end LongTails.Setups.LocalSmoothStronglyConvexLora
