import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace LongTails.Algorithms.LoraGd

open OracleTemplate

abbrev MatrixSpace (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

abbrev Factors (m n r : ℕ) :=
  EuclideanSpace ℝ ((Fin m × Fin r) ⊕ (Fin r × Fin n))

noncomputable def product {m n r : ℕ} (x : Factors m n r) : MatrixSpace m n :=
  WithLp.toLp 2 fun ij => ∑ k, x (Sum.inl (ij.1, k)) * x (Sum.inr (k, ij.2))

noncomputable def linearization {m n r : ℕ} (x h : Factors m n r) : MatrixSpace m n :=
  WithLp.toLp 2 fun ij =>
    ∑ k, (h (Sum.inl (ij.1, k)) * x (Sum.inr (k, ij.2)) +
      x (Sum.inl (ij.1, k)) * h (Sum.inr (k, ij.2)))

noncomputable def pullback {m n r : ℕ} (x : Factors m n r) (G : MatrixSpace m n) :
    Factors m n r :=
  WithLp.toLp 2 (Sum.elim
    (fun ik => ∑ j, G (ik.1, j) * x (Sum.inr (ik.2, j)))
    (fun kj => ∑ i, x (Sum.inl (i, kj.1)) * G (i, kj.2)))

noncomputable def leftAction {m n r : ℕ} (x : Factors m n r)
    (v : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => ∑ k, x (Sum.inl (i, k)) * v k

noncomputable def rightTransposeAction {m n r : ℕ} (x : Factors m n r)
    (v : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => ∑ k, x (Sum.inr (k, j)) * v k

noncomputable def method {m n r : ℕ} (η : ℕ → ℝ) (x₀ : Factors m n r) :
    Algorithm (MatrixSpace m n) (MatrixSpace m n) (Factors m n r) where
  State := ℕ × Factors m n r
  initial _ := (0, x₀)
  query state := (0, product state.2)
  update state G := (state.1 + 1, state.2 - η state.1 • pullback state.2 G)
  output state := state.2

end LongTails.Algorithms.LoraGd

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
