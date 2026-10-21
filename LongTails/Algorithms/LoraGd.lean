import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2

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
