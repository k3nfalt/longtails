import LongTails.Setups.StochasticSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

structure OracleTemplate.BatchedSGD.State (E : Type*) where
  iteration : ℕ
  count : ℕ
  point : E
  total : E

noncomputable def OracleTemplate.BatchedSGD.algorithm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (η : ℕ → ℝ) (batch : ℕ → ℕ) (x0 : E) : OracleTemplate.Algorithm E E E where
  State := OracleTemplate.BatchedSGD.State E
  initial _ := ⟨1, 0, x0, 0⟩
  query state := (0, state.point)
  update state reply :=
    if state.count + 1 < batch state.iteration then
      ⟨state.iteration, state.count + 1, state.point, state.total + reply⟩
    else
      ⟨state.iteration + 1, 0,
        state.point - (η state.iteration / batch state.iteration) •
          (state.total + reply), 0⟩
  output state := state.point

namespace LongTails.Setups.StochasticConvexQuadratic

open OracleTemplate

structure Params extends LongTails.Setups.StochasticSmoothAndConvex.Params where
  [finiteE : FiniteDimensional ℝ E]

attribute [instance] Params.finiteE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := q.E → ℝ
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  allowedAlgorithm q algorithm :=
    ∃ (η : ℕ → ℝ) (batch : ℕ → ℕ),
      (∀ i, 0 ≤ η i) ∧ (∀ i, 0 < batch i) ∧
      algorithm = BatchedSGD.algorithm η batch q.x0
  publicInput q := q
  valid q := LongTails.Setups.StochasticSmoothAndConvex.spec.valid q.toParams
  admissible q f O :=
    LongTails.Setups.StochasticSmoothAndConvex.spec.admissible q.toParams f O ∧
    ∃ (A : q.E →L[ℝ] q.E) (u : q.E) (c : ℝ),
      ∀ x, f x = c + ‖A (x - u)‖ ^ 2 / 2
  successful q f output P := LongTails.Setups.StochasticSmoothAndConvex.spec.successful q.toParams f output P

end LongTails.Setups.StochasticConvexQuadratic
