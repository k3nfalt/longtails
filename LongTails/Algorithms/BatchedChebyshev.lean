import LongTails.Setups.StochasticConvexQuadratic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace OracleTemplate.BatchedChebyshev

noncomputable def root (T i : ℕ) : ℝ :=
  Real.sin ((i : ℝ) * Real.pi / (2 * (T : ℝ) + 1)) ^ 2

noncomputable def weight (T i : ℕ) : ℝ :=
  4 * (2 * (T : ℝ) + 1) / ((i : ℝ) * Real.sqrt (i : ℝ)) + 17

noncomputable def batch (T M i : ℕ) : ℕ :=
  1 + ⌈(M : ℝ) * weight T i / (128 * (T : ℝ))⌉₊

abbrev State := BatchedSGD.State

noncomputable def algorithm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : ℝ) (T M : ℕ) (x0 : E) : Algorithm E E E :=
  BatchedSGD.algorithm (fun i => if i ≤ T then 1 / (L * root T i) else 0) (batch T M) x0

noncomputable def tuned {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L R σ ε : ℝ) (x0 : E) : Algorithm E E E :=
  algorithm L (if L * R ^ 2 / 2 ≤ ε then 0 else ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊)
    ⌈65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊ x0

noncomputable def batchUpdate {E Ω : Type*} [AddCommGroup E] [Module ℝ E]
    (L : ℝ) (T M i : ℕ) (g : E → Ω → E) (x : E) (ξ : Fin (batch T M i) → Ω) : E :=
  x - (1 / (L * root T i * batch T M i)) • ∑ j, g x (ξ j)

noncomputable def run {E Ω : Type*} [AddCommGroup E] [Module ℝ E]
    (L : ℝ) (T M : ℕ) (g : E → Ω → E) : ℕ → ℕ → E → (ℕ → Ω) → E
  | 0, _, x, _ => x
  | n + 1, i, x, ξ => run L T M g n (i + 1)
      (batchUpdate L T M i g x (fun j => ξ j)) (fun j => ξ (batch T M i + j))

noncomputable def calls (T M : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, i => batch T M i + calls T M n (i + 1)

end OracleTemplate.BatchedChebyshev
