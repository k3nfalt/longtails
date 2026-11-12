import LongTails.Algorithms.AdaptiveEntropic
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.FiniteHullDirection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

def vertex (i : Fin (n + 1)) : Fin (n + 1) → ℝ := fun j => if j = i then 1 else 0

noncomputable def point (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ) : E :=
  ∑ i, w i • h i

noncomputable def index (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  OracleTemplate.AdaptiveHeavyTailSimplex.minimumIndex (Nat.succ_pos n)
    (fun i => ⟪point h w, h i⟫)

noncomputable def gap (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ) : ℝ :=
  ‖point h w‖ ^ 2 - ⟪point h w, h (index h w)⟫

noncomputable def step (h : Fin (n + 1) → E) (γ : ℝ)
    (w : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => (1 - γ) * w i + γ * vertex (index h w) i

noncomputable def firstPhase (h : Fin (n + 1) → E) : ℕ → (Fin (n + 1) → ℝ)
  | 0 => vertex 0
  | k + 1 => step h (2 / (k + 2)) (firstPhase h k)

noncomputable def secondPhase (h : Fin (n + 1) → E) (T : ℕ) :
    ℕ → (Fin (n + 1) → ℝ)
  | 0 => firstPhase h T
  | k + 1 => step h (1 / T) (secondPhase h T k)

noncomputable def weights (h : Fin (n + 1) → E) (T : ℕ) : Fin (n + 1) → ℝ :=
  secondPhase h T (OracleTemplate.AdaptiveHeavyTailSimplex.minimumIndex
    (Nat.succ_pos T) (fun k => gap h (secondPhase h T k)))

end LongTails.Algorithms.FiniteHullDirection
