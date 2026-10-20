import LongTails.Setups.MatrixGeometry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

namespace LongTails.Algorithms.MatrixPolar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def supportFace (K : Set E) (g : E →L[ℝ] ℝ) : Set E :=
  {x | x ∈ K ∧ ∀ y ∈ K, g y ≤ g x}

noncomputable def minimumNormSupport (K : Set E) (g : E →L[ℝ] ℝ) : E :=
  Classical.epsilon (fun x => x ∈ supportFace K g ∧
    ∀ y ∈ supportFace K g, ‖x‖ ≤ ‖y‖)

noncomputable def closestPoint (K : Set E) (u : E) : E :=
  Classical.epsilon (fun x => x ∈ K ∧ ∀ y ∈ K, ‖u - x‖ ≤ ‖u - y‖)

noncomputable def polar {m n : ℕ} (X : LongTails.Setups.MatrixGeometry.Space m n) :
    LongTails.Setups.MatrixGeometry.Space m n :=
  minimumNormSupport (LongTails.Setups.MatrixGeometry.spectralBall m n) (innerSL ℝ X)

end LongTails.Algorithms.MatrixPolar
