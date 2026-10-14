import LongTails.Algorithms.Clipping
import Mathlib.Data.Finset.Sort

namespace OracleTemplate.RobustGradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def centeredClip (B : ℝ) (c v : E) : E := c + clip B (v - c)

noncomputable def neighbors {n : ℕ} (B : ℝ) (v : Fin n → E) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => ‖v i - v j‖ ≤ B / 3)

noncomputable def firstPilot {n : ℕ} (B : ℝ) (v : Fin n → E) : List (Fin n) → E
  | [] => 0
  | i :: rest => if n < 2 * (neighbors B v i).card then v i else firstPilot B v rest

noncomputable def pilotCenter {n : ℕ} (B : ℝ) (v : Fin n → E) : E :=
  firstPilot B v (List.finRange n)

end OracleTemplate.RobustGradient
