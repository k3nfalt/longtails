import LongTails.Algorithms.RobustGradientEstimator

namespace OracleTemplate.AffineGradient

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def neighbors {n : ℕ} (α ν : ℝ) (v : Fin n → E) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => ‖v i - v j‖ ≤ α * (‖v i‖ + ν)

noncomputable def firstCenter {n : ℕ} (α ν : ℝ) (v : Fin n → E) : List (Fin n) → E
  | [] => 0
  | i :: rest => if n < 2 * (neighbors α ν v i).card then v i else firstCenter α ν v rest

noncomputable def center {n : ℕ} (α ν : ℝ) (v : Fin n → E) : E :=
  firstCenter α ν v (List.finRange n)

end OracleTemplate.AffineGradient
