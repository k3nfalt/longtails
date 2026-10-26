import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.RadialFairLocation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def score (r : ℝ) (z : E) : E := (r + ‖z‖)⁻¹ • z

noncomputable def location {n : ℕ} (r : ℝ) (a : Fin n → E) : E :=
  Classical.epsilon (fun z => ∑ i, score r (z - a i) = 0)

end OracleTemplate.RadialFairLocation
