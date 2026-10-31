import LongTails.Algorithms.AdaptiveEntropic
import LongTails.Algorithms.Clipping

namespace OracleTemplate.MultiplicativeRobustEstimator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def score {n : ℕ} (v : Fin n → E) (i : Fin n) : ℝ :=
  ∑ j, ‖v i - v j‖

noncomputable def medoid {n : ℕ} (v : Fin (n + 1) → E) : E :=
  v (AdaptiveHeavyTailSimplex.minimumIndex (Nat.succ_pos n) (score v))

noncomputable def blockMean {b : ℕ} (v : Fin (b + 1) → E) : E :=
  ((b + 1 : ℝ)⁻¹) • ∑ i, v i

noncomputable def estimate {k b : ℕ} (Λ : ℝ)
    (v : Fin (k + 2) → Fin (b + 1) → E) : E × E :=
  let d := medoid (fun i : Fin (k + 1) => blockMean (v i.castSucc))
  (d, clip (4 * Λ * ‖d‖) (blockMean (v (Fin.last (k + 1)))))

end OracleTemplate.MultiplicativeRobustEstimator
