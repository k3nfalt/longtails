import LongTails.Algorithms.Batched
import LongTails.Algorithms.MarkovQuadraticSgd

namespace OracleTemplate.FixedBatchConfidence

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def fixedBatchSgd {b : ℕ} (hb : 0 < b) (η : ℝ) (x0 : E) :
    Algorithm E E E :=
  batched hb (MarkovQuadratic.lastSgd η x0) (fun x _ => x)
    (fun _ replies => (b : ℝ)⁻¹ • ∑ i : Fin b, replies i) 0

end OracleTemplate.FixedBatchConfidence
