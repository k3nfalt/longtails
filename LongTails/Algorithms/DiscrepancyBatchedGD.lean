import LongTails.Algorithms.Batched
import LongTails.Algorithms.Gd
import LongTails.Setups.RelativeDiscrepancyPL

namespace OracleTemplate.RelativeDiscrepancyPL

open LongTails.Setups.RelativeDiscrepancyPL

noncomputable def batchSize (D : ℝ) : ℕ := max 1 ⌈2 * D⌉₊

lemma batchSize_pos (D : ℝ) : 0 < batchSize D :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

noncomputable def batchedGD (p : Public) : Algorithm p.E p.E p.E :=
  batched (batchSize_pos p.D) (Gradient.gd (p.L, p.x0)) (fun x _ => x)
    (fun _ replies => ((batchSize p.D : ℕ) : ℝ)⁻¹ • ∑ i, replies i) 0

end OracleTemplate.RelativeDiscrepancyPL
