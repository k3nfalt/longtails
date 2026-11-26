import LongTails.Algorithms.MarkovNormalizedBatch

namespace LongTails.Algorithms.MarkovNonconvexBurnInBatches

open OracleTemplate AbcSgd MarkovNormalizedBatch

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def keptSlot (b : ℕ) {n : ℕ} (i : Fin n) : Fin (b + n) :=
  ⟨b + i.val, Nat.add_lt_add_left i.isLt b⟩

noncomputable def method (η : ℝ) (k b n : ℕ) (hn : 0 < n) (x0 : E) : Algorithm E E E :=
  let base := sampledSgd η k x0
  batched (show 0 < b + n by omega) base (fun s _ => (base.query s).2)
    (fun _ replies => direction (fun i : Fin n => replies (keptSlot b i))) 0

def retained {Z : Type} (b n : ℕ) (ξ : ℕ → Z) (s : ℕ) : Z :=
  ξ (s / n * (b + n) + (b + s % n))

noncomputable def iterate {Z : Type} (g : E → Z → E) (η : ℝ) (b n : ℕ) (x0 : E)
    (ξ : ℕ → Z) (j : ℕ) : E :=
  output g η n 1 x0 (retained b n ξ) j

end LongTails.Algorithms.MarkovNonconvexBurnInBatches
