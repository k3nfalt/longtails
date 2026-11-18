import LongTails.Algorithms.AbcSgd
import LongTails.Algorithms.Batched

open scoped BigOperators

namespace LongTails.Algorithms.MarkovNormalizedBatch

open OracleTemplate AbcSgd

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def slot {B h : ℕ} (hh : 0 < h) (i : Fin B) : Fin (B * h) :=
  ⟨i.val * h, Nat.mul_lt_mul_of_pos_right i.isLt hh⟩

noncomputable def direction {B : ℕ} (g : Fin B → E) : E :=
  let v := ∑ i, g i
  ‖v‖⁻¹ • v

noncomputable def method (η : ℝ) (K B h : ℕ) (hB : 0 < B) (hh : 0 < h) (x0 : E) :
    Algorithm E E E :=
  let base := sampledSgd η K x0
  batched (Nat.mul_pos hB hh) base (fun s _ => (base.query s).2)
    (fun _ values => direction (fun i => values (slot hh i))) 0

noncomputable def output {Ω : Type} (g : E → Ω → E) (η : ℝ) (B h : ℕ)
    (x0 : E) (ξ : ℕ → Ω) : ℕ → E
  | 0 => x0
  | j + 1 =>
    let x := output g η B h x0 ξ j
    x - η • direction (fun i : Fin B => g x (ξ (j * (B * h) + i.val * h)))

end LongTails.Algorithms.MarkovNormalizedBatch
