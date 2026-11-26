import LongTails.Algorithms.MarkovNonconvexBurnInBatches
import LongTails.Proofs.MarkovNormalizedExecution

open MeasureTheory OracleTemplate
namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

open Algorithms.MarkovNonconvexBurnInBatches Algorithms.AbcSgd
open Algorithms.MarkovNormalizedBatch (direction)
variable {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma retained_slot (b n j : ℕ) (hn : 0 < n) (i : Fin n) (ξ : ℕ → Z) :
    retained b n ξ (j * n + i.val) = ξ (j * (b+n) + (b+i.val)) := by
  simp [retained, Nat.mul_comm j n, Nat.mul_add_div hn, Nat.div_eq_of_lt i.isLt, Nat.mod_eq_of_lt i.isLt]

lemma execute_method [MeasurableSpace Z] (P : ProbabilityMeasure (ℕ → Z)) (g : E → Z → E)
    (η : ℝ) (k b n : ℕ) (hn : 0 < n) (x0 : E) (seed : Fin (k+1)) (ξ : ℕ → Z) :
    execute { Seed := fun _ => Z, law := P, answer := fun _ (_, x) z => g x z }
      (method η k b n hn x0) (fun _ => (k+1)*(b+n)) seed ξ =
      iterate g η b n x0 ξ seed.val := by
  let base := sampledSgd η k x0
  have actual := execute_batched (show 0 < b+n by omega) base (fun s _ => (base.query s).2)
    (fun _ replies => direction (fun i : Fin n => replies (keptSlot b i))) 0 P g ξ (k+1) seed
  have packed := execute_batched (Nat.mul_pos hn (by decide : 0 < 1)) base
    (fun s _ => (base.query s).2) (fun _ replies => direction (fun i : Fin n =>
      replies (Algorithms.MarkovNormalizedBatch.slot (by decide : 0 < 1) i))) 0 P g
    (retained b n ξ) (k+1) seed
  have normalized := MarkovNormalizedExecution.execute_method P g η k n 1 hn (by decide) x0 seed
    (retained b n ξ)
  apply actual.trans
  apply Eq.trans _ (packed.symm.trans normalized)
  simp only [keptSlot, Algorithms.MarkovNormalizedBatch.slot, Nat.mul_one, retained_slot b n _ hn]

end LongTails.Proofs.MarkovNonconvexBurnInBatches
