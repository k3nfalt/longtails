import LongTails.Algorithms.NormalizedSam
import LongTails.Proofs.Execution

namespace LongTails.Proofs.NormalizedSamRun

open LongTails.Algorithms.NormalizedSam OracleTemplate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma execute_method (g : E → E) (η ρ : ℝ) (x0 : E) (T : ℕ) :
    execute { answer := fun _ query _ => g query.2 } (method η ρ x0) (fun _ => 2 * T) =
      output g η ρ x0 T := by
  let F : (E × E × Bool) → (E × E × Bool) := fun s => (method η ρ x0).update s (g ((method η ρ x0).query s).2)
  have hs : ∀ k, F^[2 * k] (x0, 0, false) = ((step g η ρ)^[k] x0, 0, false) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
        Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        Function.iterate_succ_apply']
      rfl
  erw [execute_iterate]
  change (F^[2 * T] (x0, 0, false)).1 = output g η ρ x0 T
  rw [hs]
  rfl

end LongTails.Proofs.NormalizedSamRun
