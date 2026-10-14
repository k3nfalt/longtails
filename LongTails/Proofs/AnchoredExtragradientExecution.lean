import LongTails.Proofs.AnchoredExtragradientRun
import LongTails.Proofs.Execution

namespace OracleTemplate.GeneralizedMonotone

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma execute_anchored (F : E → E) (L0 L1 : ℝ) (x0 : E) (n : ℕ) :
    execute { answer := fun _ (_, x) _ => F x } (anchoredExtragradient L0 L1 x0) (fun _ => (2 * n)) =
      (run F L0 L1 x0 n).1 := by
  let A := anchoredExtragradient L0 L1 x0
  let T := fun s => A.update s (F ((A.query s).2))
  have hi : ∀ n, T^[2 * n] (A.initial ()) =
      ⟨false, (run F L0 L1 x0 n).1, 0, (run F L0 L1 x0 n).2⟩ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ, show 2 * n + 2 = (2 * n + 1) + 1 by omega,
        Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl
  erw [execute_iterate]
  change A.output (T^[2 * n] (A.initial ())) = _
  rw [hi]
  rfl

end OracleTemplate.GeneralizedMonotone
