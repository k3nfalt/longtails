import LongTails.Proofs.WarmMonotoneRun
import LongTails.Proofs.AnchoredExtragradientExecution

namespace OracleTemplate.WarmAnchoredMonotone

open GeneralizedMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma warm_prefix (F : E → E) (L0 L1 R : ℝ) (x0 : E) (k : ℕ)
    (hk : k ≤ warmLimit L1 R) :
    let A := algorithm L0 L1 R x0
    let T := fun s => A.update s (F (A.query s).2)
    T^[2 * k] (A.initial ()) =
      ⟨warmLimit L1 R - k, warmRun F L0 L1 R x0 k,
        ⟨false, warmRun F L0 L1 R x0 k, 0, 0⟩⟩ := by
  dsimp only
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k ≤ warmLimit L1 R := by omega
    have hn : warmLimit L1 R - k ≠ 0 := by omega
    rw [Nat.mul_succ, show 2 * k + 2 = (2 * k + 1) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_succ_apply', ih hk']
    simp [algorithm, hn, warmRun, Nat.sub_sub]

lemma anchored_suffix (F : E → E) (L0 L1 R : ℝ) (x0 a : E) (s : AnchoredState E) (n : ℕ) :
    let A := algorithm L0 L1 R x0
    let B := anchoredExtragradient L0 L1 a
    let T := fun q => A.update q (F (A.query q).2)
    let U := fun q => B.update q (F (B.query q).2)
    T^[n] ⟨0, a, s⟩ = ⟨0, a, U^[n] s⟩ := by
  dsimp only [algorithm, anchoredExtragradient]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp

lemma execute_warm_anchor (F : E → E) (L0 L1 R : ℝ) (x0 : E) (n : ℕ) :
    execute { answer := fun _ (_, x) _ => F x } (algorithm L0 L1 R x0)
      (fun _ => 2 * (warmLimit L1 R + n)) =
      (run F L0 L1 (warmRun F L0 L1 R x0 (warmLimit L1 R)) n).1 := by
  let A := algorithm L0 L1 R x0
  let T := fun s => A.update s (F (A.query s).2)
  let a := warmRun F L0 L1 R x0 (warmLimit L1 R)
  let B := anchoredExtragradient L0 L1 a
  let U := fun s => B.update s (F (B.query s).2)
  have hw : T^[2 * warmLimit L1 R] (A.initial ()) = ⟨0, a, ⟨false, a, 0, 0⟩⟩ := by
    simpa [T, A, a] using warm_prefix F L0 L1 R x0 (warmLimit L1 R) le_rfl
  have hs : T^[2 * n] ⟨0, a, B.initial ()⟩ = ⟨0, a, U^[2 * n] (B.initial ())⟩ :=
    anchored_suffix F L0 L1 R x0 a (B.initial ()) (2 * n)
  have ha := execute_anchored F L0 L1 a n
  erw [execute_iterate] at ha ⊢
  change A.output (T^[2 * (warmLimit L1 R + n)] (A.initial ())) = _
  rw [show 2 * (warmLimit L1 R + n) = 2 * n + 2 * warmLimit L1 R by omega,
    Function.iterate_add_apply, hw]
  change A.output (T^[2 * n] ⟨0, a, B.initial ()⟩) = _
  rw [hs]
  exact ha

end OracleTemplate.WarmAnchoredMonotone
