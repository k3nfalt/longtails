import LongTails.Proofs.MonotoneHessianCounts

namespace LongTails.Proofs.MonotoneHessianExecution

open OracleTemplate OracleTemplate.QueryPlan LongTails.Algorithms.MonotoneHessianReuse
open LongTails.Setups.HessianLipschitzSecondOrder LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.EnergyHessianExecution

lemma execute_of_counts (p : Params) (g : Fin 2 × p.E → Reply p.E)
    (O : Oracle p.E (Reply p.E) 2) (budget : Fin 2 → ℕ)
    (hO : ∀ k q seed, O.answer k q seed = g q)
    (seed : (algorithm p).Seed)
    (hb : ∀ i, counts g (LongTails.Algorithms.MonotoneHessianReuse.plan p seed) i ≤ budget i)
    (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) budget seed ξ = (LongTails.Algorithms.MonotoneHessianReuse.plan p seed).eval g := by
  let K := (stageCalls p + searchCalls p + 2) * stages p + 1
  let state : ℕ → (Σ k, QueryPlan (Fin 2 × p.E) (Reply p.E) p.E k) :=
    fun k => (fun s => update s (g (query ((0 : Fin 2), p.x0) s)))^[k] ⟨K, (LongTails.Algorithms.MonotoneHessianReuse.plan p seed)⟩
  have hstate0 : state 0 = ⟨K, (LongTails.Algorithms.MonotoneHessianReuse.plan p seed)⟩ := rfl
  have hstep (k : ℕ) : state (k + 1) = update (state k) (g (query ((0 : Fin 2), p.x0) (state k))) :=
    Function.iterate_succ_apply' _ _ _
  let remaining : ℕ → Fin 2 → ℕ := fun k =>
    Nat.rec budget (fun j b => Function.update b (query ((0 : Fin 2), p.x0) (state j)).1
      (b (query ((0 : Fin 2), p.x0) (state j)).1 - 1)) k
  have hremaining0 : remaining 0 = budget := rfl
  have hremaining (k : ℕ) : remaining (k + 1) =
      Function.update (remaining k) (query ((0 : Fin 2), p.x0) (state k)).1
        (remaining k (query ((0 : Fin 2), p.x0) (state k)).1 - 1) := rfl
  have hcover (k : ℕ) : ∀ i, counts g (state k).2 i ≤ remaining k i := by
    induction k with
    | zero => exact hb
    | succ k ih => rw [hstep, hremaining]; exact counts_update g ((0 : Fin 2), p.x0) (state k) _ ih
  have hlength (k : ℕ) : (state k).1 = K - k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, length_update, ih]; omega
  have heval (k : ℕ) : eval g (state k).2 = eval g (LongTails.Algorithms.MonotoneHessianReuse.plan p seed) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, eval_update, ih]
  apply execute_eq_of_safe_prefix O (algorithm p) budget seed ξ
    state remaining K (eval g (LongTails.Algorithms.MonotoneHessianReuse.plan p seed))
  · rfl
  · intro k
    change state (k.length + 1) = update (state k.length)
      (O.answer k (query ((0 : Fin 2), p.x0) (state k.length)) (ξ k.length))
    rw [hO, hstep]
  · rfl
  · exact hremaining
  · intro k hk
    exact (counts_positive g ((0 : Fin 2), p.x0) (state k) (by rw [hlength]; omega)).trans_le
      (hcover k _)
  · intro k hk
    change output p.x0 (state k) = _
    rw [output_of_length_zero g p.x0 (state k) (by rw [hlength]; omega), heval]
  · dsimp only [K]
    rw [← counts_sum g (LongTails.Algorithms.MonotoneHessianReuse.plan p seed)]
    exact Finset.sum_le_sum (fun i _ => hb i)

end LongTails.Proofs.MonotoneHessianExecution
