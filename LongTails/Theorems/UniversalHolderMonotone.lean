import LongTails.Proofs.Execution
import LongTails.Setups.HolderMonotone
import LongTails.Proofs.UniversalRegularizedHolder

namespace OracleTemplate.HolderMonotone

open LongTails.Setups.HolderMonotone

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈40 * (16 * q.L * q.R / q.ε + 2 * (8 * q.H * q.R ^ q.α / q.ε) ^ (1 / q.α) + Real.logb 2 (q.R / q.r0) + 2) * Real.log ((32 * q.L * q.R / q.ε + 4 * (8 * q.H * q.R ^ q.α / q.ε) ^ (1 / q.α) + 4) * q.R / q.r0)⌉₊

theorem result : Convergence LongTails.Setups.HolderMonotone.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => universalRegularizedExtragradient p.ε p.r0 p.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hH, hα0, hα1, hr0, hr0R, hε⟩
  intro K hK
  rintro F oracle ⟨hans, hmono, hhol, xs, hroot, hdist⟩
  obtain ⟨r, c1, ctx⟩ := exists_runCtx hL hH hα0 hα1 hr0 hr0R hε hmono hhol hroot hdist
  have e : 2 * (16 * q.L * q.R / q.ε + 2 * (8 * q.H * q.R ^ q.α / q.ε) ^ (1 / q.α)) + 4 =
      32 * q.L * q.R / q.ε + 4 * (8 * q.H * q.R ^ q.α / q.ε) ^ (1 / q.α) + 4 := by ring
  have hdone := converge ctx (K) (by rw [e]; exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hK))
  have hexec : ∀ seed : Unit × ((k : ℕ) → oracle.Seed k),
      execute oracle (universalRegularizedExtragradient q.ε q.r0 q.x0) (fun _ => (K)) seed.1 seed.2 =
        ((trans F q.ε q.x0)^[K] (stageStart q.ε q.x0 q.r0)).x := by
    rintro ⟨⟨⟩, ξ⟩
    erw [execute_eq_of_answer_eq oracle F (fun k x seed => hans k seed x)]
    exact execute_universal F q.ε q.r0 q.x0 (K)
  refine Filter.Eventually.of_forall (fun seed => ?_)
  · change ‖F (execute oracle (universalRegularizedExtragradient q.ε q.r0 q.x0) (fun _ => (K))
      seed.1 seed.2)‖ ≤ q.ε
    erw [hexec]
    exact hdone.2

end OracleTemplate.HolderMonotone
