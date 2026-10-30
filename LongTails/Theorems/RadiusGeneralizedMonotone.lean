import LongTails.Proofs.Execution
import LongTails.Setups.RadiusGeneralizedLipschitzMonotone
import LongTails.Proofs.WarmMonotoneExecution
import LongTails.Proofs.WarmMonotoneBudget

namespace OracleTemplate.WarmAnchoredMonotone

open LongTails.Setups.RadiusGeneralizedLipschitzMonotone GeneralizedMonotone

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * ⌈(2 : ℝ)^15 * (1 + q.L0 * q.R / q.ε + (q.L1 * q.R)^((4 : ℝ)/3))⌉₊

theorem result : Convergence LongTails.Setups.RadiusGeneralizedLipschitzMonotone.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun q => ⌈(2 : ℝ)^15 * (1 + q.L0 * q.R / q.ε + (q.L1 * q.R)^((4 : ℝ)/3))⌉₊) (fun _ => 2)
  refine ⟨fun p => algorithm p.L0 p.L1 p.R p.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL0, hL1, hR, hε⟩
  intro N hN
  rintro F oracle ⟨hans, hc, hmono, hlip, xs, hroot, hdist⟩
  have hyp : Hyp F q.L0 q.L1 := ⟨hL0, hL1, hc, hmono, hlip⟩
  have hg := warmRun_good hyp hroot hR hdist
  have hmain : 0 ≤ q.L0 * q.R / q.ε := by positivity
  have hLR : 0 ≤ q.L1 * q.R := by positivity
  have ht := (total_blocks hmain hLR).trans hN
  let n := N - warmLimit q.L1 q.R - 1
  have heq : N = warmLimit q.L1 q.R + (n + 1) := by dsimp [n]; omega
  have hnceil : ⌈finishScalar (q.L0 * q.R / q.ε) (q.L1 * q.R)⌉₊ ≤ n := by
    dsimp [n]; omega
  have hlog : 0 ≤ Real.log (1 + 8 * (q.L0 + q.L1 * warmThreshold q.L0 q.L1 q.R) * q.R / q.ε) := by
    apply Real.log_nonneg
    have hg0 : 0 ≤ warmThreshold q.L0 q.L1 q.R := by unfold warmThreshold; positivity
    have hh : 0 ≤ 8 * (q.L0 + q.L1 * warmThreshold q.L0 q.L1 q.R) * q.R / q.ε := by positivity
    linarith
  have hn : 4 / 3 * (8 * q.L0 * q.R / q.ε + (20 * q.L1 * q.R + 3) *
      Real.log (1 + 8 * (q.L0 + q.L1 * warmThreshold q.L0 q.L1 q.R) * q.R / q.ε)) ≤ n := by
    refine le_trans ?_ ((Nat.le_ceil _).trans (Nat.cast_le.mpr hnceil))
    rw [finishScalar_eq]
    have e1 : 8 * q.L0 * q.R / q.ε = 8 * (q.L0 * q.R / q.ε) := by ring
    have e2 : 11 * q.L0 * q.R / q.ε = 11 * (q.L0 * q.R / q.ε) := by ring
    rw [e1, e2]
    nlinarith [mul_nonneg hLR hlog]
  have hacc := run_accuracy hyp hroot hg.1 hg.2 hε n hn
  have hexec : ∀ seed : Unit × ((k : ℕ) → oracle.Seed k),
      execute oracle (algorithm q.L0 q.L1 q.R q.x0) (fun _ => 2 * N) seed.1 seed.2 =
        (run F q.L0 q.L1 (warmRun F q.L0 q.L1 q.R q.x0 (warmLimit q.L1 q.R)) (n + 1)).1 := by
    rintro ⟨⟨⟩, ξ⟩
    erw [heq, execute_eq_of_answer_eq oracle F (fun k x seed => hans k seed x)]
    exact execute_warm_anchor F q.L0 q.L1 q.R q.x0 (n + 1)
  refine Filter.Eventually.of_forall (fun seed => ?_)
  change ‖F (execute oracle (algorithm q.L0 q.L1 q.R q.x0) (fun _ => 2 * N) seed.1 seed.2)‖ ≤ q.ε
  erw [hexec]
  exact hacc

end OracleTemplate.WarmAnchoredMonotone
