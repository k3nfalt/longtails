import LongTails.Proofs.Execution
import LongTails.Setups.GeneralizedLipschitzMonotone
import LongTails.Proofs.AnchoredExtragradientExecution

namespace OracleTemplate.GeneralizedMonotone

open LongTails.Setups.GeneralizedLipschitzMonotone

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * (⌈11 * q.L0 * q.R / q.ε + (27 * q.L1 * q.R + 4) * Real.log (1 + 8 * (q.L0 + q.L1 * q.G) * q.R / q.ε)⌉₊ + 1)

theorem result : Convergence LongTails.Setups.GeneralizedLipschitzMonotone.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun q => ⌈11 * q.L0 * q.R / q.ε + (27 * q.L1 * q.R + 4) * Real.log (1 + 8 * (q.L0 + q.L1 * q.G) * q.R / q.ε)⌉₊ + 1) (fun _ => 2)
  refine ⟨fun p => anchoredExtragradient p.L0 p.L1 p.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL0, hL1, hG, hR, hε⟩
  intro N hN
  rintro F oracle ⟨hans, hc, hmono, hlip, hF0, xs, hroot, hdist⟩
  have hyp : Hyp F q.L0 q.L1 := ⟨hL0, hL1, hc, hmono, hlip⟩
  let n := N - 1
  have hNpos : 0 < N := by omega
  have hbudget : 2 * N = 2 * (n + 1) := by dsimp [n]; omega
  have hlog : 0 ≤ Real.log (1 + 8 * (q.L0 + q.L1 * q.G) * q.R / q.ε) := by
    apply Real.log_nonneg
    have : 0 ≤ 8 * (q.L0 + q.L1 * q.G) * q.R / q.ε := by positivity
    linarith
  have hmain : 0 ≤ q.L0 * q.R / q.ε := by positivity
  have hLR : 0 ≤ q.L1 * q.R := by positivity
  have hn : 4 / 3 * (8 * q.L0 * q.R / q.ε + (20 * q.L1 * q.R + 3) *
      Real.log (1 + 8 * (q.L0 + q.L1 * q.G) * q.R / q.ε)) ≤ n := by
    refine le_trans ?_ ((Nat.le_ceil _).trans (Nat.cast_le.mpr (show ⌈11 * q.L0 * q.R / q.ε + (27 * q.L1 * q.R + 4) * Real.log (1 + 8 * (q.L0 + q.L1 * q.G) * q.R / q.ε)⌉₊ ≤ n by dsimp [n]; omega)))
    have e1 : 8 * q.L0 * q.R / q.ε = 8 * (q.L0 * q.R / q.ε) := by ring
    have e2 : 11 * q.L0 * q.R / q.ε = 11 * (q.L0 * q.R / q.ε) := by ring
    rw [e1, e2]
    nlinarith [mul_nonneg hLR hlog]
  have hacc := run_accuracy hyp hroot hdist hF0 hε n hn
  have hexec : ∀ seed : Unit × ((k : ℕ) → oracle.Seed k),
      execute oracle (anchoredExtragradient q.L0 q.L1 q.x0) (fun _ => (2 * N)) seed.1 seed.2 =
        (run F q.L0 q.L1 q.x0 (n + 1)).1 := by
    rintro ⟨⟨⟩, ξ⟩
    erw [hbudget, execute_eq_of_answer_eq oracle F (fun k x seed => hans k seed x)]
    exact execute_anchored F q.L0 q.L1 q.x0 (n + 1)
  refine Filter.Eventually.of_forall (fun seed => ?_)
  · change ‖F (execute oracle (anchoredExtragradient q.L0 q.L1 q.x0) (fun _ => (2 * N))
      seed.1 seed.2)‖ ≤ q.ε
    erw [hexec]
    exact hacc

end OracleTemplate.GeneralizedMonotone
