import LongTails.Setups.GeneralizedSmoothParameterFree
import LongTails.Proofs.Execution
import LongTails.Proofs.BacktrackingAcceleratedBudget

namespace OracleTemplate.ParameterFreeGeneralized

open LongTails.Setups.GeneralizedSmoothParameterFree

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * ⌈5 + 4 * Real.sqrt (32 * q.L0 * q.R ^ 2 / q.ε) + 26 * (1 + q.L1 * q.R) * Real.log (1 + (2 + 13 * q.L1 * q.R) ^ 2 * (2 + 1 / (64 * q.L0 * q.h0) + 16 * q.L0 * q.h0 + 5 * q.L1 ^ 2 * q.Δ / (4 * q.L0) + 80 * q.L1 ^ 2 * q.Δ * q.h0))⌉₊

theorem result : Convergence LongTails.Setups.GeneralizedSmoothParameterFree.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun q => ⌈5 + 4 * Real.sqrt (32 * q.L0 * q.R ^ 2 / q.ε) + 26 * (1 + q.L1 * q.R) * Real.log (1 + (2 + 13 * q.L1 * q.R) ^ 2 * (2 + 1 / (64 * q.L0 * q.h0) + 16 * q.L0 * q.h0 + 5 * q.L1 ^ 2 * q.Δ / (4 * q.L0) + 80 * q.L1 ^ 2 * q.Δ * q.h0))⌉₊)
    (fun _ => 2)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q ⟨hh0, hL0, hL1, hR, hΔ, hε⟩
  intro N hcap
  rintro f oracle ⟨hc, hg, hgd, hH, u, hmin, hdist, hgap⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer [] (0, x) seed0
  have H : Hyp f g q.L0 q.L1 u := ⟨hL0, hL1, hc, hg [] seed0, hgd [] seed0, hH [] seed0, hmin⟩
  have hacc : f ((trial g)^[N] ⟨0, q.x0, q.x0, q.h0⟩).x - f u ≤ q.ε := by
    apply trial_accuracy H hR hh0 hε hdist N
    have hb := budget_bound H hR hh0 hε hgap
    have hm := budget_merge hL0 hL1 hR hΔ.le hh0
    have hN := Nat.le_ceil (5 + 4 * Real.sqrt (32 * q.L0 * q.R ^ 2 / q.ε) + 26 * (1 + q.L1 * q.R) * Real.log (1 + (2 + 13 * q.L1 * q.R) ^ 2 * (2 + 1 / (64 * q.L0 * q.h0) + 16 * q.L0 * q.h0 + 5 * q.L1 ^ 2 * q.Δ / (4 * q.L0) + 80 * q.L1 ^ 2 * q.Δ * q.h0)))
    have hcast : ((⌈5 + 4 * Real.sqrt (32 * q.L0 * q.R ^ 2 / q.ε) + 26 * (1 + q.L1 * q.R) * Real.log (1 + (2 + 13 * q.L1 * q.R) ^ 2 * (2 + 1 / (64 * q.L0 * q.h0) + 16 * q.L0 * q.h0 + 5 * q.L1 ^ 2 * q.Δ / (4 * q.L0) + 80 * q.L1 ^ 2 * q.Δ * q.h0))⌉₊) : ℝ) ≤ N := Nat.cast_le.mpr hcap
    linarith
  have hexec (seed : (algorithm q.toPublic).Seed × ((k : ℕ) → oracle.Seed k)) :
      execute oracle (algorithm q.toPublic) (fun _ => (2 * N)) seed.1 seed.2 =
        ((trial g)^[N] ⟨0, q.x0, q.x0, q.h0⟩).x := by
    rw [execute_eq_of_answer_eq oracle g
      (fun k x sample => (hg k sample x).unique (hg [] seed0 x))]
    exact execute_algorithm q.toPublic g N
  refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
  · intro seed
    change f (execute oracle (algorithm q.toPublic) (fun _ => (2 * N)) seed.1 seed.2) - f u ≤ q.ε
    rw [hexec]
    exact hacc

end OracleTemplate.ParameterFreeGeneralized
