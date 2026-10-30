import LongTails.Setups.ComparisonSmoothConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.ComparisonOrthConvergence

namespace OracleTemplate.ComparisonOrth

open LongTails.Setups.ComparisonSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1) * ((12 * Nat.log2 (p.n * ⌈p.L * p.R ^ 2 / p.ε⌉₊) + 96) * (3 * p.n + 7 * (12 * Nat.log2 (p.n * ⌈p.L * p.R ^ 2 / p.ε⌉₊) + 96) ^ 2))

theorem result : Convergence LongTails.Setups.ComparisonSmoothConvex.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => comparisonOrth p.x0 p.R
    (p.R / (160 * p.n ^ 2 * (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1 : ℕ) *
      (p.L * p.R ^ 2 / p.ε) ^ 2))
    (12 * (Nat.log2 (p.n * ⌈p.L * p.R ^ 2 / p.ε⌉₊) + 8))
    (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1), ?_, fun _ _ => trivial⟩
  intro p hp K hK f O ho
  obtain ⟨hn, hL, hR, hε⟩ := hp
  obtain ⟨hc, hg, hlip, ⟨xs, hmin, hx0⟩, hO⟩ := ho
  refine ⟨xs, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, ξ⟩
  have hlen := orth_len_le p.x0 p.R
    (p.R / (160 * p.n ^ 2 * (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1 : ℕ) *
      (p.L * p.R ^ 2 / p.ε) ^ 2))
    (12 * (Nat.log2 (p.n * ⌈p.L * p.R ^ 2 / p.ε⌉₊) + 8))
    (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1) (by omega)
  have hk : planIdx (orthPlan p.x0 p.R
      (p.R / (160 * p.n ^ 2 * (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1 : ℕ) *
        (p.L * p.R ^ 2 / p.ε) ^ 2))
      (12 * (Nat.log2 (p.n * ⌈p.L * p.R ^ 2 / p.ε⌉₊) + 8))
      (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1)) ≤ K := by
    refine hlen.trans (le_trans (le_of_eq ?_) hK)
    simp only [budget]
    ring
  have hex : execute O (comparisonOrth p.x0 p.R
      (p.R / (160 * p.n ^ 2 * (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1 : ℕ) *
        (p.L * p.R ^ 2 / p.ε) ^ 2))
      (12 * (Nat.log2 (p.n * ⌈p.L * p.R ^ 2 / p.ε⌉₊) + 8))
      (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1)) (fun _ => K) () ξ =
      QueryPlan.eval (cmp f) (orthPlan p.x0 p.R
        (p.R / (160 * p.n ^ 2 * (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1 : ℕ) *
          (p.L * p.R ^ 2 / p.ε) ^ 2))
        (12 * (Nat.log2 (p.n * ⌈p.L * p.R ^ 2 / p.ε⌉₊) + 8))
        (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1)) :=
    execute_cmp f O hO (p.x0, p.x0) p.x0 (fun _ => orthPlan p.x0 p.R
        (p.R / (160 * p.n ^ 2 * (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1 : ℕ) *
          (p.L * p.R ^ 2 / p.ε) ^ 2))
        (12 * (Nat.log2 (p.n * ⌈p.L * p.R ^ 2 / p.ε⌉₊) + 8))
        (⌈6 * Real.sqrt (p.L * p.R ^ 2 / p.ε)⌉₊ + 1)) hk ξ
  have key := orth_converges hc hg hlip hmin hn hL hR hε hx0
  rw [← hex] at key
  exact key

end OracleTemplate.ComparisonOrth
