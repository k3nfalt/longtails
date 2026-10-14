import LongTails.Setups.StochasticGeneralizedMonotone
import LongTails.Proofs.Execution
import LongTails.Proofs.ClippedExtragradientPublic

namespace OracleTemplate.StochasticGeneralizedMonotone

open LongTails.Setups.StochasticGeneralizedMonotone

open ClippedExtragradient

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 ^ 60 * (1 + p.L0 * p.R / p.ε + (p.L1 * p.R) ^ 2 + p.σ ^ 2 / p.ε ^ 2) * (1 + Real.log (2 + p.L0 * p.R / p.ε + p.L1 * p.R)) ^ 3 * (1 + Real.log ((2 + p.L0 * p.R / p.ε + p.L1 * p.R) / p.δ))⌉₊

theorem result : Convergence LongTails.Setups.StochasticGeneralizedMonotone.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => localizedClippedExtragradient ⟨p.L0, p.L1, p.R, p.σ, p.ε, p.δ⟩ p.x0,
    ?_, fun _ _ => trivial⟩
  rintro q ⟨h0, h1, hR, hσ, hε, hδ, hδ1⟩

  rintro F O
    ⟨g, p, P, hIID, rfl, hc, hm, hlip, ⟨xstar, hstar, hdist⟩, hg⟩
  let t : Tuning := ⟨q.L0, q.L1, q.R, q.σ, q.ε, q.δ⟩
  by_cases hRpos : 0 < q.R
  · have hK : remainingCalls t 0 (stageCount t) ≤ budget q 0 := by
      apply (Nat.cast_le (α := ℝ)).mp
      exact (total_calls_bound t h0 h1 hRpos hε hδ hδ1).trans (Nat.le_ceil _)
    exact execution_success t h0 h1 hRpos hε hδ F hc hm hlip p P hIID hg
      q.x0 xstar hstar hdist (budget q 0) hK
  · have hRzero : q.R = 0 := le_antisymm (le_of_not_gt hRpos) hR
    have hx : q.x0 = xstar := sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [hRzero] using hdist) (norm_nonneg _)))
    have hroot : F q.x0 = 0 := by rw [hx]; exact hstar
    exact execution_success_zero t hRpos hε F g P q.x0 hroot (budget q 0)

end OracleTemplate.StochasticGeneralizedMonotone
