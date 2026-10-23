import LongTails.Setups.GeneralizedSmoothAdam
import LongTails.Proofs.AdamGeneralizedExecution

namespace OracleTemplate.ExpectedGeneralizedSmoothAdam

open LongTails.Setups.GeneralizedSmoothAdam LongTails.Algorithms.GeneralizedSmoothAdam

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) * (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) + 2 / (1 - q.β)⌉₊

theorem result : Convergence LongTails.Setups.GeneralizedSmoothAdam.spec budget := by
  let makeAlgorithm := fun q : Params => algorithm q (budget q 0)
  refine ⟨makeAlgorithm, ?_, ?_⟩
  · rintro q hvalid f O ⟨g, p, P, h_samples, rfl, hf, hs, hgap, hg, hi, hmean, h2, hvar⟩
    have hbudget : 2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) *
        (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) + 2 / (1 - q.β) ≤ (budget q 0 : ℝ) := Nat.le_ceil _
    have hh := LongTails.Proofs.AdamGeneralizedExecution.execution_accuracy q p P h_samples hvalid hf hs hgap
      hg hi hmean h2 hvar hbudget
    exact hh
  · rintro q ⟨hL0, hL1, hσ, hΔ, hε, hβ, hβ1⟩
    have hb : 0 < 1 - q.β := by linarith
    have hbudget : 2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) *
        (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) + 2 / (1 - q.β) ≤ (budget q 0 : ℝ) := Nat.le_ceil _
    have hnon : 0 ≤ 2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) *
        (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) := by positivity
    have hm : 2 / (1 - q.β) ≤ (budget q 0 : ℝ) := (le_add_of_nonneg_left hnon).trans hbudget
    have ht := LongTails.Proofs.AdamGeneralizedParameters.horizon_memory hβ hβ1 hm
    have hT : (0 : ℝ) < budget q 0 := by exact_mod_cast (show 0 < budget q 0 by omega)
    have hK : 0 ≤ 4 * (1 + q.L0 + q.L1) := by positivity
    have hs := LongTails.Proofs.AdamGeneralizedParameters.scale_envelopes (d := q.d) hβ hβ1 hK
    have ha : 0 < stepScale q := hs.1
    have hρ : 0 < 1 / (budget q 0 : ℝ) := by positivity
    have hρ1 : 1 / (budget q 0 : ℝ) ≤ 1 := (div_le_one hT).2 (by exact_mod_cast (show 1 ≤ budget q 0 by omega))
    exact ⟨1 / (budget q 0 : ℝ), stepScale q / Real.sqrt (budget q 0), 1, 1 + q.σ ^ 2,
      budget q 0 - 1, hρ, hρ1, by positivity, by norm_num, by positivity, rfl⟩

end OracleTemplate.ExpectedGeneralizedSmoothAdam
