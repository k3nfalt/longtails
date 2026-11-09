import LongTails.Proofs.FullRangeMain
import LongTails.Proofs.FullRangeBudget

open MeasureTheory
open scoped ENNReal

namespace LongTails.Theorems.FullRangeCohypomonotoneMlmc

open OracleTemplate OracleTemplate.StochasticCohypomonotone
open LongTails.Setups.FullRangeCohypomonotoneInclusion
open LongTails.Algorithms.FullRangeTuned
open LongTails.Proofs.FullRangeMain LongTails.Proofs.FullRangeAccuracy

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 79 * (1 + q.L * q.R / ((1 - q.ρ * q.L) * q.ε) + q.σ ^ 2 / q.ε ^ 2) / (1 - q.ρ * q.L) ^ 2 * (1 + Real.log (2 + q.L * q.R / q.ε + q.σ ^ 2 / q.ε ^ 2) + Real.log (2 / (1 - q.ρ * q.L))) ^ 7⌉₊

theorem result : Convergence LongTails.Setups.FullRangeCohypomonotoneInclusion.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => algorithm q, ?_, fun _ _ => trivial⟩
  intro q hq I O hadm
  dsimp only
  obtain ⟨hL, hρ, hρL, hR, hσ, hε⟩ := hq
  obtain ⟨g, J, p, P, hIID, rfl, hres, hmono, hlip, hcoh, ⟨xs, hxs, hxsR⟩, hg⟩ := hadm
  have H : OpHyp I.1 I.2 J q.L q.ρ := ⟨hres, hmono, hlip, hcoh, hL, hρ⟩
  have hK : totalCalls q ≤ budget q 0 := by
    have h1 := LongTails.Proofs.FullRangeBudget.totalCalls_le q hL hρ hρL hR hε
    have h3 : (totalCalls q : ℝ) ≤ (budget q 0 : ℝ) := h1.trans (by
      unfold budget LongTails.Proofs.FullRangeBudget.B LongTails.Proofs.FullRangeBudget.Lam tau
      exact Nat.le_ceil _)
    exact_mod_cast h3
  have hexec : ∀ ℓ ξ, execute (oracleOf q g J P) (algorithm q) (fun _ => budget q 0) ℓ ξ =
      outRt q g J ℓ (thin q ξ) := fun ℓ ξ =>
    (execute_eq q g J P _ hK ℓ ξ).trans (out_eq q g J ℓ ξ)
  change spec.successful q I
    (fun ω : (Fin (calls q) → Fin (top q + 1)) × (ℕ → q.Ω) =>
      execute (oracleOf q g J P) (algorithm q) (fun _ => budget q 0) ω.1 ω.2) _
  erw [funext (fun ω : (Fin (calls q) → Fin (top q + 1)) × (ℕ → q.Ω) => hexec ω.1 ω.2)]
  have hη := LongTails.Proofs.FullRangeTuning.eta_pos q hL hρ
  have hthin : Measurable (thin q) := by unfold thin; fun_prop
  have hout := outRt_measurable q g J hL hρ hρL hR hε H p hg
  have hmeas : Measurable (fun ω : (Fin (calls q) → Fin (top q + 1)) × (ℕ → q.Ω) =>
      outRt q g J ω.1 (thin q ω.2)) :=
    measurable_from_prod_countable_right fun ℓ => (hout ℓ).comp hthin
  have hF : Continuous I.1 := (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]; exact hlip a b).continuous
  have hm : Measurable (fun ω : (Fin (calls q) → Fin (top q + 1)) × (ℕ → q.Ω) =>
      ‖I.1 (outRt q g J ω.1 (thin q ω.2)).1 + (outRt q g J ω.1 (thin q ω.2)).2‖) :=
    ((hF.measurable.comp (measurable_fst.comp hmeas)).add (measurable_snd.comp hmeas)).norm
  refine ⟨hmeas, fun ω => ?_, ?_⟩
  · show (outRt q g J ω.1 (thin q ω.2)).2 ∈ I.2 (outRt q g J ω.1 (thin q ω.2)).1
    unfold outRt
    split_ifs
    · exact certOut_mem q g J H hη _ _
    · exact certOut_mem q g J H hη _ _
  have hL2 := main_lintegral q g J hL hρ hρL hR hσ hε H p hg xs hxs hxsR (P : Measure (ℕ → q.Ω))
    hIID.independent hIID.marginal
  change Integrable (fun ω : (Fin (calls q) → Fin (top q + 1)) × (ℕ → q.Ω) =>
      ‖I.1 (outRt q g J ω.1 (thin q ω.2)).1 + (outRt q g J ω.1 (thin q ω.2)).2‖)
      ((Measure.pi fun _ : Fin (calls q) => LongTails.Proofs.FullRangeEstimator.levelLaw (top q)).prod
        (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : (Fin (calls q) → Fin (top q + 1)) × (ℕ → q.Ω),
      ‖I.1 (outRt q g J ω.1 (thin q ω.2)).1 + (outRt q g J ω.1 (thin q ω.2)).2‖
      ∂((Measure.pi fun _ : Fin (calls q) => LongTails.Proofs.FullRangeEstimator.levelLaw (top q)).prod
        (P : Measure (ℕ → q.Ω))) ≤ q.ε
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL2
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL2

end LongTails.Theorems.FullRangeCohypomonotoneMlmc
