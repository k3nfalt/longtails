import LongTails.Proofs.Execution
import LongTails.Setups.StochasticCohypomonotoneInclusion
import LongTails.Proofs.RegularizedProxEgMain
import LongTails.Proofs.RegularizedProxEgTuning

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticCohypomonotone

open LongTails.Setups.StochasticCohypomonotoneInclusion

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 53 / (1 - 2 * q.ρ * q.L) ^ 8 * (1 + q.L * q.R / q.ε + q.σ ^ 2 / q.ε ^ 2) * (1 + Real.log (2 + q.L * q.R / q.ε) + Real.log (2 / (1 - 2 * q.ρ * q.L))) ^ 4⌉₊

theorem result : Convergence LongTails.Setups.StochasticCohypomonotoneInclusion.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => regularizedProxExtragradient (tunedCfg q.L q.ρ q.R q.σ q.ε) q.x0, ?_,
    fun _ _ => trivial⟩
  intro q hq I O hadm
  dsimp only
  obtain ⟨hL, hρ, hρL, hR, hσ, hε⟩ := hq
  obtain ⟨g, J, p, P, hIID, rfl, hres, hmono, hlip, hcoh, ⟨xs, hxs, hxsR⟩, hg⟩ := hadm
  have H : OpHyp I.1 I.2 J q.L q.ρ := ⟨hres, hmono, hlip, hcoh, hL, hρ⟩
  have h : TuneHyp q.L q.ρ q.R q.σ q.ε := ⟨hL, hρ, hρL, hR, hσ, hε⟩
  set cfg := tunedCfg q.L q.ρ q.R q.σ q.ε
  have hc := tuned_cfgOK h
  have hlen : planLen cfg ≤ budget q 0 := by
    have h1 := h.planLen_le
    have h2 := Nat.le_ceil (2 ^ 53 / (1 - 2 * q.ρ * q.L) ^ 8 * (1 + q.L * q.R / q.ε + q.σ ^ 2 / q.ε ^ 2) *
      (1 + Real.log (2 + q.L * q.R / q.ε) + Real.log (2 / (1 - 2 * q.ρ * q.L))) ^ 4)
    have h3 : (planLen cfg : ℝ) ≤ (budget q 0 : ℝ) := by
      refine h1.trans (le_of_eq_of_le ?_ h2)
      simp only [tτ, tΛg]
    exact_mod_cast h3
  have hexec : ∀ (u : Unit) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ q => reply g J q.2 } :
        Oracle (q.E ⊕ (ℝ × q.E)) q.E) (regularizedProxExtragradient cfg q.x0) (fun _ => (budget q 0)) u ξ =
      evalP (reply g J) (regularizedPlan cfg q.x0) ξ := by
    intro u ξ
    exact QueryPlan.execute_sampledPlan_of_le _ P (.inl q.x0) (q.x0, 0) (planLen cfg) (budget q 0)
      (fun _ => regularizedPlan cfg q.x0) (reply g J) u ξ hlen
  change spec.successful q I
    (fun ω : Unit × (ℕ → q.Ω) =>
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ q => reply g J q.2 } :
        Oracle (q.E ⊕ (ℝ × q.E)) q.E) (regularizedProxExtragradient cfg q.x0)
        (fun _ => budget q 0) ω.1 ω.2) _
  erw [funext (fun ω : Unit × (ℕ → q.Ω) => hexec ω.1 ω.2)]
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  obtain ⟨hmeas, hmem, hbound⟩ := regularized_main H hc hg hσ q.x0 xs hxs hxsR
  refine ⟨hmeas.comp measurable_snd, fun ω => hmem ω.2, ?_⟩
  have hm : Measurable (fun ω : Unit × (ℕ → q.Ω) =>
      ‖I.1 (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).1 +
        (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).2‖) := by
    have hF : Continuous I.1 := (LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]; exact hlip a b).continuous
    exact ((hF.measurable.comp (measurable_fst.comp hmeas)).add
      (measurable_snd.comp hmeas)).norm.comp measurable_snd
  change Integrable (fun ω : Unit × (ℕ → q.Ω) =>
      ‖I.1 (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).1 +
        (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).2‖)
      ((Measure.dirac ()).prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : Unit × (ℕ → q.Ω), ‖I.1 (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).1 +
        (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).2‖
      ∂((Measure.dirac ()).prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  have hL2 : ∫⁻ ω : Unit × (ℕ → q.Ω), ENNReal.ofReal ‖I.1 (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).1 +
        (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).2‖
      ∂((Measure.dirac ()).prod (Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω))) ≤ ENNReal.ofReal q.ε := by
    have hm2 : Measurable (fun ω : Unit × (ℕ → q.Ω) => ENNReal.ofReal
        ‖I.1 (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).1 +
          (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).2‖) := ENNReal.measurable_ofReal.comp hm
    rw [lintegral_prod _ hm2.aemeasurable, lintegral_dirac]
    exact hbound
  have hfin : ∫⁻ ω : Unit × (ℕ → q.Ω), ENNReal.ofReal ‖I.1 (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).1 +
        (evalP (reply g J) (regularizedPlan cfg q.x0) ω.2).2‖
      ∂((Measure.dirac ()).prod (Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL2
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL2

end OracleTemplate.StochasticCohypomonotone
