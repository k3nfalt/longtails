import LongTails.Setups.StochasticCompositeHessianLipschitz
import LongTails.Proofs.CompositeTransportTuning
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveIID

open MeasureTheory
open scoped ENNReal

namespace OracleTemplate.CompositeTransport

open LongTails.Setups.StochasticCompositeHessianLipschitz

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈10 ^ 6 * (q.L * q.Δ / q.ε ^ 2 + (1 + q.σ ^ 2 / q.ε ^ 2) * q.Δ * Real.sqrt (q.ρ * q.ε) / q.ε ^ 2 + q.σ ^ 2 / q.ε ^ 2 + 1)⌉₊

theorem result : Convergence LongTails.Setups.StochasticCompositeHessianLipschitz.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨fun q => transport q (tunedConfig q.L q.ρ q.σ q.Δ q.ε), ?_, fun _ _ => trivial⟩
  intro q hq I O hadm
  obtain ⟨hL, hρ, -, hΔ, hε⟩ := hq
  obtain ⟨g, μ, P, hIID, hO, hf, hlip, hd, hl, hQ, hψ, hprm, hpr, hx0, hgap, hgm, hgi, hgmean,
    hgi2, hgvar⟩ := hadm
  dsimp only
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  have hO' : O = oracleOf q g I.prox P := hO
  subst hO'
  have hc0 := tuned_hyp (σ := q.σ) hL hρ hΔ hε
  have hcalls0 := tuned_calls (σ := q.σ) hL hρ hΔ hε
  have h30 : 3 * (tunedConfig q.L q.ρ q.σ q.Δ q.ε).ε = q.ε := by simp only [tunedConfig]; ring
  have hc := hc0
  have H : PathHyp I.f I.grad I.ψ I.Q I.prox q.L := ⟨hf, hlip, hQ, hψ, hpr⟩
  have Or : OracleHyp g I.grad (μ : Measure q.Ω) q.σ := ⟨hgm, hgi, hgmean, hgi2, hgvar⟩
  have hpt : ∀ (τ : (transport q (tunedConfig q.L q.ρ q.σ q.Δ q.ε)).Seed) (ξ : (k : ℕ) → (oracleOf q g I.prox P).Seed k),
      execute (oracleOf q g I.prox P) (transport q (tunedConfig q.L q.ρ q.σ q.Δ q.ε)) (fun _ => budget q 0) τ ξ =
        (traj (tunedConfig q.L q.ρ q.σ q.Δ q.ε) q.x0 g I.prox (ξ : ℕ → q.Ω) (τ : Fin ((tunedConfig q.L q.ρ q.σ q.Δ q.ε).T + 1)).val).1 :=
    fun τ ξ => execute_eq q (tunedConfig q.L q.ρ q.σ q.Δ q.ε) g I.prox ξ hc.n0 P _ τ (by simp only [budget]; exact hcalls0)
  simp only [hpt]
  have hΔ' : ∀ x ∈ I.Q, I.f q.x0 + I.ψ q.x0 - (I.f x + I.ψ x) ≤ q.Δ := hgap
  obtain ⟨hmeas, hmem, hlint⟩ := expected_bound H hL hρ hd hl hc hx0 hΔ' Or hprm
  have hGm : Measurable (fun ω : Fin ((tunedConfig q.L q.ρ q.σ q.Δ q.ε).T + 1) × (ℕ → q.Ω) =>
      ‖gradientMapping I (traj (tunedConfig q.L q.ρ q.σ q.Δ q.ε) q.x0 g I.prox ω.2 ω.1.val).1‖) := by
    have hgrad : Continuous I.grad := by
      have : LipschitzWith (Real.toNNReal q.L) I.grad := LipschitzWith.of_dist_le_mul fun a b => by
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]; exact hlip a b
      exact this.continuous
    have hp := measurable_prox_pos (prox := I.prox) (one_div_pos.mpr hL) hprm
    exact (((measurable_id.sub (hp.comp (measurable_id.prodMk hgrad.measurable))).const_smul q.L).norm).comp hmeas
  have hfin : ∫⁻ ω, ENNReal.ofReal ‖gradientMapping I (traj (tunedConfig q.L q.ρ q.σ q.Δ q.ε) q.x0 g I.prox ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin ((tunedConfig q.L q.ρ q.σ q.Δ q.ε).T + 1))).toMeasure.prod (Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlint
  have hInt : Integrable (fun ω : Fin ((tunedConfig q.L q.ρ q.σ q.Δ q.ε).T + 1) × (ℕ → q.Ω) =>
      ‖gradientMapping I (traj (tunedConfig q.L q.ρ q.σ q.Δ q.ε) q.x0 g I.prox ω.2 ω.1.val).1‖)
      ((PMF.uniformOfFintype (Fin ((tunedConfig q.L q.ρ q.σ q.Δ q.ε).T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) := by
    rw [hP]
    have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hGm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  have hIle : ∫ ω : Fin ((tunedConfig q.L q.ρ q.σ q.Δ q.ε).T + 1) × (ℕ → q.Ω), ‖gradientMapping I (traj (tunedConfig q.L q.ρ q.σ q.Δ q.ε) q.x0 g I.prox ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin ((tunedConfig q.L q.ρ q.σ q.Δ q.ε).T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε := by
    rw [hP, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hGm.aestronglyMeasurable]
    exact (ENNReal.toReal_le_of_le_ofReal (by have := hc.ε0; positivity) hlint).trans h30.le
  exact ⟨hmeas, Filter.Eventually.of_forall hmem, hInt, hIle⟩

end OracleTemplate.CompositeTransport
