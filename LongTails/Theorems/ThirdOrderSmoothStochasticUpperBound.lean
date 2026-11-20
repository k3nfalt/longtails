import LongTails.Setups.StochasticThirdOrderSmoothNonconvex
import LongTails.Proofs.LookaheadMomentumTuning
import LongTails.Proofs.GradientDependentLocal
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveIID

open MeasureTheory
open scoped ENNReal

namespace LongTails.Theorems.ThirdOrderSmoothStochasticUpperBound

open OracleTemplate OracleTemplate.LookaheadMomentum
open LongTails.Setups.StochasticThirdOrderSmoothNonconvex

noncomputable def budget : (let S := LongTails.Setups.StochasticThirdOrderSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈100000 * (1 + q.σ ^ 2 / q.ε ^ 2 + q.L₁ * q.Δ / q.ε ^ 2 + q.Δ * q.σ ^ 2 / q.ε ^ 3 * min (q.L₁ / q.ε) (min (Real.sqrt (q.L₂ / q.ε)) ((q.L₃ / q.ε) ^ (1 / 3 : ℝ))))⌉₊

theorem result : Convergence LongTails.Setups.StochasticThirdOrderSmoothNonconvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨fun q => lookahead q (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε), ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  obtain ⟨hL₁, hL₂, hL₃, -, hΔ, hε⟩ := hq
  obtain ⟨g, μ, P, hIID, hO, hf, hl₁, hl₂, hl₃, hgap, hgm, hgi, hgmean, hgi2, hgvar⟩ := hadm
  dsimp only
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  have hO' : O = oracleOf q g P := hO
  subst hO'
  have hc := tuned_hyp (L₂ := q.L₂) (L₃ := q.L₃) (σ := q.σ) hL₁ hΔ hε
  have hcalls := tuned_calls (σ := q.σ) hL₁ hL₂ hL₃ hΔ hε
  obtain ⟨hd₀, hd₁, hd₂⟩ := LongTails.Proofs.GradientDependentLocal.derivative_chain hf
  have hgrad : ∀ x, HasGradientAt f (gradient f x) x := fun x =>
    (hf.differentiable (by norm_num) x).hasGradientAt
  have Or : OracleTemplate.CompositeTransport.OracleHyp g (gradient f) (μ : Measure q.Ω) q.σ :=
    ⟨hgm, hgi, hgmean, hgi2, hgvar⟩
  have hpt : ∀ (τ : (lookahead q (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε)).Seed)
      (ξ : (k : ℕ) → (oracleOf q g P).Seed k),
      execute (oracleOf q g P) (lookahead q (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε))
        (fun _ => budget q 0) τ ξ =
        (traj (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) q.x0 g (ξ : ℕ → q.Ω)
          (τ : Fin ((tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).T + 1)).val).1 :=
    fun τ ξ => execute_eq q (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) g ξ hc.n0 P _ τ
      (by simp only [budget]; exact hcalls)
  simp only [hpt]
  have hk := keep_bounds (cfg := tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) hc.γ0 hc.γ1
  have hkγ : (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).γ ≤
      1 - keep (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) := by
    have h1 : 1 - keep (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) =
        (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).γ *
          (3 - (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).γ) / 2 := by unfold keep; ring
    rw [h1]
    nlinarith [hc.γ0, hc.γ1]
  have hD : ∀ x x' : q.E, ‖x' - x‖ ≤ (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).η →
      ‖drift (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) (gradient f) x x'‖ ≤
      (1 - keep (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε)) * (q.ε / 8) := by
    intro x x' hx
    have h := drift_le hL₁.le hL₂.le hL₃.le hd₁ hd₂ hl₁ hl₂ hl₃
      (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) hc.γ0 hc.γ1
      (tr_pos (L₂ := q.L₂) (L₃ := q.L₃) hL₁ hε).le (min_le_left _ _)
      (tr_case hL₁ hL₂ hL₃ hε) x x' hx
    exact h.trans (mul_le_mul_of_nonneg_right hkγ (by positivity))
  obtain ⟨hmeas, hlint⟩ := expected_bound hL₁.le hgrad hl₁ hc hD hgap Or
  have hgc : Continuous (gradient f) := by
    have : LipschitzWith (Real.toNNReal q.L₁) (gradient f) := LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL₁.le]; exact hl₁ a b
    exact this.continuous
  have hGm : Measurable (fun ω : Fin ((tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).T + 1) × (ℕ → q.Ω) =>
      ‖gradient f (traj (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) q.x0 g ω.2 ω.1.val).1‖) :=
    (hgc.measurable.comp hmeas).norm
  have hfin : ∫⁻ ω, ENNReal.ofReal ‖gradient f (traj (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) q.x0 g ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin ((tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).T + 1))).toMeasure.prod (Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlint
  have hInt : Integrable (fun ω : Fin ((tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).T + 1) × (ℕ → q.Ω) =>
      ‖gradient f (traj (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) q.x0 g ω.2 ω.1.val).1‖)
      ((PMF.uniformOfFintype (Fin ((tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) := by
    rw [hP]
    have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hGm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  have hIle : ∫ ω : Fin ((tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).T + 1) × (ℕ → q.Ω), ‖gradient f (traj (tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε) q.x0 g ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin ((tunedConfig q.L₁ q.L₂ q.L₃ q.σ q.Δ q.ε).T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε := by
    rw [hP, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hGm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hlint
  exact ⟨hmeas, hInt, hIle⟩

end LongTails.Theorems.ThirdOrderSmoothStochasticUpperBound
