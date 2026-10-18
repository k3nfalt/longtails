import LongTails.Setups.MeanSquaredHolderNonconvex
import LongTails.Proofs.DyadicHolderDescent
import LongTails.Proofs.DyadicHolderTuning
import LongTails.Proofs.AdaptiveIID

open MeasureTheory

namespace OracleTemplate.DyadicHolder

open LongTails.Setups.MeanSquaredHolderNonconvex

theorem convergence : Convergence LongTails.Setups.MeanSquaredHolderNonconvex.spec
    (fun q _ => ⌈800 * (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 *
      (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 +
        q.Δ * q.M ^ (1 / (2 * q.ν)) * q.σ ^ (2 - 1 / q.ν) / q.ε ^ 3)⌉₊) := by
  apply convergence_of_public_budget (S := spec) (fun q => ⌈800 *
    (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 * (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 +
      q.Δ * q.M ^ (1 / (2 * q.ν)) * q.σ ^ (2 - 1 / q.ν) / q.ε ^ 3)⌉₊)
  refine ⟨fun q => dyadicVR (tcfg q.L q.M q.ν q.σ q.Δ q.ε) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  dsimp only
  obtain ⟨hL, hM, hν1, hν2, hσ, hΔ, hε⟩ := hq
  obtain ⟨g, p, P, hIID, rfl, hgrad, hlip, hgap, hgm, hint, hmean, hvi, hvar, hdi, hmsh⟩ := hadm
  have h : TuneHyp q.L q.M q.ν q.σ q.Δ q.ε := ⟨hL, hM, hν1, hν2, hσ, hΔ, hε⟩
  have H : Hyp (p : Measure q.Ω) f g q.L q.M q.ν q.σ :=
    ⟨hgrad, hlip, hgm, hint, hmean, hvi, hvar, hdi, hmsh, hL, hM, by linarith⟩
  set cfg := tcfg q.L q.M q.ν q.σ q.Δ q.ε
  set B := ⌈800 * (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 *
    (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 +
      q.Δ * q.M ^ (1 / (2 * q.ν)) * q.σ ^ (2 - 1 / q.ν) / q.ε ^ 3)⌉₊
  have hbatch : ∀ k, 1 ≤ cfg.batch k := by
    intro k
    unfold DyadicConfig.batch
    split_ifs
    · exact tbA_pos q.σ q.ε
    · exact tb_pos q.L q.M q.ν q.σ q.Δ q.ε _
  have hB : off cfg (cfg.K + 1) ≤ B := by
    have := h.calls
    exact_mod_cast this.trans (Nat.le_ceil _)
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  have hexec : ∀ (τ : Fin (cfg.K + 1)) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (dyadicVR cfg q.x0) (fun _ => B)
        (show (dyadicVR cfg q.x0).Seed from τ) ξ = X cfg g q.x0 0 ξ τ.val :=
    fun τ ξ => execute_dyadicVR cfg hbatch g P q.x0 B τ ξ hB
  have hmX : Measurable (fun ω : Fin (cfg.K + 1) × (ℕ → q.Ω) => X cfg g q.x0 0 ω.2 ω.1.val) :=
    measurable_from_prod_countable_right fun τ => measurable_X hgm q.x0 0 τ.val
  have hout : (fun seed : (dyadicVR cfg q.x0).Seed × ((k : ℕ) → q.Ω) =>
      (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (dyadicVR cfg q.x0) (fun _ => B) seed.1 seed.2)) =
      fun ω => X cfg g q.x0 0 ω.2 ω.1.val := by
    funext seed; exact hexec seed.1 seed.2
  refine ⟨?_, ?_⟩
  · rw [hout]; exact hmX
  have hfun : (fun ω : (dyadicVR cfg q.x0).Seed × (ℕ → q.Ω) =>
      ‖gradient f (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω =>
        (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (dyadicVR cfg q.x0) (fun _ => B) ω.1 ω.2)‖) =
      fun ω => ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖ := by
    funext ω; rw [hexec ω.1 ω.2]
  rw [hfun]
  change Integrable (fun ω : Fin (cfg.K + 1) × (ℕ → q.Ω) =>
      ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖)
      ((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : Fin (cfg.K + 1) × (ℕ → q.Ω), ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  have hm : Measurable (fun ω : Fin (cfg.K + 1) × (ℕ → q.Ω) =>
      ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖) :=
    (H.grad_continuous.measurable.comp hmX).norm
  have hL' := H.master_lintegral cfg q.x0 h.eta_pos (tbA_pos q.σ q.ε)
    (tb_pos q.L q.M q.ν q.σ q.Δ q.ε)
    (β := q.ε ^ 2 / (32 * ((tJ q.L q.M q.ν q.σ q.Δ q.ε : ℝ) + 1))) (V := q.ε ^ 2 / 16)
    (fun j _ => h.beta j) h.variance hgap h.accuracy
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL'
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL'

end OracleTemplate.DyadicHolder
