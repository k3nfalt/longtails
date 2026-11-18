import LongTails.Setups.HolderNoiseNonconvex
import LongTails.Proofs.HolderNoiseAccuracy
import LongTails.Proofs.AdaptiveIID

open MeasureTheory

namespace OracleTemplate.HolderNoise

open DyadicHolder LongTails.Setups.HolderNoiseNonconvex

lemma execution_successful (q : Params) (hq : spec.valid q) (cfg : DyadicConfig)
    (B : ℕ) (hbatch : ∀ k, 1 ≤ cfg.batch k) (hB : off cfg (cfg.K + 1) ≤ B)
    (f : q.E → ℝ)
    (hacc : ∀ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω),
      CenteredDyadic.Hyp (p : Measure q.Ω) f g q.L q.M q.ν q.σ →
      (∀ x, f q.x0 - f x ≤ q.Δ) →
      ∫⁻ ω, ENNReal.ofReal ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖
        ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod
          (Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω))) ≤ ENNReal.ofReal q.ε)
    (O : Oracle (q.E × q.E) (q.E × q.E)) (hadm : spec.admissible q f O) :
    spec.successful q f
      (fun seed : (dyadicVR cfg q.x0).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (dyadicVR cfg q.x0) (fun _ => B) seed.1 seed.2)
      ⟨((dyadicVR cfg q.x0).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hL, hM, hν, _, _, _, hε⟩ := hq
  obtain ⟨g, p, P, hIID, rfl, hgrad, hlip, hgap, hgm, hint, hmean, hvi, hvar, hdi, hmsh⟩ := hadm
  have H : CenteredDyadic.Hyp (p : Measure q.Ω) f g q.L q.M q.ν q.σ :=
    ⟨hgrad, hlip, hgm, hint, hmean, hvi, hvar, hdi, hmsh, hL, hM, hν⟩
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
  · erw [hout]; exact hmX
  have hfun : (fun ω : (dyadicVR cfg q.x0).Seed × (ℕ → q.Ω) =>
      ‖gradient f (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω =>
        (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (dyadicVR cfg q.x0) (fun _ => B) ω.1 ω.2)‖) =
      fun ω => ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖ := by
    funext ω; rw [hexec ω.1 ω.2]
  erw [hfun]
  change Integrable (fun ω : Fin (cfg.K + 1) × (ℕ → q.Ω) =>
      ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖)
      ((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : Fin (cfg.K + 1) × (ℕ → q.Ω), ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  have hm : Measurable (fun ω : Fin (cfg.K + 1) × (ℕ → q.Ω) =>
      ‖gradient f (X cfg g q.x0 0 ω.2 ω.1.val)‖) :=
    (H.grad_continuous.measurable.comp hmX).norm
  have hL' := hacc g p H hgap
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL'
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL'

end OracleTemplate.HolderNoise
