import LongTails.Proofs.SublevelPLConvergence

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.SublevelRobustGradient

open LongTails.Setups.SublevelPLBoundedVariance
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

lemma convergence : Convergence spec (fun p _ =>
    steps p.L p.τ p.α p.ε *
      (subbatches p.L p.τ p.α p.Δ p.ε * subsize p.L p.τ p.α p.σ p.Δ p.ε)) := by
  apply convergence_of_public_budget (S := spec)
    (fun pub => steps pub.L pub.τ pub.α pub.ε *
      (subbatches pub.L pub.τ pub.α pub.Δ pub.ε * subsize pub.L pub.τ pub.α pub.σ pub.Δ pub.ε))
  refine ⟨fun pub => method pub.L pub.τ pub.α pub.σ pub.Δ pub.ε pub.x0, ?_, fun _ _ => trivial⟩
  intro p hp f O hadm
  rcases hadm with ⟨g, P0, P, hIID, rfl, hgr, hlip, hbdd, hpl, hx0, hg, hgi, hmean, h2i, hvar⟩
  obtain ⟨hL, hτ, hα1, hα2, hσ, hΔ, hε⟩ := hp
  have hv : Valid p.L p.τ p.α p.σ p.Δ p.ε := ⟨hL, hτ, hα1, hα2, hσ, hΔ, hε⟩
  have hm : ∀ x, (⨅ y, f y) ≤ f x := fun x => ciInf_le hbdd x
  have H : Hyp f (⨅ y, f y) p.L p.τ p.α p.x0 := ⟨hL, hτ, hα1, hα2, hgr, hlip, hm, hpl⟩
  have ho : Oracle (P0 : Measure p.Ω) f g p.σ := ⟨hg, hgi, hmean, h2i, hvar⟩
  have hgrad : Measurable (gradient f) := gradient_measurable hL hlip
  have hfm : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  set n := subbatches p.L p.τ p.α p.Δ p.ε * subsize p.L p.τ p.α p.σ p.Δ p.ε with hn
  set K := steps p.L p.τ p.α p.ε with hK
  set G := blockMap p.L p.τ p.α p.σ p.Δ p.ε g with hG
  have hGm : Measurable (Function.uncurry G) := measurable_blockMap p.L p.τ p.α p.σ p.Δ p.ε hg
  set μ := (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => (P0 : Measure p.Ω))
    with hμ
  have hexp := expected_gap (P0 : Measure p.Ω) hv H ho hx0 hgrad
  -- execution identity
  have hres : (fun seed : Unit × (ℕ → p.Ω) =>
      execute ({ Seed := fun _ => p.Ω
                 law := P
                 answer := fun _ (_, x) seed => g x seed } : OracleTemplate.Oracle p.E p.E)
        (method p.L p.τ p.α p.σ p.Δ p.ε p.x0) (fun _ => K * n) seed.1 seed.2) =
      fun seed => iter p.L G p.x0 (blocks n seed.2) K := by
    funext ⟨⟨⟩, ξ⟩
    exact execute_method P g p.L p.τ p.α p.σ p.Δ p.ε p.x0 K ξ
  change spec.successful p f
    (fun seed : Unit × (ℕ → p.Ω) =>
      execute ({ Seed := fun _ => p.Ω
                 law := P
                 answer := fun _ (_, x) seed => g x seed } : OracleTemplate.Oracle p.E p.E)
        (method p.L p.τ p.α p.σ p.Δ p.ε p.x0) (fun _ => K * n) seed.1 seed.2)
    ⟨(Measure.dirac ()).prod (P : Measure (ℕ → p.Ω)), inferInstance⟩
  rw [hres]
  -- the map seed ↦ blocks n seed.2 is measure preserving onto μ
  have hsnd : MeasurePreserving (Prod.snd : Unit × (ℕ → p.Ω) → (ℕ → p.Ω))
      ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → p.Ω))) (P : Measure (ℕ → p.Ω)) :=
    measurePreserving_snd
  have hblocks := blocks_preserving (P0 : Measure p.Ω) (P : Measure (ℕ → p.Ω))
    hIID.independent hIID.marginal n
  have hmap : MeasurePreserving (fun seed : Unit × (ℕ → p.Ω) => blocks n seed.2)
      ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → p.Ω))) μ :=
    hblocks.comp hsnd
  have hout : Measurable (fun ζ : ℕ → Fin n → p.Ω => f (iter p.L G p.x0 ζ K) - ⨅ y, f y) :=
    (hfm.comp (measurable_iter p.L hGm p.x0 K)).sub_const _
  have hnonneg : ∀ ζ, 0 ≤ f (iter p.L G p.x0 ζ K) - ⨅ y, f y := fun ζ => by
    linarith [hm (iter p.L G p.x0 ζ K)]
  have hlin : (∫⁻ seed : Unit × (ℕ → p.Ω), ENNReal.ofReal
      (f (iter p.L G p.x0 (blocks n seed.2) K) - ⨅ y, f y)
      ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → p.Ω)))) ≤
      ENNReal.ofReal p.ε := by
    have h := hmap.lintegral_comp (ENNReal.measurable_ofReal.comp hout)
    exact h.trans_le hexp
  have hmeas : Measurable (fun seed : Unit × (ℕ → p.Ω) =>
      f (iter p.L G p.x0 (blocks n seed.2) K) - ⨅ y, f y) :=
    hout.comp hmap.measurable
  refine ⟨?_, ?_⟩
  · refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc (∫⁻ seed, ‖f (iter p.L G p.x0 (blocks n seed.2) K) - ⨅ y, f y‖ₑ
          ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → p.Ω))))
        = ∫⁻ seed, ENNReal.ofReal (f (iter p.L G p.x0 (blocks n seed.2) K) - ⨅ y, f y)
            ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → p.Ω))) := by
          apply lintegral_congr
          intro seed
          rw [← ofReal_norm, Real.norm_of_nonneg (hnonneg _)]
      _ ≤ ENNReal.ofReal p.ε := hlin
      _ < ⊤ := ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun seed => hnonneg _))
      hmeas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hlin

end OracleTemplate.SublevelRobustGradient
