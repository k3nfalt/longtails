import LongTails.Setups.LocalHiddenConvexStochastic
import LongTails.Proofs.HiddenConvexExecution

open MeasureTheory Metric

namespace OracleTemplate.LocalHiddenConvex

open LongTails.Setups.LocalHiddenConvexStochastic

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈300000 * (Real.sqrt (q.L * q.R ^ 2 / q.ε) + q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2) * Real.log (300000 * (2 + q.L * q.R ^ 2 / q.ε + q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2)) ^ 2⌉₊

theorem result : Convergence LongTails.Setups.LocalHiddenConvexStochastic.spec budget := by
  refine ⟨fun q => safeguardedSimilarTriangles q.L q.σ q.R q.x0, ?_, fun _ _ => trivial⟩
  rintro q hp I O h
  rcases hp with ⟨hL, hR, hσ, hμ, hLJ, hε, hreg⟩
  rcases h with ⟨g, p, rfl, heq, hU, hH, hHd, hcJ, hJ, hF, hlip, ⟨xstar, hxs, hmin⟩, ho⟩
  have hm : LocalModel I.F I.H I.c I.J I.U q.x0 q.R q.μ q.LJ := ⟨heq, hU, hH, hHd, hcJ, hJ⟩
  have hbud := budget_sufficient (L := q.L) (σ := q.σ) (R := q.R) (ε := q.ε) hL hσ hR hε
  set K := ⌈300000 * (Real.sqrt (q.L * q.R ^ 2 / q.ε) + q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2) *
    Real.log (300000 * (2 + q.L * q.R ^ 2 / q.ε + q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2)) ^ 2⌉₊ with hK
  obtain ⟨hKpos, hacc⟩ := hbud
  let P := Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω))
  let output := fun ξ : Fin K → q.Ω => (safeguardedRun g q.L q.σ q.R q.x0 K 0 q.x0 q.x0 ξ).1
  have ha := expected_gap hm hR hμ hLJ hreg hL hσ hF hlip ho hxs hmin K hKpos
  have houtput : Measurable output :=
    ((measurable_safeguardedRun ho.measurable q.L q.σ q.R q.x0 K 0).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun ξ : Fin K → q.Ω => ((q.x0, q.x0), ξ)))).fst
  have hf : Measurable I.F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  have hprefix := StochasticGradient.prefix_measurePreserving (p : Measure q.Ω) K
  have hout : Measurable (fun ξ : ℕ → q.Ω => output (fun i => ξ i)) :=
    houtput.comp hprefix.measurable
  have hi : Integrable (fun ξ : ℕ → q.Ω => I.F (output (fun i => ξ i)) - I.F xstar) P :=
    hprefix.integrable_comp_of_integrable ha.1
  have he : (∫ ξ : ℕ → q.Ω, I.F (output (fun i => ξ i)) - I.F xstar ∂P) ≤ q.ε := by
    have hmout : Measurable (fun ξ : Fin K → q.Ω => I.F (output ξ) - I.F xstar) :=
      (hf.comp houtput).sub_const _
    rw [← integral_map hprefix.measurable.aemeasurable hmout.aestronglyMeasurable,
      hprefix.map_eq]
    exact ha.2.trans hacc
  let result := fun seed : Unit × (ℕ → q.Ω) => (execute
      { Seed := fun _ => q.Ω
        law := ⟨P, inferInstance⟩
        answer := fun _ (_, x) ω => g x ω } (safeguardedSimilarTriangles q.L q.σ q.R q.x0)
        (fun _ => K) seed.1 seed.2)
  change Measurable result ∧ ∃ xstar, IsMinOn I.F Set.univ xstar ∧
    Integrable (fun seed => I.F (result seed) - I.F xstar) ((Measure.dirac ()).prod P) ∧
    (∫ seed, I.F (result seed) - I.F xstar ∂(Measure.dirac ()).prod P) ≤ q.ε
  have hexec : result = fun seed => output (fun i => seed.2 i) := by
    funext ⟨⟨⟩, ξ⟩
    exact execute_safeguarded p g q.L q.σ q.R q.x0 K ξ
  rw [hexec]
  refine ⟨hout.comp measurable_snd, xstar, hmin, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hi
  · change (∫ seed : Unit × (ℕ → q.Ω), I.F (output (fun i => seed.2 i)) - I.F xstar
      ∂(Measure.dirac ()).prod P) ≤ q.ε
    rw [integral_fun_snd (fun ξ : ℕ → q.Ω => I.F (output (fun i => ξ i)) - I.F xstar)]
    simpa using he

end OracleTemplate.LocalHiddenConvex
