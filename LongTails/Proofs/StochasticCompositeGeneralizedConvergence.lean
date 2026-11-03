import LongTails.Proofs.StochasticCompositeGeneralizedGrowth

open MeasureTheory Set ProbabilityTheory
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

lemma measurableSet_goodEvents (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω) [SFinite μ]
    {g : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry g)) (hgm : Measurable I.grad)
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0)) (xs : p.E) (n : ℕ) :
    MeasurableSet {ξ | GoodEvents p I μ g xs n ξ} := by
  have hi : Measurable (fun ξ : ℕ → p.Ω => (initialState p, ξ)) := measurable_const.prodMk measurable_id
  have hs : Measurable (fun ξ : ℕ → p.Ω => ((initialState p, (0 : ℝ)), ξ)) := measurable_const.prodMk measurable_id
  have hnext := measurable_phaseNext p I hg hprox
  have hF := (StochasticGeneralized.accumulated_measurable (measurable_phaseCost p) hnext
    (measurable_phaseFailure p I hg hgm) n).comp hi
  have hQ := (StochasticGeneralized.accumulated_measurable (measurable_phaseCost p) hnext
    (measurable_phaseEnergy p I hg hgm) n).comp hi
  have hS := (StochasticGeneralized.accumulated_measurable ((measurable_phaseCost p).comp measurable_fst)
    (measurable_phaseSignedNext p I μ hg hgm xs hprox)
    (measurable_phaseSigned p I μ hg hgm xs) n).comp hs
  simp only [Function.comp_def, Function.uncurry_apply_pair] at hF hQ hS
  exact (measurableSet_lt hF measurable_const).inter
    ((measurableSet_lt hQ measurable_const).inter (measurableSet_lt hS measurable_const))

lemma execute_accuracy_on_goodEvents (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (hx : p.x0 ∈ I.Q) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hgap : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ)
    {G : ℝ} (hG : ‖I.grad xs‖ ≤ G) (P : ProbabilityMeasure (ℕ → p.Ω)) (ξ : ℕ → p.Ω) (K B : ℕ)
    (hg : GoodEvents p I μ g xs (4 * K) ξ)
    (hK : 20 * Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * G) * p.R ^ 2 / p.ε) +
      (6 + 256 * p.L1 * p.R) * Real.log (2 + (3 + 192 * p.L1 * p.R) *
        Real.sqrt (p.Δ / (p.L0 * p.R ^ 2))) ≤ K)
    (hB : StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ (4 * K) ≤ B) :
    let x := execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) ω => oracleReply p I g query ω }
      (algorithm p) (fun _ => B) () ξ
    x ∈ I.Q ∧ I.f x + I.ψ x - (I.f xs + I.ψ xs) ≤ p.ε := by
  have ht := goodEvents_stopped p I μ ho h hR hσ hα hα2 hΔ hε hδ hδ1 xs hxs hmin hx hd hgap hG ξ K hg hK
  have ha := goodEvents_phase_accuracy p I μ ho h hR hσ hα hα2 hΔ hε hδ hδ1 xs hxs hmin hx hd hgap hG ξ K hg hK
  dsimp only
  erw [execute_eq_rawAdvance p I g P B () ξ]
  rw [rawAdvance_after_stopped_phase p I g h.hL0 h.hL1 hR hσ hΔ ξ (4 * K) B hB ht]
  exact ha

lemma execution_high_probability (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (hx : p.x0 ∈ I.Q) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hgap : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ)
    {G : ℝ} (hG : ‖I.grad xs‖ ≤ G) (P : ProbabilityMeasure (ℕ → p.Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → p.Ω) => ξ k) μ (P : Measure _))
    (hprox : Measurable (fun t : ℝ × p.E × p.E => if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0)) (K B : ℕ)
    (hK : 20 * Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * G) * p.R ^ 2 / p.ε) +
      (6 + 256 * p.L1 * p.R) * Real.log (2 + (3 + 192 * p.L1 * p.R) *
        Real.sqrt (p.Δ / (p.L0 * p.R ^ 2))) ≤ K)
    (hB : ∀ ξ, StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ (4 * K) ≤ B) :
    ((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → p.Ω) |
      let x := execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) ω => oracleReply p I g query ω }
        (algorithm p) (fun _ => B) w.1 w.2
      x ∉ I.Q ∨ p.ε < I.f x + I.ψ x - (I.f xs + I.ψ xs)} ≤ ENNReal.ofReal p.δ := by
  have ht := iid_goodEvents_probability p I μ ho h.grad h.cont.measurable hprox h.hL0 h.hL1 hR hσ
    hα hα2 hΔ hε hδ hδ1 xs (4 * K) (P : Measure _) (fun k (ξ : ℕ → p.Ω) => ξ k) h_samples
  have hm := (measurableSet_goodEvents p I μ ho.measurable h.cont.measurable hprox xs (4 * K)).compl
  have hsnd : HasLaw (Prod.snd : Unit × (ℕ → p.Ω) → ℕ → p.Ω) (P : Measure _)
      ((Measure.dirac ()).prod (P : Measure _)) :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  calc
    _ ≤ ((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → p.Ω) |
        ¬ GoodEvents p I μ g xs (4 * K) w.2} := by
      apply measure_mono
      rintro ⟨⟨⟩, ξ⟩ hfail hgood
      have ha := execute_accuracy_on_goodEvents p I μ ho h hR hσ hα hα2 hΔ hε hδ hδ1
        xs hxs hmin hx hd hgap hG P ξ K B hgood hK (hB ξ)
      exact hfail.elim (fun hn => hn ha.1) (not_lt_of_ge ha.2)
    _ = (P : Measure _) {ξ | ¬ GoodEvents p I μ g xs (4 * K) ξ} := hsnd.measure_eq hm
    _ ≤ ENNReal.ofReal p.δ := by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal ht

end OracleTemplate.StochasticCompositeGeneralized
