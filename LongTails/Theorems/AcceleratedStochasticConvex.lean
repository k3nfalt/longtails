import LongTails.Setups.StochasticSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.AcceleratedStochastic
import LongTails.Proofs.AcceleratedStochasticExecution

open MeasureTheory

namespace OracleTemplate.StochasticGradient.AcceleratedStochasticConvex

open LongTails.Setups.StochasticSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 64 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊

theorem result :
    Convergence LongTails.Setups.StochasticSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q =>
    let K := max 1 ⌈Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 64 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊
    Gradient.accelerated (2 * q.L + 8 * (K : ℝ) * q.σ ^ 2 / q.ε, q.x0), ?_, fun _ _ => trivial⟩
  intro q hp f O h
  rcases hp with ⟨hL, hR, hσ, hε⟩
  rcases h with ⟨g, p, rfl, hc, hg, hlip, ⟨xstar, hm, hdist⟩, ho⟩
  let K := max 1 ⌈Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 64 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊
  let D := 2 * q.L + 8 * (K : ℝ) * q.σ ^ 2 / q.ε
  let P := Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω))
  let output := fun ξ : Fin K → q.Ω => (acceleratedRun g D K 0 q.x0 q.x0 ξ).1
  have hD : 0 < D := by dsimp [D]; positivity
  have hLD : 2 * q.L ≤ D := le_add_of_nonneg_right (by positivity)
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hceil : Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 64 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
  have hdet : Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) ≤ (K : ℝ) := by
    have : 0 ≤ 64 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 := by positivity
    linarith
  have hnoise : 64 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 ≤ (K : ℝ) := by
    linarith [Real.sqrt_nonneg (16 * q.L * q.R ^ 2 / q.ε)]
  have haccuracy := accelerated_tuning_bound q.L q.R q.σ q.ε ‖q.x0 - xstar‖ K
    hL hε (norm_nonneg _) hdist hK hdet hnoise
  have ha := accelerated_expected_rate hD hLD hc hg hlip ho q.x0 xstar hm K hK
  have houtput : Measurable output :=
    ((measurable_acceleratedRun ho.measurable D K 0).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun ξ : Fin K → q.Ω => ((q.x0, q.x0), ξ)))).fst
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  have hprefix := prefix_measurePreserving (p : Measure q.Ω) K
  have hout : Measurable (fun ξ : ℕ → q.Ω => output (fun i => ξ i)) := houtput.comp hprefix.measurable
  have hi : Integrable (fun ξ : ℕ → q.Ω => f (output (fun i => ξ i)) - f xstar) P :=
    hprefix.integrable_comp_of_integrable ha.1
  have he : (∫ ξ : ℕ → q.Ω, f (output (fun i => ξ i)) - f xstar ∂P) ≤ q.ε := by
    have hmout : Measurable (fun ξ : Fin K → q.Ω => f (output ξ) - f xstar) :=
      (hf.comp houtput).sub_const _
    rw [← integral_map hprefix.measurable.aemeasurable hmout.aestronglyMeasurable,
      hprefix.map_eq]
    exact ha.2.trans haccuracy
  let result := fun seed : Unit × (ℕ → q.Ω) => (execute
      { Seed := fun _ => q.Ω
        law := ⟨P, inferInstance⟩
        answer := fun _ (_, x) ω => g x ω } (Gradient.accelerated (D, q.x0)) (fun _ => K) seed.1 seed.2)
  change Measurable result ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
    Integrable (fun seed => f (result seed) - f xstar) ((Measure.dirac ()).prod P) ∧
    (∫ seed, f (result seed) - f xstar ∂(Measure.dirac ()).prod P) ≤ q.ε
  have hexec : result = fun seed => output (fun i => seed.2 i) := by
    funext ⟨⟨⟩, ξ⟩
    exact (execute_accelerated_stochastic p g D q.x0 K ξ)
  rw [hexec]
  refine ⟨hout.comp measurable_snd, xstar, hm, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hi
  · change (∫ seed : Unit × (ℕ → q.Ω), f (output (fun i => seed.2 i)) - f xstar
      ∂(Measure.dirac ()).prod P) ≤ q.ε
    rw [integral_fun_snd (fun ξ : ℕ → q.Ω => f (output (fun i => ξ i)) - f xstar)]
    simpa using he

end OracleTemplate.StochasticGradient.AcceleratedStochasticConvex
