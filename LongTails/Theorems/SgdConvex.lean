import LongTails.Setups.StochasticSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.SgdConvex
import LongTails.Proofs.SgdExecution

open MeasureTheory

namespace OracleTemplate.StochasticGradient.SgdConvex

open LongTails.Setups.StochasticSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈4 * q.L * q.R ^ 2 / q.ε + 4 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊

theorem result :
    Convergence LongTails.Setups.StochasticSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => sgd (1 / (2 * q.L + 2 * q.σ ^ 2 / q.ε)) q.x0, ?_, fun _ _ => trivial⟩
  intro q hp f O h
  rcases hp with ⟨hL, hR, hσ, hε⟩
  rcases h with ⟨g, p, rfl, hc, hg, hlip, ⟨xstar, hm, hdist⟩, ho⟩
  let η := 1 / (2 * q.L + 2 * q.σ ^ 2 / q.ε)
  let K := max 1 ⌈4 * q.L * q.R ^ 2 / q.ε + 4 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊
  let P := Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω))
  let output := fun ξ : Fin K → q.Ω => (K : ℝ)⁻¹ • (run g η K q.x0 ξ).2
  have hden : 0 < 2 * q.L + 2 * q.σ ^ 2 / q.ε := by positivity
  have hη : 0 < η := one_div_pos.mpr hden
  have hηeq : η * (2 * q.L + 2 * q.σ ^ 2 / q.ε) = 1 := by
    dsimp [η]
    field_simp
  have hηL : η * q.L ≤ 1 / 2 := by
    have := mul_nonneg hη.le (show 0 ≤ 2 * q.σ ^ 2 / q.ε by positivity)
    nlinarith [hηeq]
  have hnoise : η * q.σ ^ 2 ≤ q.ε / 2 := by
    have heq : η * (2 * q.L * q.ε + 2 * q.σ ^ 2) = q.ε := by
      calc
        _ = (η * (2 * q.L + 2 * q.σ ^ 2 / q.ε)) * q.ε := by field_simp
        _ = q.ε := by rw [hηeq, one_mul]
    nlinarith [mul_pos (mul_pos hη hL) hε]
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hceil : 2 * q.R ^ 2 / (η * q.ε) ≤ (K : ℝ) := by
    have heq : 2 * q.R ^ 2 / (η * q.ε) =
        4 * q.L * q.R ^ 2 / q.ε + 4 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 := by
      dsimp [η]
      field_simp
      ring
    rw [heq]
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
  have haccuracy : ‖q.x0 - xstar‖ ^ 2 / (η * K) + η * q.σ ^ 2 ≤ q.ε := by
    have hR2 : ‖q.x0 - xstar‖ ^ 2 ≤ q.R ^ 2 := by nlinarith [norm_nonneg (q.x0 - xstar)]
    have hh := (div_le_iff₀ (mul_pos hη hε)).mp hceil
    have hinit : ‖q.x0 - xstar‖ ^ 2 / (η * K) ≤ q.ε / 2 := by
      apply (div_le_iff₀ (mul_pos hη hKr)).mpr
      nlinarith
    linarith
  have ha := expected_average hL hη hηL hc hg hlip hm ho K hK q.x0
  have houtput : Measurable output :=
    (((measurable_run ho.measurable η K).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin K → q.Ω => (q.x0, ξ)))).snd).const_smul _
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
        answer := fun _ (_, x) ω => g x ω } (sgd η q.x0) (fun _ => K) seed.1 seed.2)
  change Measurable result ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
    Integrable (fun seed => f (result seed) - f xstar) ((Measure.dirac ()).prod P) ∧
    (∫ seed, f (result seed) - f xstar ∂(Measure.dirac ()).prod P) ≤ q.ε
  have hexec : result = fun seed => output (fun i => seed.2 i) := by
    funext ⟨⟨⟩, ξ⟩
    exact (execute_sgd p g η q.x0 K hK ξ)
  rw [hexec]
  refine ⟨hout.comp measurable_snd, xstar, hm, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hi
  · change (∫ seed : Unit × (ℕ → q.Ω), f (output (fun i => seed.2 i)) - f xstar
      ∂(Measure.dirac ()).prod P) ≤ q.ε
    rw [integral_fun_snd (fun ξ : ℕ → q.Ω => f (output (fun i => ξ i)) - f xstar)]
    simpa using he

end OracleTemplate.StochasticGradient.SgdConvex
