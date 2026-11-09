import LongTails.Proofs.AdamHeavyTailedProcess
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.CovarianceAcceleratedConcentration

open LongTails.Proofs.AdamHeavyTailedProcess
open OracleTemplate.StochasticGeneralized

variable {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

noncomputable def bad (σ : ℝ) (X : Ω → E) (ω : Ω) : ℝ :=
  if 8 * σ < ‖X ω‖ then 1 else 0

lemma bad_measurable {X : Ω → E} (hX : Measurable X) (σ : ℝ) :
    Measurable (bad σ X) := by
  exact Measurable.ite (measurableSet_lt measurable_const hX.norm) measurable_const measurable_const

lemma bad_exp_integrable {X : Ω → E} (hX : Measurable X) (σ : ℝ) :
    Integrable (fun ω => Real.exp (bad σ X ω)) p := by
  apply (integrable_const (3 : ℝ)).mono' (Real.measurable_exp.comp (bad_measurable hX σ)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  change ‖Real.exp (bad σ X ω)‖ ≤ 3
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  unfold bad
  split_ifs
  · exact Real.exp_one_lt_three.le
  · norm_num

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma bad_exp_le {X : Ω → E} {σ : ℝ} (hσ : 0 < σ) (ω : Ω) :
    Real.exp (bad σ X ω) ≤ 1 + ‖X ω‖ ^ 2 / (32 * σ ^ 2) := by
  have hp : 0 < 32 * σ ^ 2 := by positivity
  unfold bad
  split_ifs with h
  · have hs : 64 * σ ^ 2 ≤ ‖X ω‖ ^ 2 := by
      nlinarith [norm_nonneg (X ω)]
    have hr : 2 ≤ ‖X ω‖ ^ 2 / (32 * σ ^ 2) := (le_div_iff₀ hp).mpr (by nlinarith)
    linarith [Real.exp_one_lt_three]
  · rw [Real.exp_zero]
    linarith [div_nonneg (sq_nonneg ‖X ω‖) hp.le]

lemma bad_exp_bound {X : Ω → E} (hX : Measurable X) {σ : ℝ} (hσ : 0 ≤ σ)
    (hint : Integrable (fun ω => ‖X ω‖ ^ 2) p)
    (hvar : (∫ ω, ‖X ω‖ ^ 2 ∂p) ≤ σ ^ 2) :
    (∫ ω, Real.exp (bad σ X ω) ∂p) ≤ 1 + 1 / 32 := by
  by_cases hs : σ = 0
  · have hz : (∫ ω, ‖X ω‖ ^ 2 ∂p) = 0 := by
      have hn : 0 ≤ (∫ ω, ‖X ω‖ ^ 2 ∂p) := integral_nonneg (fun ω => sq_nonneg ‖X ω‖)
      simp only [hs, zero_pow (by decide : 2 ≠ 0)] at hvar
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg ‖X ω‖) hint).mp hz
    have he : (fun ω => Real.exp (bad σ X ω)) =ᵐ[p] fun _ => (1 : ℝ) := by
      filter_upwards [hae] with ω hω
      change ‖X ω‖ ^ 2 = 0 at hω
      have hn : ‖X ω‖ = 0 := by nlinarith [norm_nonneg (X ω)]
      simp [bad, hs, hn]
    rw [integral_congr_ae he]
    norm_num
  · have hsp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hs)
    have hi := (integrable_const (1 : ℝ)).add (hint.div_const (32 * σ ^ 2))
    have hb := integral_mono (bad_exp_integrable hX σ) hi (bad_exp_le hsp)
    simp only [Pi.add_apply] at hb
    rw [integral_add (integrable_const (1 : ℝ)) (hint.div_const (32 * σ ^ 2)),
      integral_div] at hb
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
    have hd : (∫ ω, ‖X ω‖ ^ 2 ∂p) / (32 * σ ^ 2) ≤ 1 / 32 := by
      apply (div_le_iff₀ (show 0 < 32 * σ ^ 2 by positivity)).mpr
      nlinarith
    linarith

lemma bad_compensated_exp_control {X : Ω → E} (hX : Measurable X) {σ : ℝ} (hσ : 0 ≤ σ)
    (hint : Integrable (fun ω => ‖X ω‖ ^ 2) p)
    (hvar : (∫ ω, ‖X ω‖ ^ 2 ∂p) ≤ σ ^ 2) :
    Integrable (fun ω => Real.exp (bad σ X ω - 1 / 32)) p ∧
      (∫ ω, Real.exp (bad σ X ω - 1 / 32) ∂p) ≤ 1 := by
  constructor
  · simpa only [Real.exp_sub] using (bad_exp_integrable (p := p) hX σ).div_const (Real.exp (1 / 32))
  · simp_rw [Real.exp_sub]
    rw [integral_div]
    apply (div_le_one₀ (Real.exp_pos _)).mpr
    exact (bad_exp_bound hX hσ hint hvar).trans (by linarith [Real.add_one_le_exp (1 / 32)])

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure p] in
lemma exponential_tail {Z : Ω → ℝ} (hi : Integrable (fun ω => Real.exp (Z ω)) p)
    (hm : (∫ ω, Real.exp (Z ω) ∂p) ≤ 1) (r : ℝ) :
    p.real {ω | r ≤ Z ω} ≤ Real.exp (-r) := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (Z ω)).le) hi (Real.exp r)
  simp only [Real.exp_le_exp] at h
  have hb : p.real {ω | r ≤ Z ω} ≤ 1 / Real.exp r := by
    apply (le_div_iff₀ (Real.exp_pos r)).mpr
    nlinarith
  simpa only [Real.exp_neg, one_div] using hb

noncomputable def blockIncrement {S Ξ : Type*} (U : S → Ξ → ℝ)
    (n : ℕ) (s : S) (b : Fin n → Ξ) : ℝ :=
  if h : 0 < n then U s (b ⟨0, h⟩) else 0

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] in
lemma unit_cost_exp_control {S : Type*} [MeasurableSpace S]
    {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hU : Measurable (Function.uncurry U))
    (hi : ∀ s, Integrable (fun ω => Real.exp (U s ω)) p)
    (hb : ∀ s, (∫ ω, Real.exp (U s ω) ∂p) ≤ 1) (N : ℕ) (s : S) :
    Integrable (fun ξ => Real.exp (OracleTemplate.StochasticGeneralized.accumulated
      (fun _ => 1) (singleNext next) (blockIncrement U) N s ξ))
      (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, Real.exp (OracleTemplate.StochasticGeneralized.accumulated
      (fun _ => 1) (singleNext next) (blockIncrement U) N s ξ)
      ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ 1 := by
  apply OracleTemplate.StochasticGeneralized.accumulated_exp_control p measurable_const
  · exact measurable_singleNext hn
  · intro n
    change Measurable (fun z : S × (Fin n → Ω) =>
      if h : 0 < n then U z.1 (z.2 ⟨0, h⟩) else 0)
    by_cases h : 0 < n
    · simp only [dite_eq_left h]
      exact hU.comp (show Measurable (fun z : S × (Fin n → Ω) => (z.1, z.2 ⟨0, h⟩)) by fun_prop)
    · simp only [dite_eq_right h]
      exact measurable_const
  · intro v
    simpa [blockIncrement, Function.comp_def, Function.eval] using
      (measurePreserving_eval (fun _ : Fin 1 => p) (0 : Fin 1)).integrable_comp_of_integrable (hi v)
  · intro v
    have he := (measurePreserving_funUnique p (Fin 1)).integral_comp'
      (fun ω => Real.exp (U v ω))
    change (∫ b, Real.exp (U v (b default)) ∂Measure.pi (fun _ : Fin 1 => p)) = _ at he
    simpa [blockIncrement] using he.trans_le (hb v)

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] in
lemma unit_cost_sum {S : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (N : ℕ) (s : S) (ξ : ℕ → Ω) :
    accumulated (fun _ => 1) (singleNext next) (blockIncrement U) N s ξ =
      ∑ t ∈ Finset.range N, U (stateAt next s ξ t) (ξ t) := by
  rw [accumulated_eq_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [blockIncrement, dite_eq_left Nat.zero_lt_one]
  change U (stateAt next s ξ t) ((blockTrace (fun _ => 1) (singleNext next) s ξ t).2 0) = _
  rw [blockTrace_tail, single_blockCalls, Nat.add_zero]

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] in
lemma iid_exp_control {S Ξ : Type*} [MeasurableSpace S] [MeasurableSpace Ξ]
    {P : Measure Ξ} {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hU : Measurable (Function.uncurry U))
    (hi : ∀ s, Integrable (fun ω => Real.exp (U s ω)) p)
    (hb : ∀ s, (∫ ω, Real.exp (U s ω) ∂p) ≤ 1) (N : ℕ) (s : S) :
    Integrable (fun ω => Real.exp (∑ t ∈ Finset.range N,
      U (stateAt next s (fun k => ξ k ω) t) (ξ t ω))) P ∧
    (∫ ω, Real.exp (∑ t ∈ Finset.range N,
      U (stateAt next s (fun k => ξ k ω) t) (ξ t ω)) ∂P) ≤ 1 := by
  have hc := unit_cost_exp_control hn hU hi hb N s
  simp_rw [unit_cost_sum] at hc
  let F : (ℕ → Ω) → ℝ := fun ζ => Real.exp (∑ t ∈ Finset.range N, U (stateAt next s ζ t) (ζ t))
  have hFm : Measurable F := by
    apply Real.measurable_exp.comp
    apply Finset.measurable_sum
    intro t _
    exact hU.comp ((measurable_stateAt hn s t).prodMk (measurable_pi_apply t))
  have hp := hsamples.stream_law
  have he : (∫ ω, F (fun k => ξ k ω) ∂P) =
      (∫ ζ, F ζ ∂Measure.infinitePi (fun _ : ℕ => p)) := by
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hFm.aestronglyMeasurable).symm
  exact ⟨hp.integrable_comp_of_integrable hc.1, he.trans_le hc.2⟩

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] in
lemma exponential_tail_measure {Z : Ω → ℝ} (hi : Integrable (fun ω => Real.exp (Z ω)) p)
    (hm : (∫ ω, Real.exp (Z ω) ∂p) ≤ 1) (r : ℝ) :
    p {ω | r ≤ Z ω} ≤ ENNReal.ofReal (Real.exp (-r)) := by
  have he : p {ω | r ≤ Z ω} = ENNReal.ofReal (p.real {ω | r ≤ Z ω}) := by
    exact (ENNReal.ofReal_toReal (measure_ne_top p _)).symm
  rw [he]
  exact ENNReal.ofReal_le_ofReal (exponential_tail hi hm r)

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] in
lemma iid_exponential_tail {S Ξ : Type*} [MeasurableSpace S] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hU : Measurable (Function.uncurry U))
    (hi : ∀ s, Integrable (fun ω => Real.exp (U s ω)) p)
    (hb : ∀ s, (∫ ω, Real.exp (U s ω) ∂p) ≤ 1) (N : ℕ) (s : S) (r : ℝ) :
    P {ω | r ≤ ∑ t ∈ Finset.range N, U (stateAt next s (fun k => ξ k ω) t) (ξ t ω)} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have hc := iid_exp_control hsamples hn hU hi hb N s
  exact exponential_tail_measure hc.1 hc.2 r

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure p] in
lemma compensated_exp_control {Z : Ω → ℝ} {c : ℝ}
    (hi : Integrable (fun ω => Real.exp (Z ω)) p)
    (hb : (∫ ω, Real.exp (Z ω) ∂p) ≤ 1 + c) :
    Integrable (fun ω => Real.exp (Z ω - c)) p ∧
      (∫ ω, Real.exp (Z ω - c) ∂p) ≤ 1 := by
  constructor
  · simpa only [Real.exp_sub] using hi.div_const (Real.exp c)
  · simp_rw [Real.exp_sub]
    rw [integral_div]
    apply (div_le_one₀ (Real.exp_pos _)).mpr
    exact hb.trans (by linarith [Real.add_one_le_exp c])

end LongTails.Proofs.CovarianceAcceleratedConcentration
