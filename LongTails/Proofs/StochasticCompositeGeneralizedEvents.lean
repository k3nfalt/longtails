import LongTails.Proofs.StochasticCompositeGeneralizedSigned
import LongTails.Proofs.StochasticCompositeGeneralizedEnergy

open MeasureTheory
open scoped RealInnerProductSpace
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

lemma EvaluationReady.center_bound (p : Public) (I : Instance p) (hσ : 0 ≤ p.σ)
    {s : State p.E} (hr : EvaluationReady p I s) :
    ‖I.grad (queryPoint p s) - s.center‖ ≤ clipRadius p s.iteration / 2 := by
  have hb : 384 * p.σ ≤ clipRadius p s.iteration := le_max_left _ _
  linarith [hr.2.2.2]

lemma finiteSignedError_eq (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (hσ : 0 ≤ p.σ) (xs : p.E) (s : State p.E)
    (hr : EvaluationReady p I s) (n : ℕ) (hn : 0 < n) (ξ : Fin n → p.Ω) :
    finiteSignedError p I μ g xs n s ξ =
      stepWeight p s * ⟪xs - s.z, finiteError p I g n s ξ - oracleBias p I μ g s⟫ := by
  have hc := hr.center_bound p I hσ
  have he : (1 / (n : ℝ)) • ∑ i, guardedOracleError p I g s (ξ i) =
      finiteError p I g n s ξ := by
    unfold finiteError
    rw [RobustGradient.finite_mean_centered
      (X := fun ω => RobustGradient.centeredClip (clipRadius p s.iteration) s.center
        (g (queryPoint p s) ω)) (I.grad (queryPoint p s)) n hn ξ]
    simp only [guardedOracleError, RobustGradient.guardedError_eq hc]
  have hz := RobustGradient.finite_mean_centered (X := guardedOracleError p I g s)
    (oracleBias p I μ g s) n hn ξ
  rw [he] at hz
  unfold finiteSignedError centeredOracleError
  rw [← hz]

lemma oracleBias_bound_positive (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hR : 0 < p.R) (hσ : 0 < p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2)
    (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) :
    ‖oracleBias p I μ g s‖ ≤ p.ε / (1048576 * p.R * confidence p s.iteration) := by
  have hgrad' : gradient I.f (queryPoint p s) = I.grad (queryPoint p s) := (hgrad _).gradient
  have hg : Measurable (g (queryPoint p s)) := ho.measurable.comp measurable_prodMk_left
  have hmean : (∫ ω, g (queryPoint p s) ω ∂μ) = I.grad (queryPoint p s) := by
    rw [ho.unbiased, hgrad']
  have hmi := ho.moment_integrable (queryPoint p s)
  have hmoment := ho.moment (queryPoint p s)
  rw [hgrad'] at hmi hmoment
  have hb : 384 * p.σ ≤ clipRadius p s.iteration := le_max_left _ _
  have hB : 0 < clipRadius p s.iteration := lt_of_lt_of_le (by positivity) hb
  have ht := RobustGradient.guardedError_heavy_moments hg (ho.integrable _) hmean hB
    hα.le hα2 hmi hmoment s.center
  exact ht.2.2.2.trans (RobustGradient.heavy_clip_bias_tuning hσ hα hR hε
    (by linarith [confidence_lower p hδ hδ1 s.iteration]) (le_max_right _ _))

lemma oracleBias_bound (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2)
    (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) :
    ‖oracleBias p I μ g s‖ ≤ p.ε / (1048576 * p.R * confidence p s.iteration) := by
  by_cases hp : 0 < p.σ
  · exact oracleBias_bound_positive p I μ ho hgrad hR hp hα hα2 hε hδ hδ1 s
  · have hz : p.σ = 0 := le_antisymm (not_lt.mp hp) hσ
    have hl := confidence_lower p hδ hδ1 s.iteration
    simp only [oracleBias, guardedOracleError_zero_noise p I g hz hα, integral_zero, norm_zero]
    positivity


lemma weighted_oracleBias_bound (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2)
    (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (xs : p.E) (s : State p.E)
    (ha : 0 ≤ stepWeight p s) (hd : ‖xs - s.z‖ ≤ 4 * p.R) :
    |stepWeight p s * ⟪xs - s.z, oracleBias p I μ g s⟫| ≤
      p.ε * stepWeight p s / (262144 * confidence p 0) := by
  have hb := oracleBias_bound p I μ ho hgrad hR hσ hα hα2 hε hδ hδ1 s
  have hl := confidence_lower p hδ hδ1 s.iteration
  have hl0 := confidence_lower p hδ hδ1 0
  rw [abs_mul, abs_of_nonneg ha]
  calc
    _ ≤ stepWeight p s * (‖xs - s.z‖ * ‖oracleBias p I μ g s‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) ha
    _ ≤ stepWeight p s * (4 * p.R * (p.ε / (1048576 * p.R * confidence p s.iteration))) := by
      gcongr
    _ = p.ε * stepWeight p s / (262144 * confidence p s.iteration) := by field_simp; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
      exact confidence_mono p hδ (Nat.zero_le _)

lemma finite_error_signed_split (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (hσ : 0 ≤ p.σ) (xs : p.E) (s : State p.E)
    (hr : EvaluationReady p I s) (n : ℕ) (hn : 0 < n) (ξ : Fin n → p.Ω) :
    stepWeight p s * ⟪finiteError p I g n s ξ, xs - s.z⟫ =
      finiteSignedError p I μ g xs n s ξ + stepWeight p s * ⟪xs - s.z, oracleBias p I μ g s⟫ := by
  rw [finiteSignedError_eq p I μ g hσ xs s hr n hn ξ,
    inner_sub_right (xs - s.z) (finiteError p I g n s ξ) (oracleBias p I μ g s),
    real_inner_comm (finiteError p I g n s ξ) (xs - s.z)]
  ring


def GoodEvents (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (n : ℕ) (ξ : ℕ → p.Ω) : Prop :=
  StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
    (phaseFailure p I g) n (initialState p) ξ < 1 ∧
  StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
    (phaseEnergy p I g) n (initialState p) ξ < p.R ^ 2 / 10 ∧
  StochasticGeneralized.accumulated (fun w : State p.E × ℝ => phaseCost p w.1)
    (phaseSignedNext p I μ g xs) (phaseSigned p I μ g xs) n (initialState p, 0) ξ < p.R ^ 2 / 10

lemma iid_goodEvents_probability (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hgm : Measurable I.grad)
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0))
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (xs : p.E) (n : ℕ)
    {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (ξ : ℕ → Ξ → p.Ω)
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P) :
    P.real {ω | ¬ GoodEvents p I μ g xs n (fun k => ξ k ω)} ≤ p.δ := by
  let A := {ω | 1 ≤ StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
    (phaseFailure p I g) n (initialState p) (fun k => ξ k ω)}
  let B := {ω | p.R ^ 2 / 10 ≤ StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
    (phaseEnergy p I g) n (initialState p) (fun k => ξ k ω)}
  let C := {ω | p.R ^ 2 / 10 ≤ StochasticGeneralized.accumulated
    (fun w : State p.E × ℝ => phaseCost p w.1) (phaseSignedNext p I μ g xs)
    (phaseSigned p I μ g xs) n (initialState p, 0) (fun k => ξ k ω)}
  have ha : P.real A ≤ 3 * p.δ / (32 * Real.exp 1) :=
    iid_phaseFailure_probability p I μ ho hgrad hgm hprox hL0 hL1 hR hσ hα hα2 hΔ hε hδ hδ1 n P ξ h_samples
  have hb : P.real B ≤ Real.exp (-confidence p 0) :=
    iid_phaseEnergy_probability p I μ ho hgrad hgm hprox hL0 hL1 hR hσ hα hα2 hΔ hε hδ hδ1 n P ξ h_samples
  have hc : P.real C ≤ Real.exp (-confidence p 0) :=
    iid_phaseSigned_probability p I μ ho hgrad hgm hprox hL0 hL1 hR hσ hα hα2 hΔ hε hδ hδ1 xs n P ξ h_samples
  have hsub : {ω | ¬ GoodEvents p I μ g xs n (fun k => ξ k ω)} ⊆ A ∪ (B ∪ C) := by
    intro ω hω
    simp only [GoodEvents, not_and_or, not_lt] at hω
    exact hω
  apply (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    ((add_le_add ha ((measureReal_union_le _ _).trans (add_le_add hb hc))).trans ?_))
  rw [exp_neg_confidence p hδ]
  norm_num only [Nat.cast_zero, zero_add, one_pow, mul_one]
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hsum : 3 * p.δ / (32 * Real.exp 1) +
      (p.δ / (64 * Real.exp 1) + p.δ / (64 * Real.exp 1)) = p.δ / (8 * Real.exp 1) := by ring
  rw [hsum]
  exact div_le_self hδ.le (by linarith)



lemma GoodEvents.energy_prefix_lt (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (n : ℕ) (ξ : ℕ → p.Ω) (hg : GoodEvents p I μ g xs n ξ) {j : ℕ} (hj : j ≤ n) :
    StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (phaseEnergy p I g) j (initialState p) ξ < p.R ^ 2 / 10 :=
  (phaseEnergy_prefix_le p I g hδ hδ1 (initialState p) ξ hj).trans_lt hg.2.1

lemma GoodEvents.signed_prefix_lt (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (n : ℕ) (ξ : ℕ → p.Ω)
    (hg : GoodEvents p I μ g xs n ξ) {j : ℕ} (hj : j ≤ n) :
    (StochasticGeneralized.blockTrace (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (initialState p, 0) ξ j).1.2 < p.R ^ 2 / 10 := by
  by_contra hn
  have ht := signedTrace_crossing_persists p I μ g xs (initialState p) 0 ξ hj (not_lt.mp hn)
  rw [signedTrace_accumulated, zero_add] at ht
  exact (not_le_of_gt hg.2.2) ht

lemma GoodEvents.failure_zero (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (n : ℕ) (ξ : ℕ → p.Ω)
    (hg : GoodEvents p I μ g xs n ξ) {j : ℕ} (hj : j < n) :
    let w := StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ j
    phaseFailure p I g (phaseCost p w.1) w.1 (fun i => w.2 i) = 0 :=
  phaseFailure_zero_of_count_lt p I g (initialState p) ξ n hg.1 j hj

lemma accumulated_biasAllowance_bound (p : Public.{0}) (I : Instance p)
    (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    (p.ε / (262144 * confidence p 0)) *
      StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
        (fun _ s _ => phaseWeight p s) n (initialState p) ξ ≤ p.R ^ 2 / (32768 * confidence p 0) := by
  have hl := confidence_lower p hδ hδ1 0
  have hw := accumulated_phaseWeight_bound p I g hL0 hL1 hR hσ hΔ hε ξ n
  apply (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ p.ε / (262144 * confidence p 0))).trans_eq
  field_simp
  ring

lemma potential_allowance_bound {R ell : ℝ} (hell : 1 ≤ ell) :
    3 * R ^ 2 / 4 + R ^ 2 / 10 + R ^ 2 / 10 + R ^ 2 / (32768 * ell) ≤ R ^ 2 := by
  have ht : R ^ 2 / (32768 * ell) ≤ R ^ 2 / 32768 := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
    linarith
  nlinarith [sq_nonneg R]


end OracleTemplate.StochasticCompositeGeneralized
