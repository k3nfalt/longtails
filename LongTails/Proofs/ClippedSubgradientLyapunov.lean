import LongTails.Proofs.ClippedSubgradientProcess
import LongTails.Proofs.ClippedSubgradientTuning
import LongTails.Proofs.GapStrongGrowthIteration

open MeasureTheory
open scoped RealInnerProductSpace BigOperators
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.WeaklyConvexHeavyTailed

open LongTails.Setups.WeaklyConvexHeavyTailed

section Lyapunov

variable (q : Params) {g : q.E → q.Ω → q.E} {projection : q.E → q.E} {D : Set q.E}

noncomputable def advanceD (hprojD : ∀ y, projection y ∈ D) (s : {x : q.E // x ∈ D}) (ω : q.Ω) :
    {x : q.E // x ∈ D} :=
  ⟨transition q g projection s.val ω, hprojD _⟩

def increment (prox : q.E → q.E) (s : {x : q.E // x ∈ D}) (_ : q.Ω) : ℝ :=
  ‖s.val - prox s.val‖ ^ 2

noncomputable def lyapunov (f : q.E → ℝ) (prox : q.E → q.E) (lower c : ℝ)
    (s : {x : q.E // x ∈ D} × ℝ) : ℝ :=
  envelope f q.ρ prox s.1.val - lower + c * |s.2|

lemma advanceD_measurable (hg : Measurable (Function.uncurry g)) (hp : Measurable projection)
    (hprojD : ∀ y, projection y ∈ D) :
    Measurable (Function.uncurry (advanceD q (g := g) hprojD)) := by
  unfold advanceD Function.uncurry
  refine Measurable.subtype_mk ?_
  exact (transition_measurable q hg hp).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

lemma increment_measurable {prox : q.E → q.E} (hprox : Continuous prox) :
    Measurable (Function.uncurry (increment q (D := D) prox)) := by
  unfold increment Function.uncurry
  exact ((measurable_subtype_coe.comp measurable_fst).sub
    (hprox.measurable.comp (measurable_subtype_coe.comp measurable_fst))).norm.pow_const 2

lemma lyapunov_measurable {f : q.E → ℝ} {prox : q.E → q.E} (henv : Continuous (envelope f q.ρ prox))
    (lower c : ℝ) : Measurable (lyapunov q (D := D) f prox lower c) := by
  unfold lyapunov
  exact ((henv.measurable.comp (measurable_subtype_coe.comp measurable_fst)).sub_const _).add
    ((continuous_abs.measurable.comp measurable_snd).const_mul _)

lemma envelope_transition_integrable {f : q.E → ℝ} {prox : q.E → q.E}
    (henv : Continuous (envelope f q.ρ prox))
    (hg : Measurable (Function.uncurry g)) (hp : Measurable projection)
    (hproj : ∀ y, ∀ u ∈ D, ⟪y - projection y, u - projection y⟫ ≤ 0)
    (hprojD : ∀ y, projection y ∈ D) (hτ : 0 ≤ threshold q) (hγ : 0 ≤ stepSize q)
    (ν : Measure q.Ω) [IsProbabilityMeasure ν] (x : q.E) :
    Integrable (fun ω => envelope f q.ρ prox (transition q g projection x ω)) ν := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (projection x) (stepSize q * threshold q)).exists_bound_of_continuousOn
    henv.continuousOn
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall (fun ω => hC _ ?_))
  · exact (henv.measurable.comp ((transition_measurable q hg hp).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · rw [Metric.mem_closedBall, dist_eq_norm]
    unfold transition
    refine (projection_nonexpansive hproj hprojD _ _).trans ?_
    rw [show x - stepSize q • clip (threshold q) (g x ω) - x = -(stepSize q • clip (threshold q) (g x ω)) by abel,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left (norm_clip_le hτ _) hγ

lemma lyapunov_step (hD : Convex ℝ D) {f : q.E → ℝ} {v : q.E → q.E}
    (hv : WeakSubgradientOn D q.ρ f v) (hG : ∀ x ∈ D, ‖v x‖ ≤ q.G) (hρ : 0 < q.ρ)
    (hG0 : 0 < q.G) (hσ : 0 ≤ q.σ) (hα : 1 < q.α) (hα2 : q.α ≤ 2) (hε : 0 < q.ε)
    {prox : q.E → q.E} (hprox : IsProx f D q.ρ prox)
    (hg : Measurable (Function.uncurry g)) (hp : Measurable projection)
    (hproj : ∀ y, ∀ u ∈ D, ⟪y - projection y, u - projection y⟫ ≤ 0)
    (hprojD : ∀ y, projection y ∈ D)
    {ν : Measure q.Ω} [IsProbabilityMeasure ν]
    (hgi : ∀ x ∈ D, Integrable (g x) ν) (hmean : ∀ x ∈ D, ∫ ω, g x ω ∂ν = v x)
    (hmi : ∀ x ∈ D, Integrable (fun ω => ‖g x ω - v x‖ ^ q.α) ν)
    (hm : ∀ x ∈ D, (∫ ω, ‖g x ω - v x‖ ^ q.α ∂ν) ≤ q.σ ^ q.α)
    {lower : ℝ} (s : {x : q.E // x ∈ D} × ℝ) :
    Integrable (fun a => lyapunov q f prox lower (q.ρ ^ 2 * stepSize q)
      (accumulatingTransition (advanceD q (g := g) hprojD) (increment q prox) s a)) ν ∧
    (∫ a, lyapunov q f prox lower (q.ρ ^ 2 * stepSize q)
      (accumulatingTransition (advanceD q (g := g) hprojD) (increment q prox) s a) ∂ν) ≤
      1 * lyapunov q f prox lower (q.ρ ^ 2 * stepSize q) s +
        (stepSize q * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 +
          2 * q.ρ * stepSize q ^ 2 * noiseScale q) := by
  have hN : noiseScale q = q.G ^ 2 + (2 * threshold q) ^ (2 - q.α) * q.σ ^ q.α := by
    unfold noiseScale; ring
  rw [hN]
  have henv : Continuous (envelope f q.ρ prox) := continuous_envelope hD hv hG hρ hG0.le hprox
  have hτpos : 0 < threshold q := threshold_pos q hG0 hσ hε
  have hγ : 0 ≤ stepSize q := (stepSize_pos q hρ hG0 hσ hε).le
  have hτG : 2 * q.G ≤ threshold q := two_G_le_threshold q hσ hε
  obtain ⟨⟨x, hx⟩, acc⟩ := s
  have hint := envelope_transition_integrable q henv hg hp hproj hprojD hτpos.le hγ ν x
  have hstep := one_step_expectation hD hv hG hρ hα.le hα2 hτG hτpos hγ hprox hproj hg hx
    (hgi x hx) (hmean x hx) (hmi x hx) (hm x hx) hint
  simp only [accumulatingTransition, advanceD, increment, lyapunov]
  refine ⟨?_, ?_⟩
  · have hA : Integrable (fun a => envelope f q.ρ prox (transition q g projection x a) - lower) ν :=
      hint.sub (integrable_const lower)
    exact hA.add (integrable_const _)
  · have hA : Integrable (fun a => envelope f q.ρ prox (transition q g projection x a) - lower) ν :=
      hint.sub (integrable_const lower)
    rw [integral_add hA (integrable_const _), integral_sub hint (integrable_const lower),
      integral_const, integral_const]
    simp only [probReal_univ, smul_eq_mul]
    have h2 : ‖prox x - x‖ ^ 2 = ‖x - prox x‖ ^ 2 := by rw [norm_sub_rev]
    have hstep' : (∫ a, envelope f q.ρ prox (transition q g projection x a) ∂ν) ≤
        envelope f q.ρ prox x - q.ρ ^ 2 * stepSize q * ‖x - prox x‖ ^ 2 +
          stepSize q * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 +
          2 * q.ρ * stepSize q ^ 2 * (q.G ^ 2 + (2 * threshold q) ^ (2 - q.α) * q.σ ^ q.α) := by
      rw [← h2]; exact hstep
    have habs : |acc + ‖x - prox x‖ ^ 2| ≤ |acc| + ‖x - prox x‖ ^ 2 := by
      calc |acc + ‖x - prox x‖ ^ 2| ≤ |acc| + |‖x - prox x‖ ^ 2| := abs_add_le _ _
        _ = |acc| + ‖x - prox x‖ ^ 2 := by rw [abs_of_nonneg (sq_nonneg ‖x - prox x‖)]
    have hc : 0 ≤ q.ρ ^ 2 * stepSize q := mul_nonneg (sq_nonneg _) hγ
    nlinarith [hstep', mul_le_mul_of_nonneg_left habs hc]

lemma lyapunov_nonneg (hρ : 0 ≤ q.ρ) {f : q.E → ℝ} {prox : q.E → q.E} (hprox : IsProx f D q.ρ prox)
    {lower c : ℝ} (hc : 0 ≤ c) (hlow : ∀ y ∈ D, lower ≤ f y) (s : {x : q.E // x ∈ D} × ℝ) :
    0 ≤ lyapunov q f prox lower c s := by
  unfold lyapunov
  have := envelope_ge hρ hprox hlow s.1.val
  nlinarith [mul_nonneg hc (abs_nonneg s.2)]

end Lyapunov

end OracleTemplate.WeaklyConvexHeavyTailed
