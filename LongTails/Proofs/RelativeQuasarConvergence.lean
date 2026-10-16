import LongTails.Proofs.RelativeQuasarStep
import LongTails.Proofs.RelativeQuasarTuning
import LongTails.Proofs.RelativeQuasarIteration
import LongTails.Proofs.CachedQuasarRate
import LongTails.Proofs.QueryPlan

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RelativeQuasar

open LongTails.Setups.RelativeGradientStrongQuasar ContinuizedSimilarQuasar

lemma run_accuracy (p : Params) (f : p.E → ℝ) (g : p.E → p.E)
    (hp : spec.valid p) (hm : Measurable g)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (he : ∀ x, ‖g x - gradient f x‖ ≤ p.δ * ‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (hgap : f p.x0 - f u ≤ p.Δ)
    (hquasar : ∀ x, p.γ * f x + ⟪gradient f x, u - x⟫ +
      p.γ * p.μ / 2 * ‖u - x‖ ^ 2 ≤ p.γ * f u) :
    Integrable (fun seed => f (run p g (calls p) (p.x0, p.x0) seed).1 - f u)
      (samplesLaw (calls p) : Measure _) ∧
    (∫ seed, f (run p g (calls p) (p.x0, p.x0) seed).1 - f u
      ∂(samplesLaw (calls p) : Measure _)) ≤ p.ε := by
  obtain ⟨hL, hμ, hγ, hγ1, hδ, hδ1, hΔ, hε⟩ := hp
  obtain ⟨ht, hs, hn⟩ := theta_bounds p hL hμ hγ hδ1
  have hcoef := generator_coefficient hL hμ hγ hδ hδ1 hs hn
  have hstep : 16 * p.L * theta p ^ 2 ≤ p.μ := by
    have hh := mul_nonneg hμ.le hδ
    nlinarith [sq_nonneg (theta p)]
  let V := SimilarQuasar.energy f (p.μ / 2) u
  let q := 4 / (4 + p.γ * theta p)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hg x).hasFDerivAt.continuousAt)
  have hV : Continuous V := energy_continuous hf (p.μ / 2) u
  have hmin' : ∀ x, f u ≤ f x := fun x => hmin (Set.mem_univ x)
  have hV0 (s : p.E × p.E) : 0 ≤ V s := SimilarQuasar.energy_nonneg (by positivity) hmin' s
  have ha := advance_measurable p.L p.μ p.γ (theta p) hm
  have hsingle (s : p.E × p.E) :
      Integrable (fun t => V (advance p.L p.μ p.γ (theta p) g s t)) (holdingLaw : Measure ℝ) ∧
      (∫ t, V (advance p.L p.μ p.γ (theta p) g s t) ∂(holdingLaw : Measure ℝ)) ≤ q * V s + 0 := by
    simpa only [add_zero] using RelativeQuasar.sample_energy_step hL hμ hγ ht.le hδ hδ1.le
      hm hstep hcoef hg hlip he u hmin' hquasar s
  have hr := measurable_iterateSamples_integral ha holdingLaw V hV.measurable hV0 hq
    hsingle (calls p) (p.x0, p.x0)
  have hb := block_contraction (mul_pos hγ ht) (blockLength p)
    (blockLength_bound p hL hμ hγ hδ1)
  have hpw : q ^ calls p ≤ (1 / 2 : ℝ) ^ blocks p := by
    rw [calls, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hq _) hb _
  have hqg := SimilarQuasar.strong_quasar_quadratic_growth hg hγ1 hmin' hquasar
  have hi := SimilarQuasar.initial_energy hμ hγ hγ1 p.x0 u hgap (hqg p.x0)
  have hi' : V (p.x0, p.x0) ≤ 2 * p.Δ / p.γ := by
    dsimp [V, SimilarQuasar.energy] at *
    nlinarith [mul_nonneg hμ.le (sq_nonneg ‖p.x0 - u‖)]
  have hacc : (∫ seed, V (run p g (calls p) (p.x0, p.x0) seed)
      ∂(samplesLaw (calls p) : Measure _)) ≤ p.ε := by
    have hh := mul_le_mul_of_nonneg_right hpw (hV0 (p.x0, p.x0))
    have hh' := mul_le_mul_of_nonneg_left hi' (by positivity : 0 ≤ (1 / 2 : ℝ) ^ blocks p)
    have heps := mul_le_mul_of_nonneg_left (blocks_accuracy p hγ hε)
      (by positivity : 0 ≤ (1 / 2 : ℝ) ^ blocks p)
    have hid : (1 / 2 : ℝ) ^ blocks p * 2 ^ blocks p = 1 := by
      rw [← mul_pow]; norm_num
    rw [← mul_assoc, hid, one_mul] at heps
    exact hr.2.trans (by simpa only [zero_mul, add_zero] using hh.trans (hh'.trans heps))
  let R := fun seed => run p g (calls p) (p.x0, p.x0) seed
  have hR : Measurable R := (iterateSamples_measurable ha (calls p)).comp
    (measurable_const.prodMk measurable_id)
  have hdom (seed) : f (R seed).1 - f u ≤ V (R seed) :=
    le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg ‖(R seed).2 - u‖))
  have hFi : Integrable (fun seed => f (R seed).1 - f u)
      (samplesLaw (calls p) : Measure _) := by
    apply hr.1.mono' ((hf.measurable.comp hR.fst).sub measurable_const).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro seed
    change ‖f (R seed).1 - f u‖ ≤ V (R seed)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmin' _))]
    exact hdom seed
  exact ⟨hFi, (integral_mono_ae hFi hr.1 (Filter.Eventually.of_forall hdom)).trans hacc⟩

lemma eval_plan (p : Params) (g : p.E → p.E) (k : ℕ) (s : p.E × p.E)
    (samples : Fin k → ℝ) : QueryPlan.eval g (plan p k s samples) = run p g k s samples := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [plan, QueryPlan.eval, ih]
      rfl

lemma execute_accelerated (p : Params) (g : p.E → p.E) (seed : (accelerated p).Seed) :
    execute {answer := fun _ (_, x) _ => g x} (accelerated p) (fun _ => calls p) seed =
      (run p g (calls p) (p.x0, p.x0) seed).1 := by
  change execute {answer := fun _ (_, x) _ => g x} (QueryPlan.algorithm _ _ _ _ _) (fun _ => _) _ = _
  erw [QueryPlan.execute_plan, QueryPlan.eval_map, eval_plan]

end OracleTemplate.RelativeQuasar
