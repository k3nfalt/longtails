import LongTails.Proofs.WeightedInterpolationDescent

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.WeightedInterpolationAdaptive

open MeasureTheory Metric
open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open WeakInterpolationDesign WeightedInterpolationAllocation WeightedInterpolationBatch WeightedInterpolationPrecision
open WeakInterpolationGeometry WeightedInterpolationEstimator WeightedInterpolationStep
open WeightedInterpolationSampling WeightedInterpolationDescent

variable {p : Params} {f : Functions p} {g : LocalOracle p} {z : Point p}
    {P : Measure (Samples p)} [IsProbabilityMeasure P] {ν : Fin p.n → ProbabilityMeasure p.Ω}

noncomputable def varianceTerm (p : Params) (k : ℕ) :=
  4*stepSize p k^2*p.σ^2*information p/(batchTime p : ℝ)

noncomputable def perturbation (p : Params) (z x : Point p) :=
  64*tolerance p*scale p*(1+‖x-z‖^2/scale p^2)

lemma finite_comp {α β γ : Type*} (a : α → β) (b : β → γ) (h : (Set.range a).Finite) :
    (Set.range (fun s => b (a s))).Finite :=
  (h.image b).subset (by rintro _ ⟨s,rfl⟩; exact ⟨_,⟨s,rfl⟩,rfl⟩)

lemma estimate_finite (T : DistributedTemplate.Time) (k : ℕ) (g : LocalOracle p) (x : Point p) :
    (Set.range (estimate p T k g x)).Finite :=
  DistributedBatchedSgd.finite_range_estimate (rawConfig p T) (scaled p g k) (fun _ => x) Set.finite_range_const 0

omit [IsProbabilityMeasure P] in
lemma estimate_measurable_of_model (D : Model p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) :
    Measurable (Function.uncurry (estimate p T k g)) :=
  DistributedBatchedSgd.measurable_estimate (rawConfig p T) (scaled p g k)
    (measurable_scaled g (fun i => (D.stochastic i).measurable) k) 0

omit [IsProbabilityMeasure P] in
lemma estimate_measurable (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) :
    Measurable (Function.uncurry (estimate p T k g)) :=
  estimate_measurable_of_model D.model T k

lemma fixed_integrable_of_model (D : Model p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ)
    (x : Point p) (M : Point p → ℝ) (hM : Measurable M) :
    Integrable (fun s => M (x-estimate p T k g x s)) P := by
  have hm : Measurable (estimate p T k g x) := (estimate_measurable_of_model D T k).comp (f := fun s : Samples p => (x,s)) measurable_prodMk_left
  exact DistributedBatchedSgd.integrable_finite_range P _ (hM.comp (measurable_const.sub hm))
    (finite_comp _ (fun y => M (x-y)) (estimate_finite T k g x))

lemma fixed_integrable (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ)
    (x : Point p) (M : Point p → ℝ) (hM : Measurable M) :
    Integrable (fun s => M (x-estimate p T k g x s)) P :=
  fixed_integrable_of_model D.model T k x M hM

lemma fixed_distance_of_model (D : Model p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (x : Point p) :
    ∫ s, infDist (x-estimate p T k g x s) (solutions p f)^2 ∂P ≤
      (1-stepSize p k*information p/2)*infDist x (solutions p f)^2+
      varianceTerm p k+perturbation p z x := by
  obtain ⟨y,hy,hd⟩ := (solutions_closed D.differentiable).exists_infDist_eq_dist ⟨z,D.solution⟩ x
  rw [dist_eq_norm] at hd
  have hmin := infDist_le_dist_of_mem (x := x) D.solution
  rw [dist_eq_norm,hd] at hmin
  have hh := fixed_descent_of_model D T k x y hy hmin
  have hg := D.weightedGrowth x
  have heq : surrogate p f z = surrogate p f y := le_antisymm
    (surrogate_min (weight_nonneg D.valid) D.solution _) (surrogate_min (weight_nonneg D.valid) hy _)
  rw [heq] at hg
  have hs := mul_le_mul_of_nonneg_left hg (step_bounds D.valid k).1
  have hmono := integral_mono (fixed_integrable_of_model D T k x (fun v => infDist v (solutions p f)^2) ((continuous_infDist_pt _).pow 2).measurable)
    (fixed_integrable_of_model D T k x (fun v => ‖v-y‖^2) (by fun_prop))
    (fun s => pow_le_pow_left₀ infDist_nonneg (by simpa [dist_eq_norm] using (infDist_le_dist_of_mem (x := x-estimate p T k g x s) hy)) 2)
  unfold varianceTerm perturbation
  rw [← hd] at hh
  linarith only [hs, hh, hmono]

lemma fixed_distance (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (x : Point p) :
    ∫ s, infDist (x-estimate p T k g x s) (solutions p f)^2 ∂P ≤
      (1-stepSize p k*information p/2)*infDist x (solutions p f)^2+
      varianceTerm p k+perturbation p z x :=
  fixed_distance_of_model D.model T k x

private lemma integrate_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Integrable G μ) (a b c d : ℝ) :
    ∫ s, a*F s+b+c*(1+G s/d) ∂μ = a*(∫ s, F s ∂μ)+b+c*(1+(∫ s, G s ∂μ)/d) := by
  have h₁ : Integrable (fun s => a*F s+b) μ := (hF.const_mul a).add (integrable_const b)
  have h₂ : Integrable (fun s => 1+G s/d) μ := (integrable_const (1:ℝ)).add (hG.div_const d)
  rw [integral_add h₁ (h₂.const_mul c), integral_add (hF.const_mul a) (integrable_const b),
    integral_const_mul, integral_const_mul, integral_add (integrable_const (1:ℝ)) (hG.div_const d),
    integral_div]
  simp

lemma adaptive_of_model (D : Model p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (M : Point p → ℝ)
    (hM : Measurable M) (hn : ∀ x, 0 ≤ M x) (a : ℝ)
    (hb : ∀ x, ∫ s, M (x-estimate p T k g x s) ∂P ≤
      a*M x+varianceTerm p k+perturbation p z x) :
    ∫ s, M (iterate p T g s (k+1)) ∂P ≤
      a*(∫ s, M (iterate p T g s k) ∂P)+varianceTerm p k+
      64*tolerance p*scale p*(1+(∫ s, ‖iterate p T g s k-z‖^2 ∂P)/scale p^2) := by
  let X := fun s => iterate p T g s k
  let fresh := DistributedSampling.tail (rawParams p) (rawConfig p T) k
  have hg := fun i => (D.stochastic i).measurable
  have hx := iterate_measurable T g hg k
  have hf := iterate_finite T g k
  have hm := estimate_measurable_of_model D T k
  have hh := DistributedBatchedSgd.independent_finite_range_bound (p := rawParams p) P X hx hf fresh
    (DistributedSampling.tail_preserving (rawParams p) (rawConfig p T) P ν D.workers D.samples k)
    (iterate_independent T g hg k P ν D.workers D.samples)
    (fun (t : Point p × Samples p) => M (t.1-estimate p T k g t.1 t.2))
    (fun x => a*M x+varianceTerm p k+perturbation p z x)
    (hM.comp (measurable_fst.sub hm)) (by unfold perturbation; fun_prop) (fun _ => hn _)
    (fun x => fixed_integrable_of_model D T k x M hM) hb
  have hi (v : Point p → ℝ) (hv : Measurable v) : Integrable (fun s => v (X s)) P :=
    DistributedBatchedSgd.integrable_finite_range P _ (hv.comp hx) (finite_comp _ _ hf)
  have eqn s : X s-estimate p T k g (X s) (fresh s) = iterate p T g s (k+1) := by
    unfold estimate fresh
    rw [DistributedBatchedSgd.estimate_tail]
    rfl
  have h := hh.2
  simp only [eqn] at h
  refine h.trans_eq ?_
  change (∫ s : Samples p, a*M (X s)+varianceTerm p k+
    64*tolerance p*scale p*(1+‖X s-z‖^2/scale p^2) ∂P) = _
  exact integrate_affine P (fun s => M (X s)) (fun s => ‖X s-z‖^2) (hi M hM)
    (hi (fun x => ‖x-z‖^2) (by fun_prop)) _ _ _ _

lemma adaptive (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (M : Point p → ℝ)
    (hM : Measurable M) (hn : ∀ x, 0 ≤ M x) (a : ℝ)
    (hb : ∀ x, ∫ s, M (x-estimate p T k g x s) ∂P ≤
      a*M x+varianceTerm p k+perturbation p z x) :
    ∫ s, M (iterate p T g s (k+1)) ∂P ≤
      a*(∫ s, M (iterate p T g s k) ∂P)+varianceTerm p k+
      64*tolerance p*scale p*(1+(∫ s, ‖iterate p T g s k-z‖^2 ∂P)/scale p^2) :=
  adaptive_of_model D.model T k M hM hn a hb

end LongTails.Proofs.WeightedInterpolationAdaptive
