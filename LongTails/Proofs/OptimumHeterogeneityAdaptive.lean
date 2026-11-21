import LongTails.Proofs.OptimumHeterogeneityDescent

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.OptimumHeterogeneityAdaptive

open MeasureTheory Metric
open LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneitySgd LongTails.Algorithms.OptimumHeterogeneityDesign
open OptimumHeterogeneityAllocation OptimumHeterogeneityPrecision OptimumHeterogeneityGrowth
open OptimumHeterogeneityDrift OptimumHeterogeneityMoments OptimumHeterogeneityStep
open OptimumHeterogeneitySampling OptimumHeterogeneityDescent

variable {p : Params} {f : Functions p} {g : LocalOracle p} {z : Point p}
    {P : Measure (Samples p)} [IsProbabilityMeasure P] {ν : Fin p.n → ProbabilityMeasure p.Ω}

lemma finite_comp {α β γ : Type*} (a : α → β) (b : β → γ) (h : (Set.range a).Finite) :
    (Set.range (fun s => b (a s))).Finite :=
  (h.image b).subset (by rintro _ ⟨s,rfl⟩; exact ⟨_,⟨s,rfl⟩,rfl⟩)

lemma estimate_finite (T : DistributedTemplate.Time) (k : ℕ) (g : LocalOracle p) (x : Point p) :
    (Set.range (estimate p T k g x)).Finite :=
  DistributedBatchedSgd.finite_range_estimate (config p T) (scaled p g k) (fun _ => x) Set.finite_range_const 0

omit [IsProbabilityMeasure P] in
lemma estimate_measurable (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) :
    Measurable (Function.uncurry (estimate p T k g)) :=
  DistributedBatchedSgd.measurable_estimate (config p T) (scaled p g k)
    (measurable_scaled g (fun i => (D.stochastic i).measurable) k) 0

lemma fixed_integrable (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ)
    (x : Point p) (M : Point p → ℝ) (hM : Measurable M) :
    Integrable (fun s => M (x-estimate p T k g x s)) P := by
  have hm : Measurable (estimate p T k g x) := (estimate_measurable D T k).comp (f := fun s : Samples p => (x,s)) measurable_prodMk_left
  exact DistributedBatchedSgd.integrable_finite_range P _ (hM.comp (measurable_const.sub hm))
    (finite_comp _ (fun y => M (x-y)) (estimate_finite T k g x))

private lemma integrate_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Integrable G μ) (a b c d : ℝ) :
    ∫ s, a*F s+b+c*(1+G s/d) ∂μ = a*(∫ s, F s ∂μ)+b+c*(1+(∫ s, G s ∂μ)/d) := by
  have h₁ : Integrable (fun s => a*F s+b) μ := (hF.const_mul a).add (integrable_const b)
  have h₂ : Integrable (fun s => 1+G s/d) μ := (integrable_const (1:ℝ)).add (hG.div_const d)
  rw [integral_add h₁ (h₂.const_mul c), integral_add (hF.const_mul a) (integrable_const b),
    integral_const_mul, integral_const_mul, integral_add (integrable_const (1:ℝ)) (hG.div_const d),
    integral_div]
  simp

lemma adaptive (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (M : Point p → ℝ)
    (hM : Measurable M) (hn : ∀ x, 0 ≤ M x) (a b c : ℝ)
    (hb : ∀ x, ∫ s, M (x-estimate p T k g x s) ∂P ≤
      a*M x+b+c*(1+‖x-z‖^2/scale p^2)) :
    ∫ s, M (iterate p T g s (k+1)) ∂P ≤
      a*(∫ s, M (iterate p T g s k) ∂P)+b+
      c*(1+(∫ s, ‖iterate p T g s k-z‖^2 ∂P)/scale p^2) := by
  let X := fun s => iterate p T g s k
  let fresh := DistributedSampling.tail (transport p) (config p T) k
  have hg := fun i => (D.stochastic i).measurable
  have hx := iterate_measurable T g hg k
  have hf := iterate_finite T g k
  have hm := estimate_measurable D T k
  have hh := DistributedBatchedSgd.independent_finite_range_bound (p := transport p) P X hx hf fresh
    (DistributedSampling.tail_preserving (transport p) (config p T) P ν D.workers D.samples k)
    (iterate_independent T g hg k P ν D.workers D.samples)
    (fun (t : Point p × Samples p) => M (t.1-estimate p T k g t.1 t.2))
    (fun (x : Point p) => a*M x+b+c*(1+‖x-z‖^2/scale p^2))
    (hM.comp (measurable_fst.sub hm)) (by fun_prop) (fun _ => hn _)
    (fun x => fixed_integrable D T k x M hM) hb
  have hi (v : Point p → ℝ) (hv : Measurable v) : Integrable (fun s => v (X s)) P :=
    DistributedBatchedSgd.integrable_finite_range P _ (hv.comp hx) (finite_comp _ _ hf)
  have eqn s : X s-estimate p T k g (X s) (fresh s) = iterate p T g s (k+1) := by
    unfold estimate fresh
    rw [DistributedBatchedSgd.estimate_tail]
    rfl
  have h := hh.2
  simp only [eqn] at h
  refine h.trans_eq ?_
  change (∫ s : Samples p, a*M (X s)+b+
    c*(1+‖X s-z‖^2/scale p^2) ∂P) = _
  exact integrate_affine P (fun s => M (X s)) (fun s => ‖X s-z‖^2) (hi M hM)
    (hi (fun x => ‖x-z‖^2) (by fun_prop)) _ _ _ _

end LongTails.Proofs.OptimumHeterogeneityAdaptive
