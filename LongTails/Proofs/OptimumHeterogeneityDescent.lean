import LongTails.Proofs.OptimumHeterogeneityStep
import LongTails.Proofs.WeightedInterpolationDescent

namespace LongTails.Proofs.OptimumHeterogeneityDescent

open MeasureTheory Metric
open LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneitySgd LongTails.Algorithms.OptimumHeterogeneityDesign
open OptimumHeterogeneityAllocation OptimumHeterogeneityGrowth OptimumHeterogeneityPrecision
open OptimumHeterogeneityMoments OptimumHeterogeneityDrift OptimumHeterogeneityStep

variable {p : Params} {f : Functions p} {g : LocalOracle p} {z : Point p}
    {P : Measure (Samples p)} [IsProbabilityMeasure P] {ν : Fin p.n → ProbabilityMeasure p.Ω}

noncomputable def varianceTerm (p : Params) (k : ℕ) :=
  4 * stepSize p k ^ 2 * p.σ ^ 2 * cost p (weights p) / (batchTime p : ℝ)

lemma step_le_one (hp : spec.valid p) (k : ℕ) : stepSize p k ≤ 1 := by
  have h : 8 ≤ (period p : ℝ) := by exact_mod_cast period_lower p
  exact (step_bounds hp k).2.1.trans ((div_le_iff₀ (by linarith)).mpr (by linarith))

lemma rounding {e B d δ : ℝ} (he : 0 < e) (hB : 0 < B) (heb : e ≤ B)
    (hd : 0 ≤ d) (hδ : 0 ≤ δ) (hh : δ ≤ e*(1+d/B)) :
    2*(d+B)*(e+3*δ)+12*δ^2+2*(e+δ)^2 ≤ 192*e*B*(1+d^2/B^2) := by
  have hh' : δ ≤ e*(1+(d+B)/B) := by
    apply hh.trans
    gcongr
    linarith
  have hr := WeightedInterpolationDescent.rounding_cost he hB heb (add_nonneg hd hB.le) hδ hh'
  apply hr.trans
  rw [← div_pow, ← div_pow, add_div, div_self hB.ne']
  have h : 1+(d/B+1)^2 ≤ 3*(1+(d/B)^2) := by nlinarith [sq_nonneg (d/B-1)]
  linarith only [mul_le_mul_of_nonneg_left h (show 0 ≤ 64*e*B by positivity)]

lemma fixed_descent (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (x y : Point p)
    (hy : y ∈ solutions p f) (hd : ‖x-y‖ ≤ ‖x-z‖) :
    ∫ s, ‖x-estimate p T k g x s-y‖^2 ∂P ≤ ‖x-y‖^2 -
      stepSize p k * gap p f y x + 2 * stepSize p k * (p.ε/64) * ‖x-y‖ +
      (stepSize p k * (p.ε/64))^2 + varianceTerm p k +
      192*tolerance p*scale p*(1+‖x-z‖^2/scale p^2) := by
  let η := stepSize p k
  let u := η • direction p f x
  let v := x-u-y
  let v₀ := x-η • (direction p f x-direction p f y)-y
  have hη := (step_bounds D.valid k).1
  have heps := D.valid.1.2.2.2.2.2.2
  have hdet : ‖v₀‖^2 ≤ ‖x-y‖^2-η*gap p f y x := corrected_step D.toGeometry k y x
  have hgap : 0 ≤ gap p f y x := Finset.sum_nonneg fun i _ => mul_nonneg (weight_nn D.valid i)
    (OptimumHeterogeneityGeometry.remainder_bounds (D.convex i) (D.grad i) (D.lip i) y x).1
  have hshort : ‖v₀‖ ≤ ‖x-y‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    linarith [mul_nonneg hη hgap]
  have hb : ‖direction p f y‖ ≤ p.ε/64 := small_bias D.toGeometry hy
  have hdiff : v = v₀ - η • direction p f y := by dsimp [v,v₀,u]; rw [smul_sub]; abel
  have hv : ‖v‖ ≤ ‖v₀‖ + η*(p.ε/64) := by
    rw [hdiff]
    have h₁ := norm_sub_le v₀ (η • direction p f y)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at h₁
    exact h₁.trans (add_le_add_right (mul_le_mul_of_nonneg_left hb hη) _)
  have hηb : 0 ≤ η*(p.ε/64) := mul_nonneg hη (by positivity)
  have hvsq := pow_le_pow_left₀ (norm_nonneg _) hv 2
  have hvdet : ‖v‖^2 ≤ ‖x-y‖^2-η*gap p f y x+2*η*(p.ε/64)*‖x-y‖+(η*(p.ε/64))^2 := by
    nlinarith only [hvsq,hdet,mul_le_mul_of_nonneg_right hshort hηb]
  have hB := scale_bounds D.valid
  have hK : 1 ≤ (rounds p : ℝ) := by exact_mod_cast (show 1 ≤ rounds p by unfold rounds; omega)
  have hscale := hB.1
  have hKpos : 0 < (rounds p : ℝ) := by linarith
  have heb : tolerance p ≤ scale p := by
    unfold tolerance
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [mul_self_le_mul_self heps.le hB.2.1,
      mul_le_mul_of_nonneg_right hK (sq_nonneg (scale p)), sq_nonneg (scale p)]
  have hδ : 0 ≤ errorRadius p T x := Real.sqrt_nonneg _
  have hr := rounding (tolerance_pos D.valid) hB.1 heb (norm_nonneg (x-z)) hδ (grid_error D.valid T x z D.initial)
  have hv' : ‖v‖ ≤ ‖x-z‖+scale p := by
    linarith [mul_le_mul_of_nonneg_right (step_le_one D.valid k) (show 0 ≤ p.ε/64 by positivity)]
  have he := tolerance_pos D.valid
  have hr' := mul_le_mul_of_nonneg_right hv' (show 0 ≤ 2*(tolerance p+3*errorRadius p T x) by positivity)
  have hh := fixed_noise D T k x v
  dsimp only at hh
  have heq s : x-estimate p T k g x s-y = v-(estimate p T k g x s-u) := by dsimp [v]; abel
  simp_rw [heq]
  unfold varianceTerm
  change _ ≤ ‖v‖^2 + _ + _ + _ + _ at hh
  linarith only [hh,hvdet,hr,hr']

end LongTails.Proofs.OptimumHeterogeneityDescent
