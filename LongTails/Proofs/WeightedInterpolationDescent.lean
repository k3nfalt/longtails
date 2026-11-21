import LongTails.Proofs.WeightedInterpolationStep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.WeightedInterpolationDescent

open MeasureTheory
open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open WeakInterpolationDesign WeightedInterpolationAllocation WeightedInterpolationBatch WeightedInterpolationPrecision
open WeakInterpolationGeometry WeightedInterpolationEstimator WeightedInterpolationStep

variable {p : Params} {f : Functions p} {g : LocalOracle p} {z : Point p}
    {P : Measure (Samples p)} [IsProbabilityMeasure P] {ν : Fin p.n → ProbabilityMeasure p.Ω}

lemma rounding_cost {e B d δ : ℝ} (he : 0 < e) (hB : 0 < B) (heb : e ≤ B)
    (hd : 0 ≤ d) (hδ : 0 ≤ δ) (hb : δ ≤ e*(1+d/B)) :
    2*d*(e+3*δ) + 12*δ^2 + 2*(e+δ)^2 ≤ 64*e*B*(1+d^2/B^2) := by
  let s := d/B
  have hs : 0 ≤ s := div_nonneg hd hB.le
  have hid : d = B*s := by dsimp [s]; field_simp
  have h1 := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 6*d)
  have h2 := mul_self_le_mul_self hδ hb
  have h3 := mul_self_le_mul_self (add_nonneg he.le hδ) (add_le_add le_rfl hb)
  change δ ≤ e*(1+s) at hb
  change 6*d*δ ≤ 6*d*(e*(1+s)) at h1
  change δ*δ ≤ e*(1+s)*(e*(1+s)) at h2
  change (e+δ)*(e+δ) ≤ (e+e*(1+s))*(e+e*(1+s)) at h3
  rw [← div_pow]
  change _ ≤ 64*e*B*(1+s^2)
  calc
    _ ≤ 2*d*(e+3*(e*(1+s))) + 12*(e*(1+s))^2 + 2*(e+e*(1+s))^2 := by linarith only [h1,h2,h3]
    _ = e*B*(8*s+6*s^2) + e*e*(20+32*s+14*s^2) := by rw [hid]; ring
    _ ≤ e*B*(8*s+6*s^2) + e*B*(20+32*s+14*s^2) := by gcongr
    _ ≤ _ := by
      have hh : (8*s+6*s^2)+(20+32*s+14*s^2) ≤ 64*(1+s^2) := by nlinarith [sq_nonneg (s-1)]
      linarith only [mul_le_mul_of_nonneg_left hh (mul_nonneg he.le hB.le)]

lemma fixed_descent_certified (D : Certificate p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (x y : Point p)
    (hy : y ∈ solutions p f) (hd : ‖x-y‖ ≤ ‖x-z‖) :
    ∫ s, ‖x-estimate p T k g x s-y‖^2 ∂P ≤ ‖x-y‖^2 -
      stepSize p k*(surrogate p f x-surrogate p f y) +
      4*stepSize p k^2*p.σ^2*information p/(batchTime p : ℝ) +
      64*tolerance p*scale p*(1+‖x-z‖^2/scale p^2) := by
  let u := stepSize p k • direction p f x
  let v := x-u-y
  have hstep := step_bounds D.valid k
  have hdet := deterministic_step (smoothness_pos D.valid) hstep.1 hstep.2
    (surrogate_support (weight_nonneg D.valid) D.convex D.differentiable x y)
    (D.gradient_sq y hy x)
  change ‖v‖^2 ≤ _ at hdet
  have hmin := surrogate_min (weight_nonneg D.valid) hy x
  have hv : ‖v‖ ≤ ‖x-z‖ := by
    apply le_trans _ hd
    nlinarith [mul_nonneg hstep.1 (sub_nonneg.mpr hmin), norm_nonneg (x-y)]
  have he := tolerance_pos D.valid
  have hB := scale_bounds D.valid
  have hK : 1 ≤ (rounds p : ℝ) := by exact_mod_cast (show 1 ≤ rounds p by unfold rounds; omega)
  have hscale := hB.1
  have hKpos : 0 < (rounds p : ℝ) := by linarith
  have heb : tolerance p ≤ scale p := by
    unfold tolerance
    apply (div_le_iff₀ (by positivity)).mpr
    have heps := Real.sq_sqrt D.valid.2.2.2.2.2.2.le
    have hs := mul_self_le_mul_self (Real.sqrt_nonneg p.ε) hB.2.1
    nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg (scale p))]
  have hδ : 0 ≤ errorRadius p T x := Real.sqrt_nonneg _
  have hr := rounding_cost he hB.1 heb (norm_nonneg (x-z)) hδ (grid_error D.valid T x z D.initial)
  have hv' := mul_le_mul_of_nonneg_right hv (show 0 ≤ 2*(tolerance p+3*errorRadius p T x) by positivity)
  have hh := fixed_noise_certified D T k x v
  dsimp only at hh
  have heq s : x-estimate p T k g x s-y = v-(estimate p T k g x s-u) := by dsimp [v]; abel
  simp_rw [heq]
  linarith only [hh,hdet,hr,hv']

lemma fixed_descent (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (x y : Point p)
    (hy : y ∈ solutions p f) (hd : ‖x-y‖ ≤ ‖x-z‖) :
    ∫ s, ‖x-estimate p T k g x s-y‖^2 ∂P ≤ ‖x-y‖^2 -
      stepSize p k*(surrogate p f x-surrogate p f y) +
      4*stepSize p k^2*p.σ^2*information p/(batchTime p : ℝ) +
      64*tolerance p*scale p*(1+‖x-z‖^2/scale p^2) :=
  fixed_descent_certified D.certificate T k x y hy hd

end LongTails.Proofs.WeightedInterpolationDescent
