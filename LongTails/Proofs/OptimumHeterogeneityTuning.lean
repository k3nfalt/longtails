import LongTails.Proofs.OptimumHeterogeneityDescent
import LongTails.Proofs.WeakInterpolationSchedule

namespace LongTails.Proofs.OptimumHeterogeneityTuning

open LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneitySgd LongTails.Algorithms.OptimumHeterogeneityDesign
open OptimumHeterogeneityPrecision OptimumHeterogeneityAllocation OptimumHeterogeneityDescent

variable {p : Params}

lemma variance_scale (hp : spec.valid p) :
    4096 * p.σ^2 * cost p (weights p) ≤ (batchTime p : ℝ) * ((phase p : ℝ) * p.ε^2) := by
  have he := hp.1.2.2.2.2.2.2
  have hc := cost_nn p
  have hh : 0 < (phase p : ℝ) := by exact_mod_cast phase_pos p
  have ht : (4096 * p.σ^2 * cost p (weights p) / (p.ε^2 * phase p)).toNNReal ≤ batchTime p :=
    le_max_right _ _
  have hh' := NNReal.coe_le_coe.mpr ht
  rw [Real.coe_toNNReal _ (by positivity)] at hh'
  linarith only [(div_le_iff₀ (by positivity)).mp hh']

lemma coarse_variance (hp : spec.valid p) (k : ℕ) : varianceTerm p k ≤ phase p*p.ε^2 := by
  have hη := pow_le_pow_left₀ (step_bounds hp k).1 (step_le_one hp k) 2
  have hv := mul_le_mul_of_nonneg_right hη (mul_nonneg (sq_nonneg p.σ) (cost_nn p))
  unfold varianceTerm
  apply (div_le_iff₀ (time_pos hp)).mpr
  nlinarith only [variance_scale hp,hv,mul_nonneg (sq_nonneg p.σ) (cost_nn p)]

lemma coarse_radius (hp : spec.valid p) {k : ℕ} (hk : k ≤ rounds p) :
    p.R^2+(k : ℝ)*(scale p*p.ε+((phase p : ℝ)+1)*p.ε^2) ≤ scale p^2 := by
  let K : ℝ := rounds p
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hh : (phase p : ℝ)+1 ≤ K := by dsimp [K]; exact_mod_cast (show phase p + 1 ≤ rounds p by unfold rounds; omega)
  have hk' : (k : ℝ) ≤ K := by dsimp [K]; exact_mod_cast hk
  have he := hp.1.2.2.2.2.2.2
  have hR := hp.1.2.2.2.2.1
  have hS := scale_bounds hp
  have hsc : p.R + 2*K*p.ε ≤ scale p := by
    unfold scale
    change _ ≤ p.R+64*K*_
    nlinarith only [mul_nonneg hK (noise_nonneg hp), mul_nonneg hK he.le]
  have h₁ := mul_le_mul_of_nonneg_left hsc hS.1.le
  have h₂ := mul_le_mul_of_nonneg_left hS.2.2 hR
  have h₃ := mul_le_mul_of_nonneg_right hsc (mul_nonneg hK he.le)
  have h₄ := mul_le_mul_of_nonneg_right (mul_le_mul hk' hh (by positivity) hK) (sq_nonneg p.ε)
  have h₅ := mul_le_mul_of_nonneg_right hk' (mul_nonneg hS.1.le he.le)
  nlinarith only [h₁,h₂,h₃,h₄,h₅,mul_nonneg hR (mul_nonneg hK he.le),sq_nonneg (K*p.ε)]

lemma warm_decay (hp : spec.valid p) :
    (1-1/(period p : ℝ))^(phase p)*p.R^2 ≤ p.ε^2/64 := by
  let m : ℝ := period p
  let A := 64*(1+(p.R/p.ε)^2)
  have he := hp.1.2.2.2.2.2.2
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (show 1 ≤ period p by have := period_lower p; omega)
  have hm' : 0 < m := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hr : 0 ≤ 1-1/m := sub_nonneg.mpr ((div_le_one hm').mpr hm)
  have hh : (phase p : ℝ) ≥ m*Real.log A := by
    unfold phase
    push_cast
    change m*(1+_) ≥ _
    have ha := Nat.le_ceil (Real.log A)
    nlinarith only [mul_le_mul_of_nonneg_left ha hm'.le, hm']
  have hρ : 1-1/m ≤ Real.exp (-1/m) := by simpa only [neg_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-1/m)
  have hpow := pow_le_pow_left₀ hr hρ (phase p)
  rw [← Real.exp_nat_mul] at hpow
  have hexp : (phase p : ℝ)*(-1/m) ≤ -Real.log A := by
    rw [←mul_div_assoc, div_le_iff₀ hm']
    linarith
  have h1 := hpow.trans (Real.exp_le_exp.mpr hexp)
  rw [Real.exp_neg,Real.exp_log hA] at h1
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg p.R)
  refine h2.trans ?_
  rw [← div_eq_inv_mul, div_le_iff₀ hA]
  dsimp [A]
  field_simp
  nlinarith [sq_nonneg p.ε]

end LongTails.Proofs.OptimumHeterogeneityTuning
