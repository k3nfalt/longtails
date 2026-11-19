import LongTails.Proofs.WeightedInterpolationPrecision
import LongTails.Proofs.WeakInterpolationSchedule

namespace LongTails.Proofs.WeightedInterpolationTuning

open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open WeakInterpolationDesign WeightedInterpolationAllocation WeightedInterpolationPrecision

variable {p : Params}

lemma variance_scale (hp : spec.valid p) :
    256 * p.σ^2 ≤ information p * (batchTime p : ℝ) * (phase p : ℝ) * p.ε := by
  have hi := information_pos hp
  have he := hp.2.2.2.2.2.2
  have hh : 0 < (phase p : ℝ) := by exact_mod_cast phase_pos p
  have ha : 0 ≤ 256 * p.σ ^ 2 / (information p * p.ε * phase p) := by positivity
  have ht : (256 * p.σ ^ 2 / (information p * p.ε * phase p)).toNNReal ≤ batchTime p := le_max_right _ _
  have ht' := NNReal.coe_le_coe.mpr ht
  rw [Real.coe_toNNReal _ ha] at ht'
  linarith only [(div_le_iff₀ (by positivity)).mp ht']

lemma coarse_variance (hp : spec.valid p) (k : ℕ) :
    4*stepSize p k^2*p.σ^2*information p/(batchTime p : ℝ) ≤ phase p*p.ε := by
  have hη := step_bounds hp k
  have hi := information_pos hp
  have ht : 0 < (batchTime p : ℝ) := by exact_mod_cast (hp.1 0).trans_le (local_time p 0)
  have hηI := mul_le_mul_of_nonneg_left (information_le hp) hη.1
  have hs : stepSize p k*information p ≤ 1 := by linarith
  have hs' := mul_self_le_mul_self (mul_nonneg hη.1 hi.le) hs
  apply (div_le_iff₀ ht).mpr
  apply le_of_mul_le_mul_right (a := information p) _ hi
  nlinarith [variance_scale hp, mul_le_mul_of_nonneg_right hs' (sq_nonneg p.σ), sq_nonneg p.σ]

lemma coarse_radius (hp : spec.valid p) {k : ℕ} (hk : k ≤ rounds p) :
    p.R^2+(k : ℝ)*((phase p : ℝ)+1)*p.ε ≤ scale p^2 := by
  let K : ℝ := rounds p
  have hK : 1 ≤ K := by dsimp [K]; exact_mod_cast (show 1 ≤ rounds p by unfold rounds; omega)
  have hh : (phase p : ℝ)+1 ≤ K := by dsimp [K]; exact_mod_cast (show phase p + 1 ≤ rounds p by unfold rounds; omega)
  have hk' : (k : ℝ) ≤ K := by dsimp [K]; exact_mod_cast hk
  have he := hp.2.2.2.2.2.2
  have hR := hp.2.2.2.2.1
  have hs := Real.sqrt_nonneg p.ε
  have hscale : p.R+K*Real.sqrt p.ε ≤ scale p := by
    unfold scale
    change _ ≤ p.R+K*_
    gcongr
    linarith [noise_nonneg hp]
  have hh' := mul_le_mul hk' hh (by positivity) (by linarith)
  have hh'' := mul_le_mul_of_nonneg_right hh' he.le
  have hh''' := mul_self_le_mul_self (by positivity : 0 ≤ p.R+K*Real.sqrt p.ε) hscale
  nlinarith [mul_nonneg hR (mul_nonneg (by linarith : 0 ≤ K) hs),
    congrArg (fun a => K^2*a) (Real.sq_sqrt he.le)]

lemma warm_decay (hp : spec.valid p) :
    (1-1/(period p : ℝ))^(phase p)*p.R^2 ≤ p.ε/64 := by
  let m : ℝ := period p
  let A := 64*(1+p.R^2/p.ε)
  have he := hp.2.2.2.2.2.2
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (show 1 ≤ period p from period_pos p)
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
  linarith

end LongTails.Proofs.WeightedInterpolationTuning
