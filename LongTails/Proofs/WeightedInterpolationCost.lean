import LongTails.Proofs.WeightedInterpolationPrecision

namespace LongTails.Proofs.WeightedInterpolationCost

open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open WeakInterpolationDesign WeightedInterpolationAllocation WeightedInterpolationPrecision

variable {p : Params}

noncomputable def condition (p : Params) : ℝ := smoothness p / information p
noncomputable def burn (p : Params) : ℝ := 1 + Real.log (1+p.R^2/p.ε)
noncomputable def magnitude (p : Params) : ℝ := 2 + p.d + condition p + (p.R^2+noiseRadius p^2)/p.ε

lemma condition_one (hp : spec.valid p) : 1 ≤ condition p := (one_le_div (information_pos hp)).mpr (information_le hp)
lemma burn_one (hp : spec.valid p) : 1 ≤ burn p := by
  unfold burn
  have hr := div_nonneg (sq_nonneg p.R) hp.2.2.2.2.2.2.le
  linarith [Real.log_nonneg (by linarith : 1 ≤ 1+p.R^2/p.ε)]

lemma rounds_bound (hp : spec.valid p) : (rounds p : ℝ) ≤ 1024*condition p*burn p := by
  have hκ := condition_one hp
  have hB := burn_one hp
  have he := hp.2.2.2.2.2.2
  have hratio : 4*smoothness p/information p = 4*condition p := by unfold condition; ring
  have hm : (period p : ℝ) ≤ 5*condition p := by
    rw [period, Nat.cast_max, hratio, max_le_iff]
    constructor
    · norm_num; linarith
    · linarith [Nat.ceil_lt_add_one (show 0 ≤ 4*condition p by linarith)]
  have hz : 0 < 1+p.R^2/p.ε := by positivity
  have hlog := Real.log_nonneg (show 1 ≤ 64*(1+p.R^2/p.ε) by linarith [div_nonneg (sq_nonneg p.R) he.le])
  have hl : 1+(⌈Real.log (64*(1+p.R^2/p.ε))⌉₊ : ℝ) ≤ 66*burn p := by
    have hh := Nat.ceil_lt_add_one hlog
    rw [Real.log_mul (by norm_num) hz.ne'] at hh ⊢
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<64)
    unfold burn at *
    linarith
  have ha := mul_le_mul hm hl (by positivity) (by linarith)
  have hb := one_le_mul_of_one_le_of_one_le hκ hB
  unfold rounds phase
  push_cast
  linarith only [ha,hb]

lemma width_bound (hp : spec.valid p) : (width p : ℕ) ≤ 1024 * Nat.size ⌈magnitude p⌉₊ := by
  let Y := magnitude p
  let a := Real.sqrt p.ε
  let r := p.R/a
  let z := noiseRadius p/a
  let K : ℝ := rounds p
  let v := scale p/a
  have he := hp.2.2.2.2.2.2
  have ha : 0 < a := Real.sqrt_pos.mpr he
  have ha2 : a^2 = p.ε := Real.sq_sqrt he.le
  have hR := hp.2.2.2.2.1
  have hΓ := noise_nonneg hp
  have hr : 0 ≤ r := div_nonneg hR ha.le
  have hz : 0 ≤ z := div_nonneg hΓ ha.le
  have hy : Y = 2+p.d+condition p+r^2+z^2 := by
    dsimp [Y,magnitude,r,z]
    rw [div_pow,div_pow,ha2,add_div]
    ring
  have hκ := condition_one hp
  have hY : 2 ≤ Y := by nlinarith [(Nat.cast_nonneg p.d : 0 ≤ (p.d : ℝ)), sq_nonneg r, sq_nonneg z]
  have hY0 : 0 ≤ Y := by linarith
  have hrY : r ≤ Y := by nlinarith [sq_nonneg (r-1),sq_nonneg z,(Nat.cast_nonneg p.d : 0 ≤ (p.d : ℝ))]
  have hzY : z ≤ Y := by nlinarith [sq_nonneg (z-1),sq_nonneg r,(Nat.cast_nonneg p.d : 0 ≤ (p.d : ℝ))]
  have hdY : 1+Real.sqrt p.d ≤ 2*Y := by
    nlinarith [Real.sq_sqrt ((Nat.cast_nonneg p.d : 0 ≤ (p.d : ℝ))),sq_nonneg (Real.sqrt p.d-1),sq_nonneg r,sq_nonneg z]
  have hkY : condition p ≤ Y := by nlinarith [sq_nonneg r,sq_nonneg z,(Nat.cast_nonneg p.d : 0 ≤ (p.d : ℝ))]
  have hbY : burn p ≤ Y := by
    have hr2 : p.R^2/p.ε = r^2 := by dsimp [r]; rw [div_pow,ha2]
    unfold burn
    rw [hr2]
    nlinarith [Real.log_le_sub_one_of_pos (by positivity : 0<1+r^2),sq_nonneg z,(Nat.cast_nonneg p.d : 0 ≤ (p.d : ℝ))]
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hK : K ≤ 1024*Y^2 := by
    exact (rounds_bound hp).trans (by rw [mul_assoc, sq]; exact mul_le_mul_of_nonneg_left (mul_le_mul hkY hbY (by linarith [burn_one hp]) hY0) (by norm_num))
  have hv : v = r+K*(8*z+8) := by
    dsimp [v,r,z,K,scale,a]
    field_simp [(Real.sqrt_pos.mpr he).ne']
  have hY2 : 1 ≤ Y^2 := by nlinarith [sq_nonneg (Y-1)]
  have hvY : v ≤ 32768*Y^3 := by
    rw [hv]
    calc
      _ ≤ Y+(1024*Y^2)*(16*Y) := by gcongr; linarith
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hY2 hY0, pow_nonneg hY0 3]
  have hv0 : 0 ≤ v := (div_pos (scale_bounds hp).1 ha).le
  let W := 64*(1+Real.sqrt p.d)*4096*K*v*(r+1+4096*K*v*z^2+v)
  have hW : 64*(1+Real.sqrt p.d)*(guardRadius p+scale p)/tolerance p = W := by
    dsimp [W,K,v,z,r,tolerance,guardRadius]
    have hKpos : 0 < (rounds p : ℝ) := by exact_mod_cast (show 0 < rounds p by unfold rounds; omega)
    have hscale := (scale_bounds hp).1
    change 64*(1+Real.sqrt p.d)*(p.R+a+noiseRadius p^2/(p.ε/(4096*(rounds p : ℝ)*scale p))+scale p)/
      (p.ε/(4096*(rounds p : ℝ)*scale p)) = _
    rw [←ha2]
    field_simp
  have hz2Y : z^2 ≤ Y^2 := pow_le_pow_left₀ hz hzY 2
  have hWp : W ≤ 2^110 * Y^13 := by
    dsimp [W]
    calc
      _ ≤ 64*(2*Y)*4096*(1024*Y^2)*(32768*Y^3)*
          (Y+1+4096*(1024*Y^2)*(32768*Y^3)*Y^2+32768*Y^3) := by gcongr
      _ ≤ _ := by
        have h6 := pow_le_pow_right₀ (by linarith : 1 ≤ Y) (show 6 ≤ 13 by decide)
        have h7 := pow_le_pow_right₀ (by linarith : 1 ≤ Y) (show 7 ≤ 13 by decide)
        have h9 := pow_le_pow_right₀ (by linarith : 1 ≤ Y) (show 9 ≤ 13 by decide)
        nlinarith only [h6,h7,h9,pow_nonneg hY0 13]
  let N := ⌈Y⌉₊
  have hN : 1 ≤ N := by apply Nat.one_le_ceil_iff.mpr; linarith
  have hcast : Y ≤ (N : ℝ) := Nat.le_ceil _
  have hc : ⌈W⌉₊ ≤ 2^110*N^13 := Nat.ceil_le.mpr (hWp.trans (by push_cast; gcongr; norm_num))
  have hs := Nat.lt_size_self N
  have hs1 : 1 ≤ Nat.size N := by
    by_contra! hn
    have hz' : Nat.size N = 0 := by omega
    rw [hz', pow_zero] at hs
    omega
  have hs2 : 2^110*N^13 < 2^(110+13*Nat.size N) := by
    rw [pow_add, Nat.mul_comm 13, pow_mul]
    gcongr
  change Nat.size ⌈64*(1+Real.sqrt p.d)*(guardRadius p+scale p)/tolerance p⌉₊ + 1 ≤ _
  rw [hW]
  have hs3 := Nat.size_le.mpr (hc.trans_lt hs2)
  change _ ≤ 1024*Nat.size N
  omega

end LongTails.Proofs.WeightedInterpolationCost
