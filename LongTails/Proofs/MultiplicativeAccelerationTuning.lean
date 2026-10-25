import LongTails.Proofs.AdaptiveHistoryAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace LongTails.Proofs.MultiplicativeAccelerationTuning

lemma power_linear_complement {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (1+r)^n*(1-(n : ℝ)*r) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (1+r)*(1-((n : ℝ)+1)*r) ≤ 1-(n : ℝ)*r := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ n+1 by positivity) (sq_nonneg r)]
    have hh := mul_le_mul_of_nonneg_left hc (pow_nonneg (by linarith : 0 ≤ 1+r) n)
    rw [pow_succ]
    push_cast
    nlinarith only [hh, ih]

lemma power_le_two {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (hn : (n : ℝ)*r ≤ 1/2) :
    (1+r)^n ≤ 2 := by
  have h := power_linear_complement hr n
  have hh := mul_le_mul_of_nonneg_left hn (pow_nonneg (by linarith : 0 ≤ 1+r) n)
  nlinarith only [h, hh]

lemma bias_variance_ratio {p H : ℝ} (hp : 1 < p) (hH : 1 ≤ H) :
    ((H^(1/(3*p-2)))^(1-p)/16)^2 / (2*(32*(H^(1/(3*p-2)))^(2-p))) =
      H^(-(p/(3*p-2)))/16384 := by
  have hHp : 0 < H := by linarith
  have hdp : 0 < 3*p-2 := by linarith
  have hpow : 0 < H^(1/(3*p-2)) := Real.rpow_pos_of_pos hHp _
  rw [div_pow, ← Real.rpow_two ((H^(1/(3*p-2)))^(1-p)), ← Real.rpow_mul hpow.le]
  rw [← Real.rpow_mul hHp.le, ← Real.rpow_mul hHp.le]
  have he : 1/(3*p-2)*((1-p)*2) - 1/(3*p-2)*(2-p) = -(p/(3*p-2)) := by ring
  rw [← he, Real.rpow_sub hHp]
  ring

lemma bias_growth_bound {p H : ℝ} (hp : 1 < p) (hH : 1 ≤ H) :
    (1+((H^(1/(3*p-2)))^(1-p)/16)^2 /
      (2*(32*(H^(1/(3*p-2)))^(2-p))))^⌈128*H^(p/(3*p-2))⌉₊ ≤ 2 := by
  rw [bias_variance_ratio hp hH]
  apply power_le_two (by positivity)
  have hHp : 0 < H := by linarith
  have hdp : 0 < 3*p-2 := by linarith
  have hpow : 1 ≤ H^(p/(3*p-2)) :=
    Real.one_le_rpow hH (by positivity)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 128*H^(p/(3*p-2)) by positivity)
  have hmul := mul_le_mul_of_nonneg_right hceil.le
    (show 0 ≤ H^(-(p/(3*p-2)))/16384 by positivity)
  have hcancel : H^(p/(3*p-2))*H^(-(p/(3*p-2))) = 1 := by
    rw [← Real.rpow_add hHp]
    simp
  have hinv : H^(-(p/(3*p-2))) ≤ 1 := by
    rw [Real.rpow_neg hHp.le]
    exact inv_le_one_of_one_le₀ hpow
  nlinarith only [hmul, hcancel, hinv]

lemma pilot_failure_bound {p H : ℝ} (hp : 1 < p) (hH : 1 ≤ H) :
    (1/2 : ℝ)^(128+⌈2*Real.log H⌉₊+1) ≤ (H^(1/(3*p-2)))^(1-p)/64 := by
  have hHp : 0 < H := by linarith
  have hdp : 0 < 3*p-2 := by linarith
  have hn := Nat.le_ceil (2*Real.log H)
  have he := AdaptiveHistoryAlgebra.half_power_exponential (128+⌈2*Real.log H⌉₊+1)
  have hex : Real.exp (-((128+⌈2*Real.log H⌉₊+1 : ℕ) : ℝ)/2) ≤
      Real.exp (-64-Real.log H) := by
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have h64 : Real.exp (-64) ≤ (1:ℝ)/64 := by
    rw [Real.exp_neg]
    have hx := Real.add_one_le_exp (64:ℝ)
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 64) (by linarith : (64:ℝ) ≤ Real.exp 64))
  have hid : Real.exp (-64-Real.log H) = Real.exp (-64)/H := by
    rw [Real.exp_sub, Real.exp_log hHp]
  have hpow : H^(-1:ℝ) ≤ (H^(1/(3*p-2)))^(1-p) := by
    rw [← Real.rpow_mul hHp.le]
    apply Real.rpow_le_rpow_of_exponent_le hH
    rw [div_mul_eq_mul_div, one_mul]
    apply (le_div_iff₀ hdp).2
    linarith
  calc
    _ ≤ Real.exp (-64-Real.log H) := he.trans hex
    _ ≤ (1/64:ℝ)/H := by rw [hid]; exact div_le_div_of_nonneg_right h64 hHp.le
    _ = H^(-1:ℝ)/64 := by rw [Real.rpow_neg_one]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hpow (by norm_num)

lemma iteration_square_bound {p H : ℝ} (hp : 1 < p) (hH : 1 ≤ H) :
    256*(32*(H^(1/(3*p-2)))^(2-p))*H ≤
      (⌈128*H^(p/(3*p-2))⌉₊ : ℝ)^2 := by
  have hHp : 0 < H := by linarith
  have hd : 3*p-2 ≠ 0 := by linarith
  have hn := Nat.le_ceil (128*H^(p/(3*p-2)))
  have hs : (128*H^(p/(3*p-2)))^2 ≤ (⌈128*H^(p/(3*p-2))⌉₊ : ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) hn 2
  have hid : (H^(p/(3*p-2)))^2 = (H^(1/(3*p-2)))^(2-p)*H := by
    rw [← Real.rpow_two (H^(p/(3*p-2))), ← Real.rpow_mul hHp.le,
      ← Real.rpow_mul hHp.le]
    conv_rhs => arg 2; rw [← Real.rpow_one H]
    rw [← Real.rpow_add hHp]
    congr 1
    have hinv := inv_mul_cancel₀ hd
    simp only [div_eq_mul_inv]
    nlinarith only [hinv]
  rw [mul_pow, hid] at hs
  nlinarith [show 0 ≤ (H^(1/(3*p-2)))^(2-p)*H by positivity]

lemma batch_normalization {p ρ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hρ : 0 ≤ ρ) :
    4*65536^p*ρ ≤ ((⌈(17179869184*ρ)^(1/(p-1))⌉₊+1 : ℕ) : ℝ)^(p-1) := by
  have hsmall : (65536:ℝ)^p ≤ (65536:ℝ)^(2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 65536) hp2
  have hconstant : 4*65536^p*ρ ≤ 17179869184*ρ := by
    norm_num at hsmall
    nlinarith
  have hbase : (17179869184*ρ)^(1/(p-1)) ≤
      ((⌈(17179869184*ρ)^(1/(p-1))⌉₊+1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil ((17179869184*ρ)^(1/(p-1)))
    push_cast
    linarith
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (17179869184*ρ)^(1/(p-1)))
    hbase (by linarith : 0 ≤ p-1)
  rw [one_div, Real.rpow_inv_rpow (by positivity) (by linarith)] at hpow
  simpa only [one_div] using hconstant.trans hpow

lemma batch_cost {p ρ : ℝ} (hρ : 0 < ρ) :
    ⌈(17179869184*ρ)^(1/(p-1))⌉₊+1 ≤ 2*⌈(17179869184*ρ)^(1/(p-1))⌉₊ := by
  have hp : 0 < (17179869184*ρ)^(1/(p-1)) := Real.rpow_pos_of_pos (by positivity) _
  have hn : 0 < ⌈(17179869184*ρ)^(1/(p-1))⌉₊ := Nat.ceil_pos.mpr hp
  omega

lemma accuracy_algebra {L V R ε D : ℝ} {N : ℕ}
    (hL : 0 < L) (hV : 0 < V) (_hR : 0 ≤ R) (hε : 0 < ε)
    (hD : 0 ≤ D) (hDR : D ≤ R) (hN : 0 < N)
    (hs : 64*L*V*R^2/ε ≤ (N : ℝ)^2) :
    2*D^2/(2*((N : ℝ)*(N+1)/(64*L*V))) ≤ ε := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hd : 0 < 2*((N : ℝ)*(N+1)/(64*L*V)) := by positivity
  have hs' := (div_le_iff₀ hε).mp hs
  have hsq : D^2 ≤ R^2 := pow_le_pow_left₀ hD hDR 2
  apply (div_le_iff₀ hd).2
  apply (mul_le_mul_iff_of_pos_right (show 0 < 64*L*V by positivity)).mp
  field_simp
  nlinarith [mul_nonneg (show 0 ≤ 64*L*V by positivity) (sub_nonneg.mpr hsq)]

lemma deterministic_square_bound {H : ℝ} (hH : 1 ≤ H) :
    8192*H ≤ (⌈128*Real.sqrt H⌉₊ : ℝ)^2 := by
  have hn := Nat.le_ceil (128*Real.sqrt H)
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 128*Real.sqrt H) hn 2
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ H)] at hs
  nlinarith

end LongTails.Proofs.MultiplicativeAccelerationTuning
