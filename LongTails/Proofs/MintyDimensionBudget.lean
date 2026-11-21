import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace LongTails.Proofs.MintyDimensionBudget

lemma scaled_ratio (x ε d : ℝ) : x^2 / (d * ε^2) = (x/ε)^2/d := by
  rw [div_pow]
  ring

lemma entropy_le_sq {d : ℕ} (hd : 0 < d) (t : ℝ) :
    d * Real.log (1 + t^2 / d) ≤ t^2 := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + t^2 / d by positivity)
  calc
    _ ≤ d * (t^2 / d) := mul_le_mul_of_nonneg_left (by linarith) hd'.le
    _ = _ := mul_div_cancel₀ _ hd'.ne'

lemma packing {d N : ℕ} {t : ℝ} (hd : 0 < d) (ht : 0 < t) (hN : 0 < N)
    (hB : N ≤ ⌊(d : ℝ) * Real.log (1 + t^2 / d) / 4194304⌋₊) :
    ∃ k m : ℕ, 0 < k ∧ k ≤ d ∧ 8 ≤ m ∧ 32 * m * Real.sqrt k ≤ t ∧
      2 * (4 ^ N * 2 ^ k) ≤ m ^ k := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog := Real.log_nonneg (show 1 ≤ 1 + t^2 / d by linarith [div_nonneg (sq_nonneg t) hd'.le])
  have hb := (Nat.le_floor_iff (by positivity)).mp hB
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have ht2 := entropy_le_sq hd t
  have htbig : 256 ≤ t := by nlinarith
  let k := min d ⌊(t/256)^2⌋₊
  have hk : 0 < k := lt_min hd (Nat.floor_pos.mpr (by nlinarith))
  have hkd : k ≤ d := min_le_left _ _
  have hkf : k ≤ ⌊(t/256)^2⌋₊ := min_le_right _ _
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by positivity
  have hks := Real.sq_sqrt hk0.le
  have hroot := Real.sqrt_pos.mpr hk0
  have hkb := (Nat.le_floor_iff (sq_nonneg _)).mp hkf
  have h256 : 256 * Real.sqrt k ≤ t := by nlinarith
  let u := t / (32 * Real.sqrt k)
  have hu : 8 ≤ u := (le_div_iff₀ (by positivity)).mpr (by linarith)
  let m := ⌊u⌋₊
  have hm : 8 ≤ m := (Nat.le_floor_iff (by linarith : 0 ≤ u)).mpr (by exact_mod_cast hu)
  have hm' : (8:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hf := Nat.lt_floor_add_one u
  change u < (m : ℝ) + 1 at hf
  have hpack := (le_div_iff₀ (by positivity : 0 < 32 * Real.sqrt k)).mp (Nat.floor_le (by linarith : 0 ≤ u))
  have hmLog : 1 ≤ Real.log m := (Real.le_log_iff_exp_le hm0).mpr (by linarith [Real.exp_one_lt_three])
  have hrate : (d : ℝ) * Real.log (1 + t^2 / d) ≤ 131072 * k * Real.log m := by
    by_cases hdk : k = d
    · have hsmall : t ≤ 64 * m * Real.sqrt k := by
        have e := (div_lt_iff₀ (by positivity : 0 < 32 * Real.sqrt k)).mp hf
        nlinarith [mul_nonneg (by linarith : 0 ≤ (m:ℝ)-1) hroot.le]
      have hs := pow_le_pow_left₀ ht.le hsmall 2
      have hscale : t^2 / k ≤ 4096 * (m:ℝ)^2 := by
        apply (div_le_iff₀ hk0).mpr
        rw [mul_pow, hks] at hs
        linarith
      have hpow : (8:ℝ)^6 ≤ (m:ℝ)^6 := pow_le_pow_left₀ (by norm_num) hm' 6
      have hp : 1 + t^2 / k ≤ (m:ℝ)^8 := by
        rw [show (m:ℝ)^8 = (m:ℝ)^2*(m:ℝ)^6 by ring]
        nlinarith [mul_nonneg (sq_nonneg (m:ℝ)) (sub_nonneg.mpr hpow)]
      have hl := Real.log_le_log (by positivity) hp
      rw [Real.log_pow] at hl
      rw [← hdk]
      nlinarith [mul_le_mul_of_nonneg_left hl hk0.le,
        mul_nonneg hk0.le (Real.log_nonneg (by linarith : 1 ≤ (m:ℝ)))]
    · have he : k = ⌊(t/256)^2⌋₊ := min_eq_right (by
          by_contra hh
          exact hdk (min_eq_left (by omega)))
      have hkceil := Nat.lt_floor_add_one ((t/256)^2)
      rw [← he] at hkceil
      nlinarith [mul_le_mul_of_nonneg_left hmLog hk0.le]
  have hml := Real.log_le_log (by norm_num : (0:ℝ)<2^3) (by norm_num; exact hm : (2:ℝ)^3 ≤ m)
  rw [Real.log_pow] at hml
  have h2 := Real.log_two_lt_d9
  have h2pos := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hcost : (N : ℝ) ≤ k * Real.log m / 32 := by linarith
  have hcnt : 2 * ((4:ℝ)^N * 2^k) ≤ (m:ℝ)^k := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, hfour]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') h2pos.le,
      mul_le_mul_of_nonneg_left hml hk0.le,
      mul_le_mul_of_nonneg_left h2.le (show 0 ≤ (N:ℝ) by positivity)]
  refine ⟨k, m, hk, hkd, hm, ?_, by exact_mod_cast hcnt⟩
  change (m:ℝ) * (32 * Real.sqrt k) ≤ t at hpack
  linarith

lemma rounds_suffice {d : ℕ} {t : ℝ} (hd : 0 < d) (ht : 0 < t) (n : ℕ)
    (hn : 1024 * d * Real.log (1 + t^2 / d) ≤ n) :
    ((d : ℝ) ≤ t^2 → d * Real.log (512*t/Real.sqrt d) < n/8) ∧
    (t^2 ≤ d → 256*t^2 < n) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  let v := t^2 / d
  have hv : 0 < v := div_pos (sq_pos_of_pos ht) hd'
  have hvd : d*v = t^2 := mul_div_cancel₀ _ hd'.ne'
  have hh := Real.log_pos (by linarith : 1 < 1+v)
  change 1024 * d * Real.log (1+v) ≤ n at hn
  constructor
  · intro h
    have hu : 1 ≤ v := (le_div_iff₀ hd').mpr (by simpa using h)
    have hroot := Real.sqrt_pos.mpr hd'
    have he := Real.sq_sqrt hd'.le
    have ht' : Real.sqrt d ≤ t := by nlinarith
    have hv' : t / Real.sqrt d ≤ v := by
      apply (div_le_iff₀ hroot).mpr
      have hx := mul_le_mul_of_nonneg_left ht' ht.le
      apply (mul_le_mul_iff_left₀ hroot).mp
      calc
        t * Real.sqrt d ≤ t^2 := by linarith
        _ = v * Real.sqrt d * Real.sqrt d := by rw [mul_assoc, ← sq, he]; linarith
    have h2 := Real.log_le_log (by norm_num : 0 < (2:ℝ)) (by linarith : 2 ≤ 1+v)
    have hl := Real.log_le_log (div_pos ht hroot) (hv'.trans (by linarith : v ≤ 1+v))
    have heq : Real.log (512*t/Real.sqrt d) = 9*Real.log 2 + Real.log (t/Real.sqrt d) := by
      rw [show 512*t/Real.sqrt d = 2^9 * (t/Real.sqrt d) by ring,
        Real.log_mul (by norm_num) (div_pos ht hroot).ne', Real.log_pow]
      norm_num
    rw [heq]
    have hm := mul_le_mul_of_nonneg_left (by linarith only [h2, hl] :
      9*Real.log 2 + Real.log (t / Real.sqrt d) ≤ 10*Real.log (1+v)) hd'.le
    nlinarith only [hm, hn, mul_pos hd' hh]
  · intro h
    have hu : v ≤ 1 := (div_le_iff₀ hd').mpr (by simpa using h)
    have hl := Real.le_log_one_add_of_nonneg hv.le
    have hhalf : v / 2 ≤ Real.log (1+v) := by
      refine le_trans ((le_div_iff₀ (by linarith : 0 < v+2)).mpr ?_) hl
      nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hu)]
    nlinarith only [mul_le_mul_of_nonneg_left hhalf hd'.le, hn, hvd, sq_pos_of_pos ht]

end LongTails.Proofs.MintyDimensionBudget
