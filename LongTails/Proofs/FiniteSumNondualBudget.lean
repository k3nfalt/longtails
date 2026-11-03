import LongTails.Algorithms.FiniteSumNondual
import LongTails.Proofs.KnownValueNondualBudget

namespace LongTails.Proofs.FiniteSumNondualBudget

open LongTails.Setups.FiniteSumNondualSmoothConvex
open LongTails.Algorithms.FiniteSumNondual

noncomputable def binaryScale (p : Params) : ℕ := 2 ^ logSize p

lemma scale_pos (p : Params) (hp : spec.valid p) : 0 < scale p := by
  obtain ⟨_, _, hL, hR, hε⟩ := hp
  unfold scale
  positivity

lemma logSize_pos (p : Params) : 0 < logSize p := by unfold logSize; omega

lemma rootSize_pos (p : Params) : 0 < rootSize p := by unfold rootSize; omega

lemma phaseSize_pos (p : Params) : 0 < phaseSize p := by
  unfold phaseSize
  exact Nat.mul_pos (Nat.mul_pos (by decide) (rootSize_pos p)) (logSize_pos p)

lemma requestCount_pos (p : Params) : 0 < requestCount p := by
  unfold requestCount
  exact Nat.mul_pos (Nat.mul_pos (logSize_pos p) (Nat.mul_pos (by decide) (phaseSize_pos p))) (by omega)

lemma binaryScale_two (p : Params) : 2 ≤ binaryScale p := by
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (logSize_pos p)
  simpa only [pow_one, binaryScale] using hh

lemma log_arg_lt (p : Params) : 2 + p.d + p.n + ⌈scale p⌉₊ < binaryScale p := by
  simpa only [binaryScale, logSize, Nat.add_comm 1, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) (2 + p.d + p.n + ⌈scale p⌉₊)

lemma scale_le_binary (p : Params) : scale p ≤ binaryScale p := by
  have hh := Nat.le_ceil (scale p)
  have hn : ⌈scale p⌉₊ ≤ binaryScale p := by have := log_arg_lt p; omega
  exact hh.trans (by exact_mod_cast hn)

lemma n_le_binary (p : Params) : p.n ≤ binaryScale p := by have := log_arg_lt p; omega

lemma logSize_le_binary (p : Params) : logSize p ≤ binaryScale p := Nat.lt_two_pow_self.le

lemma root_cube_lower (p : Params) (hp : spec.valid p) : scale p / p.n ≤ (rootSize p : ℝ) ^ 3 := by
  have hx : 0 ≤ scale p / p.n := div_nonneg (scale_pos p hp).le (Nat.cast_nonneg _)
  have hr := Real.rpow_nonneg hx (1 / 3 : ℝ)
  have hh : (scale p / p.n) ^ (1 / 3 : ℝ) ≤ (rootSize p : ℝ) := by
    have h := Nat.le_ceil ((scale p / p.n) ^ (1 / 3 : ℝ))
    simp only [rootSize, Nat.cast_add, Nat.cast_one]
    linarith
  have hpow := pow_le_pow_left₀ hr hh 3
  rwa [KnownValueNondualBudget.root_cube hx] at hpow

lemma root_le_binary (p : Params) (hp : spec.valid p) : rootSize p ≤ binaryScale p := by
  have hA := (scale_pos p hp).le
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast NeZero.pos p.n
  have hx : scale p / p.n ≤ scale p := (div_le_self hA hn)
  have hr := KnownValueNondualBudget.rpow_fraction_le_add_one
    (div_nonneg hA (Nat.cast_nonneg p.n)) (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hc := Nat.le_ceil (scale p)
  have hh : ⌈(scale p / p.n) ^ (1 / 3 : ℝ)⌉₊ ≤ 1 + ⌈scale p⌉₊ := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  unfold rootSize
  have := log_arg_lt p
  omega

lemma phaseSize_le_binary (p : Params) (hp : spec.valid p) : phaseSize p ≤ binaryScale p ^ 8 := by
  have hB := binaryScale_two p
  have h64 : 64 ≤ binaryScale p ^ 6 := by
    have hh := Nat.pow_le_pow_left hB 6
    norm_num at hh
    exact hh
  calc
    phaseSize p ≤ binaryScale p ^ 6 * binaryScale p * binaryScale p :=
      Nat.mul_le_mul (Nat.mul_le_mul h64 (root_le_binary p hp)) (logSize_le_binary p)
    _ = binaryScale p ^ 8 := by ring

lemma phaseFuel_le_binary (p : Params) (hp : spec.valid p) : 10 * phaseSize p ≤ binaryScale p ^ 12 := by
  have h10 : 10 ≤ binaryScale p ^ 4 := by
    have hh := Nat.pow_le_pow_left (binaryScale_two p) 4
    norm_num at hh
    omega
  exact (Nat.mul_le_mul h10 (phaseSize_le_binary p hp)).trans_eq (by ring)

lemma lineCalls_le_binary (p : Params) : lineFuel p + 2 ≤ binaryScale p ^ 8 := by
  have hB := binaryScale_two p
  have h128 : 128 ≤ binaryScale p ^ 7 := by
    have hh := Nat.pow_le_pow_left hB 7
    norm_num at hh
    exact hh
  have hline : lineFuel p + 2 ≤ 128 * binaryScale p := by
    unfold lineFuel
    have hh := logSize_le_binary p
    omega
  exact hline.trans ((Nat.mul_le_mul_right (binaryScale p) h128).trans_eq (by ring))

lemma requestCount_le_binary (p : Params) (hp : spec.valid p) : requestCount p ≤ binaryScale p ^ 21 := by
  calc
    requestCount p ≤ binaryScale p * binaryScale p ^ 12 * binaryScale p ^ 8 :=
      Nat.mul_le_mul (Nat.mul_le_mul (logSize_le_binary p) (phaseFuel_le_binary p hp)) (lineCalls_le_binary p)
    _ = binaryScale p ^ 21 := by ring

lemma dimension_log_bound (p : Params) : 1 + Nat.log 2 p.d ≤ logSize p := by
  unfold logSize
  exact Nat.add_le_add_left (Nat.log_mono_right (by omega : p.d ≤ 2 + p.d + p.n + ⌈scale p⌉₊)) 1

lemma phase_log_bound (p : Params) (hp : spec.valid p) : 1 + Nat.log 2 (10 * phaseSize p) ≤ 16 * logSize p := by
  have hh := Nat.log_mono_right (b := 2) (phaseFuel_le_binary p hp)
  rw [binaryScale, ← pow_mul, Nat.log_pow (by decide : 1 < 2)] at hh
  have hl := logSize_pos p
  omega

lemma smoothing_scale (p : Params) (hp : spec.valid p) :
    smoothing p * p.R ^ 2 = (scale p / p.n) * p.ε := by
  have hε := hp.2.2.2.2
  unfold smoothing scale
  field_simp

lemma cube_budget (p : Params) (hp : spec.valid p) :
    512 * smoothing p * p.R ^ 2 * (1 + Nat.log 2 p.d : ℕ) *
      (1 + Nat.log 2 (10 * phaseSize p) : ℕ) ≤ (phaseSize p : ℝ) ^ 3 * p.ε := by
  have hε := hp.2.2.2.2
  have hA := (scale_pos p hp).le
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ rootSize p := Nat.cast_nonneg _
  have hl : (1 : ℝ) ≤ logSize p := by exact_mod_cast logSize_pos p
  have hlsq : (logSize p : ℝ) ^ 2 ≤ (logSize p : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hl (sq_nonneg (logSize p : ℝ))]
  have hb : 512 * (scale p / p.n) * (1 + Nat.log 2 p.d : ℕ) *
      (1 + Nat.log 2 (10 * phaseSize p) : ℕ) ≤ (phaseSize p : ℝ) ^ 3 := by
    calc
      _ ≤ 512 * (rootSize p : ℝ) ^ 3 * (logSize p : ℝ) * (16 * (logSize p : ℝ)) := by
        gcongr
        · exact root_cube_lower p hp
        · exact_mod_cast dimension_log_bound p
        · exact_mod_cast phase_log_bound p hp
      _ = 8192 * (rootSize p : ℝ) ^ 3 * (logSize p : ℝ) ^ 2 := by ring
      _ ≤ 8192 * (rootSize p : ℝ) ^ 3 * (logSize p : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hlsq (by positivity)
      _ ≤ 262144 * (rootSize p : ℝ) ^ 3 * (logSize p : ℝ) ^ 3 := by gcongr; norm_num
      _ = (phaseSize p : ℝ) ^ 3 := by simp only [phaseSize, Nat.cast_mul, Nat.cast_ofNat]; ring
  have hh := mul_le_mul_of_nonneg_right hb hε.le
  have he := smoothing_scale p hp
  nlinarith only [hh, congrArg (fun v : ℝ => 512 * v *
    (1 + Nat.log 2 p.d : ℕ) * (1 + Nat.log 2 (10 * phaseSize p) : ℕ)) he]

lemma line_precision (p : Params) (hp : spec.valid p) :
    4 * smoothing p * p.R ^ 2 / (2 : ℝ) ^ lineFuel p ≤ p.ε / (64 * phaseSize p) := by
  have hε := hp.2.2.2.2
  have hB : (2 : ℝ) ≤ binaryScale p := by exact_mod_cast binaryScale_two p
  have hA := (scale_pos p hp).le
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast NeZero.pos p.n
  have ha : scale p / p.n ≤ binaryScale p := (div_le_self hA hn).trans (scale_le_binary p)
  have hm : (phaseSize p : ℝ) ≤ (binaryScale p : ℝ) ^ 8 := by exact_mod_cast phaseSize_le_binary p hp
  have h256 : (256 : ℝ) ≤ (binaryScale p : ℝ) ^ 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hB 8
    norm_num at hh
    exact hh
  have hh : 256 * (scale p / p.n) * (phaseSize p : ℝ) ≤ (2 : ℝ) ^ lineFuel p := by
    calc
      _ ≤ (binaryScale p : ℝ) ^ 8 * (binaryScale p : ℝ) * (binaryScale p : ℝ) ^ 8 := by gcongr
      _ = (binaryScale p : ℝ) ^ 17 := by ring
      _ ≤ (binaryScale p : ℝ) ^ 64 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ = (2 : ℝ) ^ lineFuel p := by simp only [binaryScale, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, lineFuel, Nat.mul_comm]
  have hmul := mul_le_mul_of_nonneg_left hh hε.le
  have he := smoothing_scale p hp
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ lineFuel p)
    (by positivity [phaseSize_pos p] : 0 < 64 * (phaseSize p : ℝ))).mpr
  nlinarith only [hmul, congrArg (fun v : ℝ => 256 * v * (phaseSize p : ℝ)) he]

lemma smoothing_pos (p : Params) (hp : spec.valid p) : 0 < smoothing p := by
  have hL := hp.2.2.1
  have hn : (0 : ℝ) < p.n := Nat.cast_pos.mpr (NeZero.pos p.n)
  unfold smoothing
  positivity

lemma tolerance_pos (p : Params) (hp : spec.valid p) : 0 < residualTolerance p := by
  have hε := hp.2.2.2.2
  have hR := hp.2.2.2.1
  have hm : (0 : ℝ) < phaseSize p := Nat.cast_pos.mpr (phaseSize_pos p)
  have hμ := smoothing_pos p hp
  unfold residualTolerance
  positivity

lemma tolerance_line (p : Params) (hp : spec.valid p) :
    2 * p.R * residualTolerance p ≤ p.ε / (64 * phaseSize p) := by
  have hR := hp.2.2.2.1
  have hm : (0 : ℝ) < phaseSize p := Nat.cast_pos.mpr (phaseSize_pos p)
  have hh := mul_le_mul_of_nonneg_left
    (min_le_left (p.ε / (128 * phaseSize p * p.R)) (Real.sqrt (smoothing p * p.ε / (32 * phaseSize p))))
    (show 0 ≤ 2 * p.R by positivity)
  change 2 * p.R * residualTolerance p ≤ 2 * p.R * (p.ε / (128 * phaseSize p * p.R)) at hh
  convert hh using 1
  field_simp
  ring

lemma tolerance_value (p : Params) (hp : spec.valid p) :
    residualTolerance p ^ 2 / (2 * smoothing p) ≤ p.ε / (64 * phaseSize p) := by
  have hε := hp.2.2.2.2
  have hm : (0 : ℝ) < phaseSize p := Nat.cast_pos.mpr (phaseSize_pos p)
  have hμ := smoothing_pos p hp
  have hh := min_le_right (p.ε / (128 * phaseSize p * p.R)) (Real.sqrt (smoothing p * p.ε / (32 * phaseSize p)))
  have hs := pow_le_pow_left₀ (tolerance_pos p hp).le hh 2
  rw [Real.sq_sqrt (by positivity)] at hs
  apply (div_le_iff₀ (by positivity : 0 < 2 * smoothing p)).mpr
  convert hs using 1
  field_simp
  ring

lemma initial_bound (p : Params) (hp : spec.valid p) :
    p.L * p.R ^ 2 / 2 ≤ p.ε / 2 * (2 : ℝ) ^ logSize p := by
  have hε := hp.2.2.2.2
  have hh := mul_le_mul_of_nonneg_right (scale_le_binary p) hε.le
  have he : scale p * p.ε = p.L * p.R ^ 2 := by unfold scale; field_simp
  rw [he] at hh
  simp only [binaryScale, Nat.cast_pow, Nat.cast_ofNat] at hh
  nlinarith

lemma requestCount_polynomial (p : Params) : requestCount p ≤ 42240 * rootSize p * logSize p ^ 3 := by
  have hl := logSize_pos p
  have hh : lineFuel p + 2 ≤ 66 * logSize p := by unfold lineFuel; omega
  calc
    requestCount p ≤ logSize p * (10 * phaseSize p) * (66 * logSize p) := Nat.mul_le_mul_left _ hh
    _ = 42240 * rootSize p * logSize p ^ 3 := by unfold phaseSize; ring

lemma total_cost_bound (p : Params) :
    p.n + requestCount p * ((145 * epochCount p + 3) * p.n) ≤
      1099511627776 * p.n * rootSize p * logSize p ^ 4 := by
  have hl := logSize_pos p
  have hr := rootSize_pos p
  have hc : 145 * epochCount p + 3 ≤ 74243 * logSize p := by unfold epochCount; omega
  have hb : p.n ≤ p.n * rootSize p * logSize p ^ 4 := by
    have h1 : 1 ≤ rootSize p := hr
    have h2 : 1 ≤ logSize p ^ 4 := Nat.one_le_pow _ _ hl
    nlinarith [Nat.mul_le_mul_left p.n h1, Nat.mul_le_mul_left (p.n * rootSize p) h2]
  calc
    _ ≤ p.n + (42240 * rootSize p * logSize p ^ 3) * ((74243 * logSize p) * p.n) := by
      gcongr
      exact requestCount_polynomial p
    _ ≤ p.n * rootSize p * logSize p ^ 4 +
        (42240 * rootSize p * logSize p ^ 3) * ((74243 * logSize p) * p.n) := Nat.add_le_add_right hb _
    _ = 3136024321 * p.n * rootSize p * logSize p ^ 4 := by ring
    _ ≤ 1099511627776 * p.n * rootSize p * logSize p ^ 4 := by gcongr; norm_num

lemma polynomial_decay (p : Params) (k : ℕ) (hk : k ≤ 128) :
    (binaryScale p : ℝ) ^ k * (3 / 4 : ℝ) ^ epochCount p ≤ 1 := by
  have hB : (1 : ℝ) ≤ binaryScale p := by
    have hh := binaryScale_two p
    exact_mod_cast (show 1 ≤ binaryScale p by omega)
  calc
    _ ≤ (binaryScale p : ℝ) ^ 128 * (3 / 4 : ℝ) ^ epochCount p := by
      gcongr
    _ = ((2 : ℝ) * (3 / 4 : ℝ) ^ 4) ^ (128 * logSize p) := by
      simp only [binaryScale, Nat.cast_pow, Nat.cast_ofNat, epochCount, mul_pow, ← pow_mul]
      congr 1 <;> congr 1 <;> omega
    _ ≤ 1 ^ (128 * logSize p) := by gcongr; norm_num
    _ = 1 := one_pow _

noncomputable def failureRate (p : Params) : ℝ := 1 / (scale p * requestCount p)

lemma failureRate_pos (p : Params) (hp : spec.valid p) : 0 < failureRate p := by
  have ha := scale_pos p hp
  have hm : (0 : ℝ) < requestCount p := Nat.cast_pos.mpr (requestCount_pos p)
  unfold failureRate
  positivity

lemma first_ratio (p : Params) (hp : spec.valid p) :
    262144 * scale p ^ 3 * requestCount p * (phaseSize p : ℝ) ^ 2 ≤ (binaryScale p : ℝ) ^ 58 := by
  have hB : (2 : ℝ) ≤ binaryScale p := by exact_mod_cast binaryScale_two p
  have hc : (262144 : ℝ) ≤ (binaryScale p : ℝ) ^ 18 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hB 18
    norm_num at hh
    exact hh
  have ha := scale_le_binary p
  have ha0 := (scale_pos p hp).le
  have hm : (requestCount p : ℝ) ≤ (binaryScale p : ℝ) ^ 21 := by exact_mod_cast requestCount_le_binary p hp
  have ht : (phaseSize p : ℝ) ≤ (binaryScale p : ℝ) ^ 8 := by exact_mod_cast phaseSize_le_binary p hp
  calc
    _ ≤ (binaryScale p : ℝ) ^ 18 * (binaryScale p : ℝ) ^ 3 *
        (binaryScale p : ℝ) ^ 21 * ((binaryScale p : ℝ) ^ 8) ^ 2 := by gcongr
    _ = (binaryScale p : ℝ) ^ 58 := by ring

lemma second_ratio (p : Params) (hp : spec.valid p) :
    512 * (p.n : ℝ) * scale p ^ 2 * requestCount p * phaseSize p ≤ (binaryScale p : ℝ) ^ 41 := by
  have hB : (2 : ℝ) ≤ binaryScale p := by exact_mod_cast binaryScale_two p
  have hc : (512 : ℝ) ≤ (binaryScale p : ℝ) ^ 9 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hB 9
    norm_num at hh
    exact hh
  have hn : (p.n : ℝ) ≤ binaryScale p := by exact_mod_cast n_le_binary p
  have ha := scale_le_binary p
  have ha0 := (scale_pos p hp).le
  have hm : (requestCount p : ℝ) ≤ (binaryScale p : ℝ) ^ 21 := by exact_mod_cast requestCount_le_binary p hp
  have ht : (phaseSize p : ℝ) ≤ (binaryScale p : ℝ) ^ 8 := by exact_mod_cast phaseSize_le_binary p hp
  calc
    _ ≤ (binaryScale p : ℝ) ^ 9 * (binaryScale p : ℝ) * (binaryScale p : ℝ) ^ 2 *
        (binaryScale p : ℝ) ^ 21 * (binaryScale p : ℝ) ^ 8 := by gcongr
    _ = (binaryScale p : ℝ) ^ 41 := by ring

lemma residual_failure_budget (p : Params) (hp : spec.valid p) :
    16 * p.L ^ 2 * p.R ^ 2 * (3 / 4 : ℝ) ^ epochCount p ≤
      failureRate p * residualTolerance p ^ 2 := by
  have hL := hp.2.2.1
  have hR := hp.2.2.2.1
  have hε := hp.2.2.2.2
  have hn : (0 : ℝ) < p.n := Nat.cast_pos.mpr (NeZero.pos p.n)
  have hm : (0 : ℝ) < phaseSize p := Nat.cast_pos.mpr (phaseSize_pos p)
  have hM : (0 : ℝ) < requestCount p := Nat.cast_pos.mpr (requestCount_pos p)
  have hμ := smoothing_pos p hp
  have hq := (failureRate_pos p hp).le
  have hdec : 0 ≤ (3 / 4 : ℝ) ^ epochCount p := by positivity
  have hr1 := (mul_le_mul_of_nonneg_right (first_ratio p hp) hdec).trans
    (polynomial_decay p 58 (by norm_num))
  have hr2 := (mul_le_mul_of_nonneg_right (second_ratio p hp) hdec).trans
    (polynomial_decay p 41 (by norm_num))
  have he1 : 16 * p.L ^ 2 * p.R ^ 2 =
      (failureRate p * (p.ε / (128 * phaseSize p * p.R)) ^ 2) *
        (262144 * scale p ^ 3 * requestCount p * (phaseSize p : ℝ) ^ 2) := by
    unfold failureRate scale
    field_simp
    ring
  have he2 : 16 * p.L ^ 2 * p.R ^ 2 =
      (failureRate p * (smoothing p * p.ε / (32 * phaseSize p))) *
        (512 * (p.n : ℝ) * scale p ^ 2 * requestCount p * phaseSize p) := by
    unfold failureRate scale smoothing
    field_simp
    ring
  have hb1 := mul_le_mul_of_nonneg_left hr1
    (show 0 ≤ failureRate p * (p.ε / (128 * phaseSize p * p.R)) ^ 2 by positivity)
  have hb2 := mul_le_mul_of_nonneg_left hr2
    (show 0 ≤ failureRate p * (smoothing p * p.ε / (32 * phaseSize p)) by positivity)
  rw [← mul_assoc, ← he1, mul_one] at hb1
  rw [← mul_assoc, ← he2, mul_one] at hb2
  unfold residualTolerance
  rcases le_total (p.ε / (128 * phaseSize p * p.R))
    (Real.sqrt (smoothing p * p.ε / (32 * phaseSize p))) with hh | hh
  · rw [min_eq_left hh]
    exact hb1
  · rw [min_eq_right hh, Real.sq_sqrt (by positivity)]
    exact hb2

lemma failure_loss (p : Params) (hp : spec.valid p) :
    (p.L * p.R ^ 2 / 2) * requestCount p * failureRate p = p.ε / 2 := by
  have hL := hp.2.2.1
  have hR := hp.2.2.2.1
  have hε := hp.2.2.2.2
  have hM : (0 : ℝ) < requestCount p := Nat.cast_pos.mpr (requestCount_pos p)
  unfold failureRate scale
  field_simp

end LongTails.Proofs.FiniteSumNondualBudget
