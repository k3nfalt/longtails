import LongTails.Algorithms.HessianOnlyFiniteSumThirdSmooth
import LongTails.Proofs.QuarticAccelerationGrowth
import LongTails.Proofs.QuarticTrialExecution

namespace LongTails.Proofs.HessianOnlyFiniteSumTuning

open LongTails.Setups.FiniteSumThirdSmoothConvex
open LongTails.Algorithms.HessianOnlyFiniteSumThirdSmooth

lemma scale_bounds (p : Params) (hp : spec.valid p) :
    3 ≤ scale p ∧ (p.n : ℝ) ≤ scale p ∧ p.L * p.R ^ 4 / p.ε + 1 ≤ scale p - 2 ∧
      p.G ≤ p.ε / p.R * scale p ∧ p.H ≤ p.ε / p.R ^ 2 * scale p := by
  rcases hp with ⟨hL, hR, hε, hG, hH⟩
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast NeZero.pos p.n
  have hGterm : 0 ≤ p.G * p.R / p.ε := by positivity
  have hHterm : 0 ≤ p.H * p.R ^ 2 / p.ε := by positivity
  have hLterm : 0 ≤ p.L * p.R ^ 4 / p.ε := by positivity
  have hQ : 3 ≤ scale p := by dsimp [scale]; linarith
  refine ⟨hQ, ?_, ?_, ?_, ?_⟩
  · dsimp [scale]; linarith
  · dsimp [scale]; linarith
  · have ht : p.G * p.R / p.ε ≤ scale p := by dsimp [scale]; linarith
    have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ p.ε / p.R by positivity)
    have he : (p.ε / p.R) * (p.G * p.R / p.ε) = p.G := by field_simp
    rwa [he] at hm
  · have ht : p.H * p.R ^ 2 / p.ε ≤ scale p := by dsimp [scale]; linarith
    have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ p.ε / p.R ^ 2 by positivity)
    have he : (p.ε / p.R ^ 2) * (p.H * p.R ^ 2 / p.ε) = p.H := by field_simp
    rwa [he] at hm

lemma padding_bounds (p : Params) (hp : spec.valid p) :
    0 < padding p ∧ p.ε / p.R ^ 4 ≤ padding p ∧ padding p ≤ p.ε / p.R ^ 4 * scale p := by
  rcases hp with ⟨hL, hR, hε, hG, hH⟩
  have hsmall : 0 < p.ε / p.R ^ 4 := by positivity
  have hlo : p.ε / p.R ^ 4 ≤ padding p := by dsimp [padding]; linarith
  refine ⟨hsmall.trans_le hlo, hlo, ?_⟩
  have hq := (scale_bounds p ⟨hL, hR, hε, hG, hH⟩).2.2.1
  have ht : p.L * p.R ^ 4 / p.ε + 1 ≤ scale p := by linarith
  have hm := mul_le_mul_of_nonneg_left ht hsmall.le
  have he : (p.ε / p.R ^ 4) * (p.L * p.R ^ 4 / p.ε + 1) = padding p := by
    dsimp [padding]
    field_simp
  rwa [he] at hm

lemma regularization_bounds (p : Params) (hp : spec.valid p) :
    0 < regularization p ∧ p.ε / (p.R ^ 4 * scale p) ≤ regularization p ∧
    regularization p ≤ p.ε / p.R ^ 4 * scale p ∧
    padding p ≤ (p.n : ℝ) * regularization p ∧
    padding p + 6 * regularization p ≤ regularization p * scale p ^ 2 := by
  have hR := hp.2.1
  have hε := hp.2.2.1
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast NeZero.pos p.n
  have hs := scale_bounds p hp
  have hM := padding_bounds p hp
  have hγ : 0 < regularization p := div_pos hM.1 hn
  have hid : (p.n : ℝ) * regularization p = padding p := by dsimp [regularization]; field_simp
  refine ⟨hγ, ?_, ?_, hid.symm.le, ?_⟩
  · calc
      _ = (p.ε / p.R ^ 4) / scale p := by ring
      _ ≤ (p.ε / p.R ^ 4) / p.n := div_le_div_of_nonneg_left (by positivity) hn hs.2.1
      _ ≤ regularization p := div_le_div_of_nonneg_right hM.2.1 hn.le
  · have hh : regularization p ≤ padding p := by
      apply (div_le_iff₀ hn).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hn1 hM.1.le]
    exact hh.trans hM.2.2
  · have hnum : (p.n : ℝ) + 6 ≤ scale p ^ 2 := by nlinarith [hs.1, hs.2.1]
    have hm := mul_le_mul_of_nonneg_left hnum hγ.le
    rw [← hid]
    nlinarith only [hm]

lemma regularization_scale (p : Params) (hp : spec.valid p) :
    regularization p * p.R ^ 4 / p.ε = (p.L * p.R ^ 4 / p.ε + 1) / p.n := by
  have hR := hp.2.1
  have hε := hp.2.2.1
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  dsimp [regularization, padding]
  field_simp

lemma iterations_bounds (p : Params) (hp : spec.valid p) :
    0 < iterations p ∧ (iterations p : ℝ) ≤ 256 * scale p ∧
    64 * (1 + (regularization p * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ)) ≤ (iterations p : ℝ) := by
  have hL := hp.1
  have hR := hp.2.1
  have hε := hp.2.2.1
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast NeZero.pos p.n
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hs := scale_bounds p hp
  let v := (p.L * p.R ^ 4 / p.ε + 1) / p.n
  have hv : 0 < v := by dsimp [v]; positivity
  have hvQ : v ≤ scale p - 2 := by
    have hh : v ≤ p.L * p.R ^ 4 / p.ε + 1 := by
      apply (div_le_iff₀ hnpos).mpr
      have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ p.L * p.R ^ 4 / p.ε + 1 by positivity)
      simpa only [mul_one] using hm
    exact hh.trans hs.2.2.1
  have hr : v ^ (1 / 5 : ℝ) ≤ scale p - 2 := by
    have h1 : 1 ≤ scale p - 2 := by linarith [hs.1]
    calc
      _ ≤ (scale p - 2) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hv.le hvQ (by norm_num)
      _ ≤ (scale p - 2) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = _ := Real.rpow_one _
  have hpos : 0 < 64 * (1 + v ^ (1 / 5 : ℝ)) := by positivity
  refine ⟨Nat.ceil_pos.mpr hpos, ?_, ?_⟩
  · have hceil := Nat.ceil_lt_add_one hpos.le
    change (iterations p : ℝ) < 64 * (1 + v ^ (1 / 5 : ℝ)) + 1 at hceil
    nlinarith only [hceil, hr, hs.1]
  · rw [regularization_scale p hp]
    exact Nat.le_ceil _


lemma scaled_fifth_root {n U : ℝ} (hn : 1 ≤ n) (hU : 0 ≤ U) :
    n * ((U + 1) / n) ^ (1 / 5 : ℝ) ≤ n + (n ^ 4 * U) ^ (1 / 5 : ℝ) := by
  have hnpos : 0 < n := by linarith
  let r := ((U + 1) / n) ^ (1 / 5 : ℝ)
  let a := (n ^ 4 * U) ^ (1 / 5 : ℝ)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hnr : (n * r) ^ 5 = n ^ 4 * (U + 1) := by
    dsimp [r]
    rw [mul_pow, QuarticAccelerationGrowth.fifth_root_pow (by positivity : 0 ≤ (U + 1) / n)]
    field_simp
  have hap : a ^ 5 = n ^ 4 * U := QuarticAccelerationGrowth.fifth_root_pow (by positivity)
  have hn4 : n ^ 4 ≤ n ^ 5 := by
    have hh := mul_le_mul_of_nonneg_right hn (pow_nonneg hnpos.le 4)
    nlinarith only [hh]
  have hpoly : n ^ 5 + a ^ 5 ≤ (n + a) ^ 5 := by
    have hh : 0 ≤ 5 * n ^ 4 * a + 10 * n ^ 3 * a ^ 2 + 10 * n ^ 2 * a ^ 3 + 5 * n * a ^ 4 := by positivity
    nlinarith only [hh]
  apply (pow_le_pow_iff_left₀ (mul_nonneg hnpos.le hr) (add_nonneg hnpos.le ha) (by norm_num : (5 : ℕ) ≠ 0)).mp
  nlinarith only [hnr, hap, hn4, hpoly]

lemma component_iterations_bound (p : Params) (hp : spec.valid p) :
    p.n * iterations p ≤ 129 * (p.n + ⌈((p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ)⌉₊) := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast NeZero.pos p.n
  have hL := hp.1
  have hR := hp.2.1
  have hε := hp.2.2.1
  let U := p.L * p.R ^ 4 / p.ε
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hroot := scaled_fifth_root hn hU
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 64 * (1 + ((U + 1) / p.n) ^ (1 / 5 : ℝ)) by positivity)
  change (iterations p : ℝ) < 64 * (1 + ((U + 1) / p.n) ^ (1 / 5 : ℝ)) + 1 at hceil
  have hm := mul_le_mul_of_nonneg_left hceil.le (show 0 ≤ (p.n : ℝ) by positivity)
  have hround := Nat.le_ceil (((p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ))
  have he : (p.n : ℝ) ^ 4 * U = (p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε := by dsimp [U]; ring
  rw [he] at hroot
  have hnreal : (p.n : ℝ) * iterations p ≤ 129 * ((p.n : ℝ) +
      (⌈((p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ)⌉₊ : ℝ)) := by
    have ha : 0 ≤ ((p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ) := by positivity
    nlinarith only [hm, hroot, hround, ha]
  exact_mod_cast hnreal

lemma calls_bound (p : Params) (hp : spec.valid p) :
    calls p ≤ 2 ^ 38 * (p.n + ⌈((p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ)⌉₊) *
      (1 + ⌈Real.log (scale p)⌉₊) ^ 2 := by
  have ht := QuarticTrialExecution.trialCost_bound p.n (scale p)
  have hn := component_iterations_bound p hp
  unfold calls
  calc
    _ ≤ (2 ^ 29 * p.n * LongTails.Algorithms.QuarticProximalTrial.logarithm (scale p) ^ 2) * iterations p :=
      Nat.mul_le_mul_right _ ht
    _ = 2 ^ 29 * (p.n * iterations p) * (1 + ⌈Real.log (scale p)⌉₊) ^ 2 := by
      unfold LongTails.Algorithms.QuarticProximalTrial.logarithm
      ring
    _ ≤ 2 ^ 29 * (129 * (p.n + ⌈((p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ)⌉₊)) *
        (1 + ⌈Real.log (scale p)⌉₊) ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_right ((p.n + ⌈((p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ)⌉₊) *
        (1 + ⌈Real.log (scale p)⌉₊) ^ 2) (show 2 ^ 29 * 129 ≤ 2 ^ 38 by norm_num)
      nlinarith only [hh]


end LongTails.Proofs.HessianOnlyFiniteSumTuning
