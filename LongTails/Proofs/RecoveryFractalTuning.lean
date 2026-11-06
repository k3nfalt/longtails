import LongTails.Proofs.RecoveryFractalSchedule

namespace LongTails.Proofs.RecoveryFractalTuning

open LongTails.Setups.SmoothHessianLipschitzGd LongTails.Algorithms.RecoveryFractalGd
open LongTails.Proofs.RecoveryFractalExecution

lemma selected_level_admissible (p : Params) (hk : 2 ≤ level p) : admissibleLevel p (level p) := by
  classical
  exact Nat.findGreatest_of_ne_zero rfl (by omega : level p ≠ 0)

lemma repetitions_square_bound (k : ℕ) (hk : 2 ≤ k) : (k + 8) ^ 2 ≤ 25 * 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    nlinarith

lemma repetitions_power_bound (k : ℕ) (hk : 2 ≤ k) : k + 8 ≤ (2 ^ k) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    nlinarith

lemma repetitions_le_sqrt (p : Params) (hk : 2 ≤ level p) :
    (repetitions p : ℝ) ≤ 5 * Real.sqrt (blockLength p) := by
  have hh : (repetitions p : ℝ) ^ 2 ≤ 25 * blockLength p := by
    exact_mod_cast repetitions_square_bound (level p) hk
  have hn : 0 ≤ (blockLength p : ℝ) := by positivity
  have hs := Real.sq_sqrt hn
  have hm0 : 0 ≤ (repetitions p : ℝ) := by positivity
  nlinarith [Real.sqrt_nonneg (blockLength p)]

lemma repetitions_le_block_square (p : Params) (hk : 2 ≤ level p) :
    (repetitions p : ℝ) ≤ (blockLength p : ℝ) ^ 2 := by
  exact_mod_cast repetitions_power_bound (level p) hk

lemma error_normalization (p : Params) (hL : 0 < p.L) :
    errorBound p * (blockLength p : ℝ) =
      1024 * (curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6) * p.ε := by
  have hn : (blockLength p : ℝ) ≠ 0 := by exact_mod_cast (blockLength_pos p).ne'
  unfold errorBound radius threshold lowerCurvature curvatureScale
  simp only [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg (blockLength p))]
  field_simp
  ring

lemma forcing_normalization (p : Params) (hL : 0 < p.L) :
    (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) =
      2048 * (curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6) * p.ε := by
  have hn : (blockLength p : ℝ) ≠ 0 := by exact_mod_cast (blockLength_pos p).ne'
  unfold epochLength radius threshold lowerCurvature curvatureScale
  push_cast
  field_simp
  ring_nf
  rw [Real.sq_sqrt (Nat.cast_nonneg (blockLength p))]
  ring

lemma normalized_smallness (n c ε E D : ℝ) (hn : 4 ≤ n) (hc : c ≤ 1 / 2 ^ 28)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (heq : E * n = 1024 * c * ε)
    (hD : D = 2048 * c * ε) : E ≤ ε / 256 ∧ D + E ≤ ε / 256 := by
  have hp := mul_le_mul_of_nonneg_right hc hε
  have hEn := mul_le_mul_of_nonneg_left hn hE
  norm_num at hp
  constructor <;> nlinarith only [hp, hEn, heq, hD, hε]

lemma sqrt_scaled_filter (n ε : ℝ) (hn : 1 ≤ n) (hε : 0 ≤ ε) :
    1 / (256 * n) * (Real.sqrt n * ε) ≤ ε / 256 := by
  have hn0 : 0 < n := by linarith
  have hs := Real.sq_sqrt hn0.le
  have hsqrt : Real.sqrt n ≤ n := by nlinarith [Real.sqrt_nonneg n]
  have hm := mul_le_mul_of_nonneg_right hsqrt hε
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
  have heq : 1 / (256 * n) * (Real.sqrt n * ε) * 256 = Real.sqrt n * ε / n := by field_simp
  rw [heq]
  exact (div_le_iff₀ hn0).mpr (by nlinarith only [hm])

lemma completed_small_conditions (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hε : 0 ≤ p.ε) (hk : 2 ≤ level p) :
    errorBound p ≤ p.ε / 256 ∧
    ((2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ threshold p) ∧
    (1 / (256 * blockLength p) * threshold p +
      (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ 3 * p.ε / 256) := by
  have hn : (4 : ℝ) ≤ blockLength p := by
    have hh : (4 : ℕ) ≤ 2 ^ level p := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ level p := Nat.pow_le_pow_right (by norm_num) hk
    exact_mod_cast hh
  let c := curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6
  have hc : c ≤ 1 / 2 ^ 28 := by
    have hh := (selected_level_admissible p hk).2.2.1
    simpa only [c, repetitions, blockLength, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow] using hh
  have hG0 : 0 ≤ threshold p := by unfold threshold; positivity
  have hB0 : 0 ≤ errorBound p := by unfold errorBound radius lowerCurvature; positivity
  obtain ⟨hE, hDE⟩ := normalized_smallness (blockLength p) c p.ε (errorBound p)
    ((2 * epochLength p : ℝ) * (4 / lowerCurvature p) * (p.ρ * radius p * (8 * threshold p)))
    hn hc hε hB0 (error_normalization p hL) (forcing_normalization p hL)
  have hfilter := sqrt_scaled_filter (blockLength p) p.ε (by linarith) hε
  change 1 / (256 * blockLength p) * threshold p ≤ p.ε / 256 at hfilter
  have hsqrt : 1 ≤ Real.sqrt (blockLength p) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (blockLength p)), Real.sqrt_nonneg (blockLength p)]
  have hG : p.ε ≤ threshold p := by
    have hh := mul_le_mul_of_nonneg_right hsqrt hε
    simpa [threshold] using hh
  exact ⟨hE, by linarith, by linarith⟩

lemma cubic_normalization (p : Params) (hL : 0 < p.L) :
    (p.ρ * radius p ^ 3 * lowerCurvature p) * (blockLength p : ℝ) =
      32768 * (curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6) *
        repetitions p * Real.sqrt (blockLength p) * p.ε ^ 2 := by
  have hn : (blockLength p : ℝ) ≠ 0 := by exact_mod_cast (blockLength_pos p).ne'
  unfold radius threshold lowerCurvature curvatureScale
  field_simp
  ring_nf
  rw [Real.sq_sqrt (Nat.cast_nonneg (blockLength p))]
  ring

lemma log_one_add_square_le (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x ^ 2) ≤ 2 * x := by
  have hm := Real.log_le_log (by positivity : 0 < 1 + x ^ 2)
    (show 1 + x ^ 2 ≤ (1 + x) ^ 2 by nlinarith)
  rw [Real.log_pow] at hm
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + x)
  norm_num at hm
  linarith

lemma normalized_noise (n c ε E ℓ : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2 ^ 28)
    (heq : E * n = 1024 * c * ε) (hlog : ℓ ≤ 2 * n ^ 2) : E ^ 2 * ℓ ≤ ε ^ 2 / 64 := by
  have hsq := pow_le_pow_left₀ hc0 hc 2
  have hp := mul_le_mul_of_nonneg_right hsq (sq_nonneg ε)
  calc
    _ ≤ E ^ 2 * (2 * n ^ 2) := mul_le_mul_of_nonneg_left hlog (sq_nonneg E)
    _ = 2 * (1024 * c * ε) ^ 2 := by rw [← heq]; ring
    _ ≤ _ := by norm_num at hp ⊢; nlinarith only [hp, sq_nonneg ε]

lemma normalized_total_error (n m c ε E J : ℝ) (hn : 0 < n) (hc0 : 0 ≤ c)
    (hc : c ≤ 1 / 2 ^ 28) (hm : m * Real.sqrt n ≤ 5 * n) (hm2 : m ≤ n ^ 2)
    (heq : E * n = 1024 * c * ε)
    (hJ : J * n = 32768 * c * m * Real.sqrt n * ε ^ 2) :
    4 * Real.sqrt n * ε * m * E + m * E ^ 2 + J ≤ ε ^ 2 / 1024 := by
  have hfirst : 4 * Real.sqrt n * ε * m * E ≤ 20480 * c * ε ^ 2 := by
    apply (mul_le_mul_iff_left₀ hn).mp
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ 4096 * c * ε ^ 2 by positivity)
    have he := congrArg (fun x : ℝ => 4 * Real.sqrt n * ε * m * x) heq
    nlinarith only [hh, he]
  have hsecond : m * E ^ 2 ≤ 1048576 * c ^ 2 * ε ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hm2 (sq_nonneg E)
    have he := congrArg (fun x : ℝ => x ^ 2) heq
    nlinarith only [hh, he]
  have hthird : J ≤ 163840 * c * ε ^ 2 := by
    apply (mul_le_mul_iff_left₀ hn).mp
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ 32768 * c * ε ^ 2 by positivity)
    nlinarith only [hh, hJ]
  have hs := pow_le_pow_left₀ hc0 hc 2
  have hlin := mul_le_mul_of_nonneg_right hc (sq_nonneg ε)
  have hquad := mul_le_mul_of_nonneg_right hs (sq_nonneg ε)
  norm_num at hlin hquad ⊢
  nlinarith only [hfirst, hsecond, hthird, hlin, hquad, sq_nonneg ε]

open OracleTemplate.ScheduleBlock LongTails.Proofs.RecoveryFractalSchedule

lemma completed_error_conditions (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hε : 0 ≤ p.ε) (hk : 2 ≤ level p) :
    errorBound p ^ 2 * Real.log (1 + p.L * ssum (fractalStep p) (epochLength p)) ≤ p.ε ^ 2 / 64 ∧
    (4 * threshold p * ssum (fractalStep p) (epochLength p) * errorBound p +
      ssum (fractalStep p) (epochLength p) * errorBound p ^ 2 + p.ρ * radius p ^ 3 ≤
      p.ε ^ 2 / (1024 * lowerCurvature p)) := by
  let c := curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6
  have hc0 : 0 ≤ c := by dsimp [c, curvatureScale]; positivity
  have hc : c ≤ 1 / 2 ^ 28 := by
    have hh := (selected_level_admissible p hk).2.2.1
    simpa only [c, repetitions, blockLength, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow] using hh
  have hn : 0 < (blockLength p : ℝ) := by exact_mod_cast blockLength_pos p
  have hμ := lowerCurvature_pos p hL
  have hG : 0 ≤ threshold p := by unfold threshold; positivity
  have hB : 0 ≤ errorBound p := by unfold errorBound radius; positivity
  have hS := (epoch_sum_bounds p hL hk).2
  have hS0 : 0 ≤ ssum (fractalStep p) (epochLength p) :=
    Finset.sum_nonneg fun i _ => (fractalStep_pos p hL hk i).le
  have hSμ : ssum (fractalStep p) (epochLength p) * lowerCurvature p ≤ repetitions p :=
    (le_div_iff₀ hμ).mp hS
  have hLS : p.L * ssum (fractalStep p) (epochLength p) ≤ ((blockLength p : ℝ) ^ 2) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hS hL.le
    have heq : p.L * ((repetitions p : ℝ) / lowerCurvature p) =
        repetitions p * (blockLength p : ℝ) ^ 2 := by
      unfold lowerCurvature
      field_simp
    rw [heq] at hh
    have hm := mul_le_mul_of_nonneg_right (repetitions_le_block_square p hk) (sq_nonneg (blockLength p : ℝ))
    nlinarith only [hh, hm]
  have hlog : Real.log (1 + p.L * ssum (fractalStep p) (epochLength p)) ≤ 2 * (blockLength p : ℝ) ^ 2 :=
    (Real.log_le_log (by positivity) (by linarith only [hLS])).trans
      (log_one_add_square_le ((blockLength p : ℝ) ^ 2) (sq_nonneg _))
  refine ⟨normalized_noise (blockLength p) c p.ε (errorBound p) _ hc0 hc
    (error_normalization p hL) hlog, ?_⟩
  have hm : (repetitions p : ℝ) * Real.sqrt (blockLength p) ≤ 5 * blockLength p := by
    have hh := mul_le_mul_of_nonneg_right (repetitions_le_sqrt p hk) (Real.sqrt_nonneg (blockLength p))
    have hs := Real.sq_sqrt hn.le
    nlinarith only [hh, hs]
  have hnrm := normalized_total_error (blockLength p) (repetitions p) c p.ε (errorBound p)
    (p.ρ * radius p ^ 3 * lowerCurvature p) hn hc0 hc hm (repetitions_le_block_square p hk)
    (error_normalization p hL) (cubic_normalization p hL)
  have hfirst := mul_le_mul_of_nonneg_left hSμ (show 0 ≤ 4 * threshold p * errorBound p by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hSμ (sq_nonneg (errorBound p))
  rw [div_mul_eq_div_div]
  apply (le_div_iff₀ hμ).mpr
  dsimp only [threshold] at hfirst ⊢
  nlinarith only [hnrm, hfirst, hsecond]

lemma recovery_target_identity (p : Params) (hL : 0 < p.L) :
    let c := curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6
    recoveryTarget p = 16 * epochLength p * threshold p ^ 2 +
      262144 * c * repetitions p * (blockLength p : ℝ) ^ 2 * Real.sqrt (blockLength p) * p.ε ^ 2 +
      8388608 * c ^ 2 * repetitions p * p.ε ^ 2 +
      131072 * c * repetitions p * blockLength p * Real.sqrt (blockLength p) * p.ε ^ 2 := by
  have hn : (blockLength p : ℝ) ≠ 0 := by exact_mod_cast (blockLength_pos p).ne'
  dsimp only
  unfold recoveryTarget prefixIncrease errorBound radius threshold lowerCurvature curvatureScale epochLength
  push_cast
  simp only [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg (blockLength p))]
  field_simp
  ring_nf
  linear_combination
    ((repetitions p : ℝ) ^ 3 * p.ε ^ 3 * (blockLength p : ℝ) ^ 4 * p.ρ * p.L ^ 2 *
      Real.sqrt (blockLength p) * 131072) * Real.sq_sqrt (Nat.cast_nonneg (blockLength p))

lemma normalized_recovery_target (n m c ε : ℝ) (hn : 4 ≤ n) (hm : 0 ≤ m)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    262144 * c * m * n ^ 2 * Real.sqrt n * ε ^ 2 +
      8388608 * c ^ 2 * m * ε ^ 2 + 131072 * c * m * n * Real.sqrt n * ε ^ 2 ≤
      1048576 * c * m * n ^ 2 * Real.sqrt n * ε ^ 2 := by
  have hn0 : 0 ≤ n := by linarith
  have hs : 2 ≤ Real.sqrt n := by nlinarith [Real.sq_sqrt hn0, Real.sqrt_nonneg n]
  have hn2 : 16 ≤ n ^ 2 := by nlinarith
  have hp := mul_le_mul hn2 hs (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg n)
  have hnn : n ≤ n ^ 2 := by nlinarith
  have hns := mul_le_mul_of_nonneg_right hnn (Real.sqrt_nonneg n)
  have hc : 262144 * n ^ 2 * Real.sqrt n + 8388608 * c + 131072 * n * Real.sqrt n ≤
      1048576 * n ^ 2 * Real.sqrt n := by nlinarith only [hp, hns, hc1]
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ c * m * ε ^ 2 by positivity)
  nlinarith only [hh]

noncomputable def recoveryOverhead (p : Params) : ℝ :=
  65536 * curvatureScale p * (repetitions p : ℝ) ^ 3 * (blockLength p : ℝ) ^ 7 * Real.sqrt (blockLength p)

noncomputable def recoveryLength (p : Params) : ℕ := epochLength p + ⌈recoveryOverhead p⌉₊ + 1

lemma recoveryLength_pos (p : Params) : 0 < recoveryLength p := by unfold recoveryLength; omega

lemma recoveryLength_lower (p : Params) :
    (epochLength p : ℝ) + recoveryOverhead p ≤ recoveryLength p := by
  have hh := Nat.le_ceil (recoveryOverhead p)
  unfold recoveryLength
  push_cast
  linarith

lemma recoveryLength_upper (p : Params) (hρ : 0 ≤ p.ρ) (hε : 0 ≤ p.ε) :
    (recoveryLength p : ℝ) ≤ epochLength p + recoveryOverhead p + 2 := by
  have hO : 0 ≤ recoveryOverhead p := by unfold recoveryOverhead curvatureScale; positivity
  have hh := Nat.ceil_lt_add_one hO
  unfold recoveryLength
  push_cast
  linarith

lemma recovery_target_budget (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hε : 0 ≤ p.ε) (hk : 2 ≤ level p) :
    recoveryTarget p ≤ 16 * recoveryLength p * threshold p ^ 2 := by
  let c := curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6
  have hc0 : 0 ≤ c := by dsimp [c, curvatureScale]; positivity
  have hc : c ≤ 1 / 2 ^ 28 := by
    have hh := (selected_level_admissible p hk).2.2.1
    simpa only [c, repetitions, blockLength, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow] using hh
  have hn : (4 : ℝ) ≤ blockLength p := by
    have hh : (4 : ℕ) ≤ 2 ^ level p := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ level p := Nat.pow_le_pow_right (by norm_num) hk
    exact_mod_cast hh
  have hb := normalized_recovery_target (blockLength p) (repetitions p) c p.ε hn
    (by positivity) hc0 (by norm_num at hc; linarith)
  have heq := recovery_target_identity p hL
  have hG : threshold p ^ 2 = (blockLength p : ℝ) * p.ε ^ 2 := by
    simp [threshold, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (blockLength p))]
  have hO : recoveryOverhead p = 65536 * c * repetitions p * blockLength p * Real.sqrt (blockLength p) := by
    dsimp [recoveryOverhead, c]
    ring
  have ht : recoveryTarget p ≤ 16 * ((epochLength p : ℝ) + recoveryOverhead p) * threshold p ^ 2 := by
    rw [heq, hG, hO]
    nlinarith only [hb]
  have hm := mul_le_mul_of_nonneg_right (recoveryLength_lower p) (show 0 ≤ 16 * threshold p ^ 2 by positivity)
  nlinarith only [ht, hm]

lemma normalized_recovery_length (n m c M : ℝ) (hn : 4 ≤ n) (hm : 1 ≤ m)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2 ^ 28)
    (hM : M ≤ n * m + 65536 * c * m * n * Real.sqrt n + 2) : M ≤ 4 * m * n ^ 2 := by
  have hn0 : 0 ≤ n := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hs : Real.sqrt n ≤ n := by nlinarith [Real.sq_sqrt hn0, Real.sqrt_nonneg n]
  have hcoef : 65536 * c ≤ 1 := by norm_num at hc; linarith
  have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 65536 * c * m * n by positivity)
  have h2 := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ m * n ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left (show n ≤ n ^ 2 by nlinarith) hm0
  have h4 := mul_le_mul hm (show 1 ≤ n ^ 2 by nlinarith) (by norm_num : (0 : ℝ) ≤ 1) hm0
  nlinarith only [hM, h1, h2, h3, h4]

lemma blockLength_four_le (p : Params) (hk : 2 ≤ level p) : (4 : ℝ) ≤ blockLength p := by
  have hh : (4 : ℕ) ≤ 2 ^ level p := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ level p := Nat.pow_le_pow_right (by norm_num) hk
  exact_mod_cast hh

lemma selected_smoothness_cap (p : Params) (hk : 2 ≤ level p) :
    curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6 ≤ 1 / 2 ^ 28 := by
  have hh := (selected_level_admissible p hk).2.2.1
  simpa only [repetitions, blockLength, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow] using hh

lemma recoveryLength_radius_bound (p : Params) (hρ : 0 ≤ p.ρ) (hε : 0 ≤ p.ε)
    (hk : 2 ≤ level p) : (recoveryLength p : ℝ) ≤ 4 * repetitions p * (blockLength p : ℝ) ^ 2 := by
  let c := curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6
  have hc0 : 0 ≤ c := by dsimp [c, curvatureScale]; positivity
  have hO : recoveryOverhead p = 65536 * c * repetitions p * blockLength p * Real.sqrt (blockLength p) := by
    dsimp [recoveryOverhead, c]
    ring
  have hM := recoveryLength_upper p hρ hε
  rw [hO] at hM
  unfold epochLength at hM
  push_cast at hM
  exact normalized_recovery_length (blockLength p) (repetitions p) c (recoveryLength p)
    (blockLength_four_le p hk) (by
      unfold repetitions
      push_cast
      have hh : 0 ≤ (level p : ℝ) := by positivity
      linarith) hc0
    (selected_smoothness_cap p hk) hM

lemma recovery_parameter_conditions (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hε : 0 ≤ p.ε) (hk : 2 ≤ level p) :
    recoveryTarget p ≤ 16 * recoveryLength p * threshold p ^ 2 ∧
    4 * recoveryLength p * threshold p / p.L ≤ radius p / 2 ∧
    errorBound p ≤ threshold p / 2 ∧
    errorBound p ^ 2 * Real.log (1 + (recoveryLength p : ℝ)) ≤ threshold p ^ 2 := by
  have hn := blockLength_four_le p hk
  have hμ := lowerCurvature_pos p hL
  have hG : 0 ≤ threshold p := by unfold threshold; positivity
  have hGsq : threshold p ^ 2 = (blockLength p : ℝ) * p.ε ^ 2 := by
    simp [threshold, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (blockLength p))]
  have hpow := mul_le_mul_of_nonneg_right hn (sq_nonneg p.ε)
  have hGe : p.ε ≤ threshold p := by nlinarith only [hGsq, hpow, hG, hε]
  have hM := recoveryLength_radius_bound p hρ hε hk
  have htravel : 4 * recoveryLength p * threshold p / p.L ≤ radius p / 2 := by
    have hh := mul_le_mul_of_nonneg_right hM (show 0 ≤ 4 * threshold p / p.L by positivity)
    have heq : radius p / 2 = 16 * repetitions p * (blockLength p : ℝ) ^ 2 * threshold p / p.L := by
      unfold radius lowerCurvature
      field_simp
      ring
    rw [heq]
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith only [hh]
  have hE := (completed_small_conditions p hL hρ hε hk).1
  have hhalf : errorBound p ≤ threshold p / 2 := by linarith
  have hM4 : (recoveryLength p : ℝ) ≤ (2 * (blockLength p : ℝ) ^ 2) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (repetitions_le_block_square p hk)
      (show 0 ≤ 4 * (blockLength p : ℝ) ^ 2 by positivity)
    nlinarith only [hM, hh]
  have hlog : Real.log (1 + (recoveryLength p : ℝ)) ≤ 4 * (blockLength p : ℝ) ^ 2 := by
    have hh := (Real.log_le_log (by positivity : 0 < 1 + (recoveryLength p : ℝ))
      (show 1 + (recoveryLength p : ℝ) ≤ 1 + (2 * (blockLength p : ℝ) ^ 2) ^ 2 by linarith)).trans
      (log_one_add_square_le (2 * (blockLength p : ℝ) ^ 2) (by positivity))
    nlinarith only [hh]
  let c := curvatureScale p * (repetitions p : ℝ) ^ 2 * (blockLength p : ℝ) ^ 6
  have hc0 : 0 ≤ c := by dsimp [c, curvatureScale]; positivity
  have hnoise := normalized_noise (blockLength p) c p.ε (errorBound p)
    (Real.log (1 + (recoveryLength p : ℝ)) / 2) hc0 (selected_smoothness_cap p hk)
    (error_normalization p hL) (by linarith only [hlog])
  refine ⟨recovery_target_budget p hL hρ hε hk, htravel, hhalf, ?_⟩
  nlinarith only [hnoise, hGsq, hpow, sq_nonneg p.ε]

lemma recoveryOverhead_identity (p : Params) (hL : 0 < p.L) :
    recoveryOverhead p * threshold p ^ 2 =
      p.L * (64 * epochLength p * threshold p * errorBound p / lowerCurvature p) := by
  have hn : (blockLength p : ℝ) ≠ 0 := by exact_mod_cast (blockLength_pos p).ne'
  unfold recoveryOverhead errorBound radius threshold lowerCurvature curvatureScale epochLength
  push_cast
  simp only [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg (blockLength p))]
  field_simp
  ring

lemma recoveryOverhead_paid (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hε : 0 ≤ p.ε) :
    recoveryOverhead p * threshold p ^ 2 ≤ p.L * prefixIncrease p := by
  rw [recoveryOverhead_identity p hL]
  have hμ := lowerCurvature_pos p hL
  have hG : 0 ≤ threshold p := by unfold threshold; positivity
  have hR : 0 ≤ radius p := by unfold radius; positivity
  have h2 : 0 ≤ 2 * repetitions p * errorBound p ^ 2 / lowerCurvature p := by positivity
  have h3 : 0 ≤ p.ρ * radius p ^ 3 := by positivity
  unfold prefixIncrease
  nlinarith [mul_nonneg hL.le h2, mul_nonneg hL.le h3]

lemma abort_group_cost (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hε : 0 ≤ p.ε)
    (t r : ℕ) (ht : t ≤ 2 * epochLength p) (hr : r ≤ recoveryLength p) :
    ((t + r : ℕ) : ℝ) * threshold p ^ 2 / p.L ≤
      prefixIncrease p + 8 * epochLength p * threshold p ^ 2 / p.L := by
  have hN : (1 : ℝ) ≤ epochLength p := by
    have hh : 0 < epochLength p := by
      unfold epochLength repetitions
      exact Nat.mul_pos (blockLength_pos p) (by omega)
    exact_mod_cast hh
  have ht' : (t : ℝ) ≤ 2 * epochLength p := by exact_mod_cast ht
  have hr' : (r : ℝ) ≤ recoveryLength p := by exact_mod_cast hr
  have hM := recoveryLength_upper p hρ hε
  have hcount : ((t + r : ℕ) : ℝ) ≤ 8 * epochLength p + recoveryOverhead p := by
    push_cast
    linarith
  have hh := mul_le_mul_of_nonneg_right hcount (sq_nonneg (threshold p))
  have hp := recoveryOverhead_paid p hL hρ hε
  apply (div_le_iff₀ hL).mpr
  have heq : (prefixIncrease p + 8 * epochLength p * threshold p ^ 2 / p.L) * p.L =
      prefixIncrease p * p.L + 8 * epochLength p * threshold p ^ 2 := by field_simp
  rw [heq]
  nlinarith only [hh, hp]

end LongTails.Proofs.RecoveryFractalTuning
