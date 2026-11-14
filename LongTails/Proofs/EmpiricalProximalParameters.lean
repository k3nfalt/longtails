import LongTails.Proofs.EmpiricalProximalInner

namespace LongTails.Proofs.EmpiricalProximalParameters

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthConvex
open LongTails.Algorithms.EmpiricalProximalAcceleration
open EmpiricalProximalInner

lemma batchSize_eq_min (p : Params) (hρ : 1 ≤ p.ρ) :
    batchSize p = min p.n ⌈1024 * p.ρ⌉₊ := by
  have hn : 1 ≤ p.n := NeZero.pos p.n
  have hc : 1 ≤ ⌈1024 * p.ρ⌉₊ := Nat.ceil_pos.mpr (by linarith)
  exact max_eq_right (le_min hn hc)

lemma batchSize_le_n (p : Params) (hρ : 1 ≤ p.ρ) : batchSize p ≤ p.n := by
  rw [batchSize_eq_min p hρ]
  exact min_le_left _ _

lemma batchSize_le_growth (p : Params) (hρ : 1 ≤ p.ρ) : (batchSize p : ℝ) ≤ 1025 * p.ρ := by
  have hnat : batchSize p ≤ ⌈1024 * p.ρ⌉₊ := by
    rw [batchSize_eq_min p hρ]
    exact min_le_right _ _
  have hcast : (batchSize p : ℝ) ≤ ⌈1024 * p.ρ⌉₊ := by exact_mod_cast hnat
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 1024 * p.ρ by linarith)
  linarith

lemma stochastic_batch_lower (p : Params) (hρ : 1 ≤ p.ρ) (h : batchSize p ≠ p.n) :
    1024 * p.ρ ≤ (batchSize p : ℝ) := by
  have he : batchSize p = ⌈1024 * p.ρ⌉₊ := by
    have hm := batchSize_eq_min p hρ
    omega
  rw [he]
  exact Nat.le_ceil _

lemma regularization_mul_size (p : Params) :
    regularization p * (batchSize p : ℝ) = 1024 * p.L := by
  have hb : (batchSize p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (batchSize p)
  unfold regularization
  field_simp

lemma condition_identity (p : Params) (hL : 0 < p.L) :
    1 + p.L / regularization p = 1 + (batchSize p : ℝ) / 1024 := by
  have hb : (batchSize p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (batchSize p)
  unfold regularization
  field_simp

lemma condition_ge_one (p : Params) (hL : 0 < p.L) : 1 ≤ 1 + p.L / regularization p := by
  have hμ := regularization_pos p hL
  have hn := div_nonneg hL.le hμ.le
  linarith

lemma condition_le_growth (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ) :
    1 + p.L / regularization p ≤ 3 * p.ρ := by
  rw [condition_identity p hL]
  have hb := batchSize_le_growth p hρ
  linarith

lemma stochastic_stability_size (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ)
    (h : batchSize p ≠ p.n) :
    18 * (p.L + regularization p) ≤ (batchSize p : ℝ) * regularization p := by
  have hb := stochastic_batch_lower p hρ h
  have hm := regularization_mul_size p
  have hμ := regularization_pos p hL
  have hμL : regularization p ≤ p.L := by nlinarith
  nlinarith

lemma tuning_eq_one (p : Params) (hL : 0 < p.L) (c : p.E) :
    Katyusha.tuning (innerParams p c) = 1 := by
  have hb : (batchSize p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (batchSize p)
  have he : p.L / (((2 * batchSize p : ℕ) : ℝ) * regularization p) = 1 / 2048 := by
    push_cast
    unfold regularization
    field_simp
    norm_num
  have hs : Real.sqrt (1 / 2048 : ℝ) ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hc : ⌈Real.sqrt (1 / 2048 : ℝ)⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using hs)
  unfold Katyusha.tuning
  change max 1 ⌈Real.sqrt (p.L / (((2 * batchSize p : ℕ) : ℝ) * regularization p))⌉₊ = 1
  rw [he]
  exact max_eq_left hc

lemma inner_log_bound (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ) :
    Nat.clog 2 ⌈14 * (2 ^ 20 * p.ρ * (1 + p.L / regularization p) ^ 4)⌉₊ ≤
      Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊ := by
  apply Nat.clog_mono_right
  apply Nat.ceil_mono
  have hk := condition_le_growth p hL hρ
  have hk0 : 0 ≤ 1 + p.L / regularization p := (by norm_num : (0 : ℝ) ≤ 1).trans (condition_ge_one p hL)
  calc
    14 * (2 ^ 20 * p.ρ * (1 + p.L / regularization p) ^ 4) ≤
        14 * (2 ^ 20 * p.ρ * (3 * p.ρ) ^ 4) := by gcongr
    _ = (14 * 2 ^ 20 * 81) * p.ρ ^ 5 := by ring
    _ ≤ 2 ^ 32 * p.ρ ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

lemma public_log_pos (p : Params) (hρ : 1 ≤ p.ρ) : 0 < Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊ := by
  have hp : (1 : ℝ) ≤ p.ρ ^ 5 := one_le_pow₀ hρ
  have hc0 : (2 : ℝ) ≤ 2 ^ 32 * p.ρ ^ 5 := by nlinarith only [hp]
  have hc : (2 : ℝ) ≤ (⌈2 ^ 32 * p.ρ ^ 5⌉₊ : ℝ) := hc0.trans (Nat.le_ceil _)
  have hn : 2 ≤ ⌈2 ^ 32 * p.ρ ^ 5⌉₊ := by exact_mod_cast hc
  have hh := Nat.le_pow_clog (by decide : 1 < 2) ⌈2 ^ 32 * p.ρ ^ 5⌉₊
  by_contra hz
  have he : Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊ = 0 := by omega
  rw [he] at hh
  simp only [pow_zero] at hh
  omega

lemma stepCost_bound (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ) :
    stepCost p ≤ 109 * batchSize p * Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊ := by
  have hlog := inner_log_bound p hL hρ
  have hp := public_log_pos p hρ
  have he : stepCost p = batchSize p + 108 * batchSize p *
      Nat.clog 2 ⌈14 * (2 ^ 20 * p.ρ * (1 + p.L / regularization p) ^ 4)⌉₊ := by
    unfold stepCost innerCost innerEpochs
    rw [tuning_eq_one p hL p.x0]
    ring
  rw [he]
  nlinarith [Nat.mul_le_mul_left (108 * batchSize p) hlog,
    Nat.mul_le_mul_left (batchSize p) (show 1 ≤ Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊ from hp)]

lemma outer_cost_bound (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε) :
    batchSize p * (1 + ⌈Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)⌉₊) ≤
      64 * (batchSize p + ⌈Real.sqrt ((batchSize p : ℝ) * p.L * p.R ^ 2 / p.ε)⌉₊) := by
  let b : ℝ := batchSize p
  let s := Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)
  let t := Real.sqrt (b * p.L * p.R ^ 2 / p.ε)
  have hb : 0 < b := by dsimp [b]; exact_mod_cast NeZero.pos (batchSize p)
  have hμ := regularization_pos p hL
  have hs : s ^ 2 = 4 * regularization p * p.R ^ 2 / p.ε := Real.sq_sqrt (by positivity)
  have ht : t ^ 2 = b * p.L * p.R ^ 2 / p.ε := Real.sq_sqrt (by positivity)
  have hid : b ^ 2 * (4 * regularization p * p.R ^ 2 / p.ε) =
      4096 * (b * p.L * p.R ^ 2 / p.ε) := by
    dsimp [b, regularization]
    field_simp
    ring
  have hsq : (b * s) ^ 2 = (64 * t) ^ 2 := by
    rw [mul_pow, hs, mul_pow, ht]
    norm_num
    exact hid
  have he : b * s = 64 * t := by
    have h₁ : 0 ≤ b * s := by dsimp [s]; positivity
    have h₂ : 0 ≤ 64 * t := by dsimp [t]; positivity
    nlinarith only [hsq, h₁, h₂]
  have hcs : (⌈s⌉₊ : ℝ) ≤ s + 1 := (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  have hct : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil _
  have hm := mul_le_mul_of_nonneg_left hcs hb.le
  have hreal : b * (1 + (⌈s⌉₊ : ℝ)) ≤ 64 * (b + (⌈t⌉₊ : ℝ)) := by
    nlinarith only [hm, he, hct, hb]
  dsimp only [b, s, t] at hreal
  exact_mod_cast hreal

lemma totalCost_bound (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ) (hε : 0 < p.ε) :
    stepCost p * (1 + ⌈Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)⌉₊) ≤
      7000 * (min p.n ⌈1024 * p.ρ⌉₊ +
        ⌈Real.sqrt (((min p.n ⌈1024 * p.ρ⌉₊ : ℕ) : ℝ) * p.L * p.R ^ 2 / p.ε)⌉₊) *
        Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊ := by
  have hs := stepCost_bound p hL hρ
  have ht := outer_cost_bound p hL hε
  rw [← batchSize_eq_min p hρ]
  calc
    _ ≤ (109 * batchSize p * Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊) *
        (1 + ⌈Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)⌉₊) := Nat.mul_le_mul_right _ hs
    _ = (109 * Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊) *
        (batchSize p * (1 + ⌈Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)⌉₊)) := by ring
    _ ≤ (109 * Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊) *
        (64 * (batchSize p + ⌈Real.sqrt ((batchSize p : ℝ) * p.L * p.R ^ 2 / p.ε)⌉₊)) :=
      Nat.mul_le_mul_left _ ht
    _ = 6976 * (batchSize p + ⌈Real.sqrt ((batchSize p : ℝ) * p.L * p.R ^ 2 / p.ε)⌉₊) *
        Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊ := by ring
    _ ≤ _ := by gcongr; norm_num

lemma accuracy_tuning (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε) :
    2 * regularization p * p.R ^ 2 /
      ((1 + ⌈Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)⌉₊ : ℕ) : ℝ) ^ 2 ≤ p.ε := by
  have hμ := regularization_pos p hL
  have hs := Nat.le_ceil (Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε))
  have hsq := Real.sq_sqrt (show 0 ≤ 4 * regularization p * p.R ^ 2 / p.ε by positivity)
  have hT : 0 < ((1 + ⌈Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)⌉₊ : ℕ) : ℝ) := by
    positivity
  apply (div_le_iff₀ (sq_pos_of_pos hT)).mpr
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [hsq] at hh
  have hm := (div_le_iff₀ hε).mp hh
  push_cast
  nlinarith [sq_nonneg p.R]

lemma outer_steps_eq (p : Params) (hρ : 1 ≤ p.ρ) :
    1 + ⌈Real.sqrt (4096 * p.L * p.R ^ 2 /
      (((min p.n ⌈1024 * p.ρ⌉₊ : ℕ) : ℝ) * p.ε))⌉₊ =
        1 + ⌈Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)⌉₊ := by
  rw [← batchSize_eq_min p hρ]
  congr 3
  unfold regularization
  ring

end LongTails.Proofs.EmpiricalProximalParameters
