import LongTails.Proofs.HeavyTailedHighProbabilityConstants

namespace LongTails.Proofs.HeavyTailedHighProbabilityBudget

open LongTails.Algorithms.HighProbabilityStationarity
open LongTails.Algorithms.HeavyTailedHighProbabilityStationarity
open LongTails.Setups.HeavyTailedHighProbabilityStationarity
open LongTails.Proofs.HighProbabilityConstants LongTails.Proofs.HeavyTailedHighProbabilityConstants

variable {q : Params} (hv : spec.valid q)
include hv

omit hv in
lemma rounds_succ_pos : (0 : ℝ) < (rounds (varianceParams q) : ℝ) + 1 := by positivity

lemma testSize_le :
    (testSize q : ℝ) ≤ 2 ^ 26 * (noiseScale (varianceParams q) ^ 2 / q.ε ^ 2) *
      ((rounds (varianceParams q) : ℝ) + 1) ^ (2 + (2 - q.p) / q.p) + 1 := by
  have hε := hv.2.2.2.2.2.1
  set R : ℝ := (rounds (varianceParams q) : ℝ) + 1 with hR
  have hR0 : 0 < R := rounds_succ_pos (q := q)
  have hS := noise_pos (varianceParams_valid hv)
  have hacc : accuracy (varianceParams q) = q.ε / (64 * R) := rfl
  have hval : 2 ^ 14 * noiseScale (varianceParams q) ^ 2 * R ^ ((2 - q.p) / q.p) /
      accuracy (varianceParams q) ^ 2 =
      2 ^ 26 * (noiseScale (varianceParams q) ^ 2 / q.ε ^ 2) * R ^ (2 + (2 - q.p) / q.p) := by
    rw [hacc, Real.rpow_add hR0, Real.rpow_two]
    field_simp
    ring
  have hnn : 0 ≤ 2 ^ 14 * noiseScale (varianceParams q) ^ 2 * R ^ ((2 - q.p) / q.p) /
      accuracy (varianceParams q) ^ 2 := by
    have := Real.rpow_nonneg hR0.le ((2 - q.p) / q.p)
    positivity
  have h := Nat.ceil_lt_add_one hnn
  have hdef : (testSize q : ℝ) = (⌈2 ^ 14 * noiseScale (varianceParams q) ^ 2 *
      R ^ ((2 - q.p) / q.p) / accuracy (varianceParams q) ^ 2⌉₊ : ℝ) := rfl
  rw [hdef]
  linarith

lemma phase_two_le :
    (8 * ((4 + testSize q : ℕ) : ℝ) * 2 ^ rounds (varianceParams q)) *
      ((rounds (varianceParams q) : ℝ) + 1) ≤
      2 ^ 54 * ((1 + effectiveSigma q ^ 2 / q.ε ^ 2) * Real.log (16 / q.δ) *
        Real.log (2 + Real.log (16 / q.δ)) ^ (2 + 2 / q.p)) := by
  have hv' := varianceParams_valid hv
  have hε := hv.2.2.2.2.2.1
  have hp := hv.2.1
  have hp2 := hv.2.2.1
  set R : ℝ := (rounds (varianceParams q) : ℝ) + 1 with hR
  have hR0 : 0 < R := rounds_succ_pos (q := q)
  have hR1 : 1 ≤ R := by have : (0 : ℝ) ≤ rounds (varianceParams q) := Nat.cast_nonneg _; linarith
  set ℓ := Real.log (16 / q.δ) with hℓ
  have hconf : confidence (varianceParams q) = ℓ := rfl
  have hl := confidence_ge hv'
  rw [hconf] at hl
  have hJ := rounds_pow_le hv'
  rw [hconf] at hJ
  have hrl := rounds_le_log hv'
  rw [hconf] at hrl
  have hT := testSize_le hv
  set ρ := 1 + effectiveSigma q ^ 2 / q.ε ^ 2 with hρ
  have hρ1 : 1 ≤ ρ := by
    have h0 : 0 ≤ effectiveSigma q ^ 2 / q.ε ^ 2 := by positivity
    linarith
  have hS2 : noiseScale (varianceParams q) ^ 2 / q.ε ^ 2 ≤ 2 * ρ := by
    have h1 : noiseScale (varianceParams q) ^ 2 ≤ 2 * (q.ε ^ 2 + effectiveSigma q ^ 2) := by
      change (effectiveSigma q + q.ε) ^ 2 ≤ _
      nlinarith [sq_nonneg (effectiveSigma q - q.ε)]
    calc noiseScale (varianceParams q) ^ 2 / q.ε ^ 2 ≤ 2 * (q.ε ^ 2 + effectiveSigma q ^ 2) / q.ε ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = 2 * ρ := by rw [hρ]; field_simp
  set γ : ℝ := 2 + (2 - q.p) / q.p with hγ
  have hγ0 : 0 ≤ γ := by
    have : 0 ≤ (2 - q.p) / q.p := div_nonneg (by linarith) (by linarith)
    linarith
  have hRγ1 : 1 ≤ R ^ γ := Real.one_le_rpow hR1 hγ0
  have hts : ((4 + testSize q : ℕ) : ℝ) ≤ 2 ^ 28 * ρ * R ^ γ := by
    push_cast
    have h1 : 2 ^ 26 * (noiseScale (varianceParams q) ^ 2 / q.ε ^ 2) * R ^ γ ≤
        2 ^ 27 * ρ * R ^ γ := by
      have := mul_le_mul_of_nonneg_right hS2 (show 0 ≤ 2 ^ 26 * R ^ γ by positivity)
      nlinarith
    have h2 : (5 : ℝ) ≤ 2 ^ 27 * ρ * R ^ γ := by
      have := mul_le_mul hρ1 hRγ1 zero_le_one (by linarith)
      nlinarith
    linarith
  have hexp : R ^ γ * R = R ^ (2 + 2 / q.p) := by
    rw [← Real.rpow_add_one hR0.ne']
    congr 1
    rw [hγ]
    field_simp
    ring
  have hlg0 : 0 ≤ Real.log (2 + ℓ) := Real.log_nonneg (by linarith)
  have hpow : R ^ (2 + 2 / q.p) ≤ 11 ^ 4 * Real.log (2 + ℓ) ^ (2 + 2 / q.p) := by
    have hq0 : 0 ≤ 2 + 2 / q.p := by positivity
    calc R ^ (2 + 2 / q.p) ≤ (11 * Real.log (2 + ℓ)) ^ (2 + 2 / q.p) :=
          Real.rpow_le_rpow hR0.le hrl hq0
      _ = (11 : ℝ) ^ (2 + 2 / q.p) * Real.log (2 + ℓ) ^ (2 + 2 / q.p) :=
          Real.mul_rpow (by norm_num) hlg0
      _ ≤ 11 ^ 4 * Real.log (2 + ℓ) ^ (2 + 2 / q.p) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hlg0 _)
          calc (11 : ℝ) ^ (2 + 2 / q.p) ≤ (11 : ℝ) ^ (4 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                  have : 2 / q.p ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
                  linarith)
            _ = 11 ^ 4 := by norm_num
  have hJ0 : (0 : ℝ) ≤ 2 ^ rounds (varianceParams q) := by positivity
  calc (8 * ((4 + testSize q : ℕ) : ℝ) * 2 ^ rounds (varianceParams q)) * R ≤
        8 * (2 ^ 28 * ρ * R ^ γ) * (2 ^ 8 * ℓ) * R := by gcongr
    _ = 2 ^ 39 * ρ * ℓ * (R ^ γ * R) := by ring
    _ = 2 ^ 39 * ρ * ℓ * R ^ (2 + 2 / q.p) := by rw [hexp]
    _ ≤ 2 ^ 39 * ρ * ℓ * (11 ^ 4 * Real.log (2 + ℓ) ^ (2 + 2 / q.p)) := by
        have : 0 ≤ 2 ^ 39 * ρ * ℓ := by positivity
        exact mul_le_mul_of_nonneg_left hpow this
    _ ≤ 2 ^ 54 * (ρ * ℓ * Real.log (2 + ℓ) ^ (2 + 2 / q.p)) := by
        have : 0 ≤ ρ * ℓ * Real.log (2 + ℓ) ^ (2 + 2 / q.p) := by
          have := Real.rpow_nonneg hlg0 (2 + 2 / q.p)
          positivity
        nlinarith

set_option maxHeartbeats 1000000 in
lemma plan_le_budgetH :
    (8 * (4 + testSize q) * 2 ^ rounds (varianceParams q)) * (rounds (varianceParams q) + 1) +
      (pilotSamples q + clipSize (varianceParams q)) * steps (varianceParams q) ≤
      ⌈2 ^ 76 * ((1 + (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1))) *
        (q.L * q.Δ / q.ε ^ 2 + Real.log (16 / q.δ) * Real.log (2 + Real.log (16 / q.δ)) ^ (2 + 2 / q.p)) +
          Real.sqrt (q.L * q.Δ) * Real.log (16 / q.δ) / q.ε)⌉₊ := by
  have hv' := varianceParams_valid hv
  have hε := hv.2.2.2.2.2.1
  have hp := hv.2.1
  have hp2 := hv.2.2.1
  have hL := hv.1
  have hΔ := hv.2.2.2.2.1
  set ℓ := Real.log (16 / q.δ) with hℓ
  have hl : 4 ≤ ℓ := confidence_ge hv'
  have h229 := plan_le_budget hv'
  have hP2 := phase_two_le hv
  rw [← hℓ] at hP2
  set s := (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1)) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) hv.2.2.2.1) hε.le) _
  have hσ' := effective_sq_le hv
  rw [← hs] at hσ'
  set ρ := 1 + effectiveSigma q ^ 2 / q.ε ^ 2 with hρ
  have hρ1 : 1 ≤ ρ := by
    have h0 : 0 ≤ effectiveSigma q ^ 2 / q.ε ^ 2 := by positivity
    linarith
  have hρs : ρ ≤ 2 * (1 + s) := by linarith
  have hA0 : 0 ≤ q.L * q.Δ / q.ε ^ 2 := div_nonneg (mul_nonneg hL.le hΔ) (sq_nonneg _)
  have hlg1 : 1 ≤ Real.log (2 + ℓ) := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hlg0 : 0 ≤ Real.log (2 + ℓ) := by linarith
  set lam3 := Real.log (2 + ℓ) ^ 3 with hlam3
  set lamp := Real.log (2 + ℓ) ^ (2 + 2 / q.p) with hlamp
  have h3p : lam3 ≤ lamp := by
    rw [hlam3, hlamp, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hlg1 ?_
    have : (1 : ℝ) ≤ 2 / q.p := by rw [le_div_iff₀ (by linarith)]; linarith
    push_cast
    linarith
  have hlamp1 : 1 ≤ lamp := Real.one_le_rpow hlg1 (by positivity)
  have hsqrt : 0 ≤ Real.sqrt (q.L * q.Δ) * ℓ / q.ε := by positivity
  set X229 := 2 ^ 71 * ((1 + (varianceParams q).σ ^ 2 / (varianceParams q).ε ^ 2) *
    ((varianceParams q).L * (varianceParams q).Δ / (varianceParams q).ε ^ 2 +
      Real.log (16 / (varianceParams q).δ) * Real.log (2 + Real.log (16 / (varianceParams q).δ)) ^ 3) +
    Real.sqrt ((varianceParams q).L * (varianceParams q).Δ) * Real.log (16 / (varianceParams q).δ) /
      (varianceParams q).ε) with hX
  have hXeq : X229 = 2 ^ 71 * (ρ * (q.L * q.Δ / q.ε ^ 2 + ℓ * lam3) + Real.sqrt (q.L * q.Δ) * ℓ / q.ε) :=
    rfl
  have hX0 : 0 ≤ X229 := by rw [hXeq]; positivity
  have hphase1 : (((pilotSize (varianceParams q) + clipSize (varianceParams q)) *
      steps (varianceParams q) : ℕ) : ℝ) ≤ X229 + 1 := by
    have h1 : (((pilotSize (varianceParams q) + clipSize (varianceParams q)) *
        steps (varianceParams q) : ℕ) : ℝ) ≤ ((⌈X229⌉₊ : ℕ) : ℝ) := by
      have : (pilotSize (varianceParams q) + clipSize (varianceParams q)) *
          steps (varianceParams q) ≤ ⌈X229⌉₊ := le_trans (Nat.le_add_left _ _) h229
      exact_mod_cast this
    exact h1.trans (Nat.ceil_lt_add_one hX0).le
  have hdbl : (((pilotSamples q + clipSize (varianceParams q)) * steps (varianceParams q) : ℕ) : ℝ) ≤
      2 * (X229 + 1) := by
    have : (pilotSamples q + clipSize (varianceParams q)) * steps (varianceParams q) ≤
        2 * ((pilotSize (varianceParams q) + clipSize (varianceParams q)) * steps (varianceParams q)) := by
      unfold pilotSamples; nlinarith
    have h : (((pilotSamples q + clipSize (varianceParams q)) * steps (varianceParams q) : ℕ) : ℝ) ≤
        2 * ((((pilotSize (varianceParams q) + clipSize (varianceParams q)) *
          steps (varianceParams q) : ℕ) : ℝ)) := by exact_mod_cast this
    linarith
  have hreal : (((8 * (4 + testSize q) * 2 ^ rounds (varianceParams q)) *
      (rounds (varianceParams q) + 1) +
      (pilotSamples q + clipSize (varianceParams q)) * steps (varianceParams q) : ℕ) : ℝ) ≤
      2 ^ 76 * ((1 + s) * (q.L * q.Δ / q.ε ^ 2 + ℓ * lamp) + Real.sqrt (q.L * q.Δ) * ℓ / q.ε) := by
    have hcast : (((8 * (4 + testSize q) * 2 ^ rounds (varianceParams q)) *
        (rounds (varianceParams q) + 1) : ℕ) : ℝ) =
        (8 * ((4 + testSize q : ℕ) : ℝ) * 2 ^ rounds (varianceParams q)) *
          ((rounds (varianceParams q) : ℝ) + 1) := by push_cast; ring
    rw [Nat.cast_add, hcast]
    rw [hXeq] at hdbl
    have hs1 : (0 : ℝ) ≤ 1 + s := by linarith
    have hl0 : (0 : ℝ) ≤ ℓ := by linarith
    have hlp0 : 0 ≤ ℓ * lamp := mul_nonneg hl0 (by linarith)
    have hl30 : 0 ≤ ℓ * lam3 := mul_nonneg hl0 (by rw [hlam3]; exact pow_nonneg hlg0 3)
    have hrholam : ρ * (q.L * q.Δ / q.ε ^ 2 + ℓ * lam3) ≤ 2 * (1 + s) * (q.L * q.Δ / q.ε ^ 2 + ℓ * lamp) := by
      have h1 : q.L * q.Δ / q.ε ^ 2 + ℓ * lam3 ≤ q.L * q.Δ / q.ε ^ 2 + ℓ * lamp := by
        have := mul_le_mul_of_nonneg_left h3p hl0
        linarith
      have h2 : 0 ≤ q.L * q.Δ / q.ε ^ 2 + ℓ * lam3 := add_nonneg hA0 hl30
      calc ρ * (q.L * q.Δ / q.ε ^ 2 + ℓ * lam3) ≤ (2 * (1 + s)) * (q.L * q.Δ / q.ε ^ 2 + ℓ * lam3) :=
            mul_le_mul_of_nonneg_right hρs h2
        _ ≤ 2 * (1 + s) * (q.L * q.Δ / q.ε ^ 2 + ℓ * lamp) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
    have hP2' : 2 ^ 54 * (ρ * ℓ * lamp) ≤ 2 ^ 55 * ((1 + s) * (ℓ * lamp)) := by
      have h := mul_le_mul_of_nonneg_right hρs hlp0
      calc 2 ^ 54 * (ρ * ℓ * lamp) = 2 ^ 54 * (ρ * (ℓ * lamp)) := by ring
        _ ≤ 2 ^ 54 * (2 * (1 + s) * (ℓ * lamp)) := mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 2 ^ 55 * ((1 + s) * (ℓ * lamp)) := by ring
    have h4 : (4 : ℝ) ≤ ℓ * lamp := by
      calc (4 : ℝ) = 4 * 1 := by norm_num
        _ ≤ ℓ * lamp := mul_le_mul hl hlamp1 (by norm_num) hl0
    have hone : (2 : ℝ) ≤ (1 + s) * (ℓ * lamp) := by
      have := le_mul_of_one_le_left hlp0 (show (1 : ℝ) ≤ 1 + s by linarith)
      linarith
    have hB0 : 0 ≤ (1 + s) * (q.L * q.Δ / q.ε ^ 2 + ℓ * lamp) := mul_nonneg hs1 (add_nonneg hA0 hlp0)
    have hsA : 0 ≤ (1 + s) * (q.L * q.Δ / q.ε ^ 2) := mul_nonneg hs1 hA0
    have hexp : (1 + s) * (q.L * q.Δ / q.ε ^ 2 + ℓ * lamp) =
        (1 + s) * (q.L * q.Δ / q.ε ^ 2) + (1 + s) * (ℓ * lamp) := by ring
    linarith
  exact_mod_cast hreal.trans (Nat.le_ceil _)

end LongTails.Proofs.HeavyTailedHighProbabilityBudget
