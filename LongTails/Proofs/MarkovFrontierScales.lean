import LongTails.Setups.HighDimensionalMarkovSmoothNonconvex
import LongTails.Proofs.AbcLowerAssembly
import LongTails.Proofs.CountdownCalibration

namespace LongTails.Proofs.MarkovFrontierScales

open LongTails.Setups.MarkovSmoothNonconvex
open LongTails.Setups.HighDimensionalMarkovSmoothNonconvex (Valid)
open AbcLowerParameters AbcLowerAssembly
open OracleTemplate.CountdownMarkov

noncomputable def chainParams (p : Params) : Setups.HighDimensionalAbcNoiseNonconvex.Params :=
  ⟨p.d, p.L, 0, 0, 0, p.Δ, p.ε, p.x0⟩

noncomputable def rareMass (p : Params) : ℝ := (2048 * p.ε / p.σ) ^ 2 * 2

noncomputable def halfLength (p : Params) : ℕ :=
  ⌊p.τ * Real.log (1 / rareMass p) / 4⌋₊

noncomputable def lowerCalls (p : Params) : ℕ :=
  ⌊p.τ * p.L * p.Δ * p.σ ^ 2 * Real.log (p.σ / p.ε) / (2 ^ 65 * p.ε ^ 4)⌋₊

variable {p : Params}

lemma ratio_large (hv : Valid p) : 2 ^ 16 ≤ p.σ / p.ε :=
  (le_div_iff₀ hv.2.1).mpr hv.2.2.2.2.1

lemma chain_valid (hv : Valid p) : Setups.HighDimensionalAbcNoiseNonconvex.spec.valid (chainParams p) := by
  have hr : 1 ≤ p.σ / p.ε := by linarith [ratio_large hv]
  have ht : 0 ≤ p.τ := by linarith [hv.2.2.1]
  have hl := Real.log_nonneg hr
  refine ⟨hv.1, le_rfl, le_rfl, le_rfl, hv.2.1, hv.2.2.2.1, ?_⟩
  simp only [chainParams, zero_mul, zero_div, add_zero, mul_one]
  refine le_trans ?_ hv.2.2.2.2.2
  have hw := mul_nonneg (mul_nonneg ht (sq_nonneg (p.σ / p.ε))) hl
  exact le_mul_of_one_le_right (by positivity) (by linarith)

lemma mass_eq (hv : Valid p) : rareMass p = 2 ^ 23 / (p.σ / p.ε) ^ 2 := by
  have he := hv.2.1.ne'
  have hs : 0 < p.σ := by linarith [hv.2.1, hv.2.2.2.2.1]
  unfold rareMass
  field_simp
  ring

lemma mass_bounds (hv : Valid p) : 0 < rareMass p ∧ rareMass p ≤ 1 / 32 := by
  have hr := ratio_large hv
  rw [mass_eq hv]
  have h : 0 < p.σ / p.ε := by linarith
  constructor
  · positivity
  · apply (div_le_iff₀ (sq_pos_of_pos h)).mpr
    nlinarith [sq_nonneg (p.σ / p.ε - 2 ^ 16)]

lemma log_mass (hv : Valid p) :
    Real.log (1 / rareMass p) = 2 * Real.log (p.σ / p.ε) - 23 * Real.log 2 := by
  have hr : 0 < p.σ / p.ε := by linarith [ratio_large hv]
  rw [one_div, Real.log_inv, mass_eq hv, Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

lemma half_bounds (hv : Valid p) :
    0 < halfLength p ∧ p.τ * Real.log (p.σ / p.ε) / 32 ≤ halfLength p ∧
      2 * (halfLength p : ℝ) ≤ p.τ * (Real.log (1 / rareMass p) / 2) := by
  have hr := ratio_large hv
  have ht := hv.2.2.1
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 16) hr
  rw [Real.log_pow] at hl
  norm_num at hl
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by norm_num)
    rw [Real.log_inv] at h
    norm_num at h ⊢
    linarith
  have hm := log_mass hv
  have hraw : 0 < p.τ * Real.log (1 / rareMass p) / 4 := by
    have : 0 < Real.log (1 / rareMass p) := by linarith
    positivity
  have hlog : Real.log (1 / rareMass p) ≥ Real.log (p.σ / p.ε) / 4 := by linarith
  have hu := Nat.floor_le hraw.le
  by_cases hh : 1 ≤ p.τ * Real.log (1 / rareMass p) / 4
  · have hlower := (Nat.div_two_lt_floor hh).le
    exact ⟨Nat.floor_pos.mpr hh, by unfold halfLength; nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ p.τ)], by unfold halfLength; linarith⟩
  · exfalso
    linarith [mul_le_mul_of_nonneg_right ht (by linarith : 0 ≤ Real.log (1 / rareMass p))]

lemma dimension_available (hv : Valid p) (N : ℕ) (hN : N ≤ lowerCalls p) :
    let T : ℝ := chainLength (chainParams p)
    T + 2 ^ 31 * ((N : ℝ) + 1) * T ^ 3 ≤ p.d := by
  intro T
  let D := p.L * p.Δ / p.ε ^ 2
  let r := p.σ / p.ε
  let w := p.τ * r ^ 2 * Real.log r
  have ht : 0 ≤ p.τ := by linarith [hv.2.2.1]
  have hr : 1 ≤ r := by have := ratio_large hv; dsimp [r]; linarith
  have hw : 0 ≤ w := mul_nonneg (mul_nonneg ht (sq_nonneg _)) (Real.log_nonneg hr)
  have hprod : 0 ≤ p.L * p.Δ := (by positivity : 0 ≤ 2 ^ 26 * p.ε ^ 2).trans hv.2.2.2.1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hT : T ≤ D := by
    have hh := chainLength_le _ (chain_valid hv)
    change T ≤ p.L * p.Δ / (11059200 * p.ε ^ 2) at hh
    have eq : p.L * p.Δ / (11059200 * p.ε ^ 2) = D / 11059200 := by dsimp [D]; ring
    rw [eq] at hh
    linarith
  have eq : lowerCalls p = ⌊D*w / 2^65⌋₊ := by unfold lowerCalls; congr 1; dsimp [D,w,r]; ring
  rw [eq] at hN
  have hn := (Nat.cast_le (α := ℝ)).mpr hN |>.trans (Nat.floor_le (by positivity))
  have ht0 : 0 ≤ T := Nat.cast_nonneg _
  have h1 : (N : ℝ)+1 ≤ (1+D)*(1+w) := by nlinarith [mul_nonneg hD hw]
  have h2 : T^3 ≤ (1+D)^3 := by gcongr; linarith
  have h3 : T ≤ (1+D)^4*(1+w) := by
    calc T ≤ 1+D := by linarith
         _ ≤ (1+D)^4 := by simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 1+D) (by decide : 1 ≤ 4)
         _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)
  have h4 := mul_le_mul h1 h2 (pow_nonneg ht0 _) (by positivity)
  change _ ≤ (p.d : ℝ)
  apply le_trans _ hv.2.2.2.2.2
  change T + _ ≤ 2^40*(1+D)^4*(1+w)
  nlinarith [mul_nonneg (by positivity : 0 ≤ (1+D)^4) (by linarith : 0 ≤ 1+w)]

lemma nonempty_regime : ∃ p, Valid p ∧ 1 ≤ lowerCalls p := by
  let e : ℝ := 1 / 2^16
  let d := ⌈2^40 * (1 + 1/e^2)^4 * (1 + (1/e)^2 * Real.log (1/e))⌉₊
  let p : Params := ⟨d, 1, 1, 1, 1, e, 0⟩
  refine ⟨p, ?_, ?_⟩
  · refine ⟨by norm_num [p], by norm_num [p,e], le_rfl, by norm_num [p,e], by norm_num [p,e], ?_⟩
    simpa only [p, one_mul] using (Nat.le_ceil (2^40*(1+1/e^2)^4*(1+(1/e)^2*Real.log (1/e))))
  · apply Nat.floor_pos.mpr
    have hl := Real.log_le_sub_one_of_pos (show 0 < (2:ℝ)⁻¹ by norm_num)
    rw [Real.log_inv] at hl
    have he : 1/e = 2^16 := by norm_num [e]
    change (1:ℝ) ≤ 1*1*1*1^2*Real.log (1/e) / (2^65*e^4)
    rw [he, Real.log_pow]
    norm_num [e] at hl ⊢
    linarith

lemma few_entries (hv : Valid p) (b : ℕ) (hb : b ≤ lowerCalls p) :
    1 + (b : ℝ) * (2 * rareMass p / (halfLength p + halfLength p : ℕ)) ≤
      chainLength (chainParams p) / (3 : ℝ) := by
  have he := hv.2.1
  have hL := hv.1
  have ht := hv.2.2.1
  have hprod : 0 ≤ p.L * p.Δ := (by positivity : 0 ≤ 2 ^ 26 * p.ε ^ 2).trans hv.2.2.2.1
  let r := p.σ / p.ε
  let D := p.L * p.Δ / p.ε ^ 2
  have hr : 1 < r := by have := ratio_large hv; dsimp [r]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg : 0 < Real.log r := Real.log_pos hr
  let l := chainLength (chainParams p)
  have hl : (6 : ℝ) ≤ l := by exact_mod_cast chainLength_ge _ (chain_valid hv)
  have hlen : D ≤ 22118400 * (l : ℝ) := by
    have h := chainLength_lower _ (chain_valid hv)
    change p.L * p.Δ / (22118400 * p.ε ^ 2) ≤ l at h
    dsimp [D]
    linarith [show p.L * p.Δ / p.ε ^ 2 = 22118400 * (p.L * p.Δ / (22118400 * p.ε ^ 2)) by ring]
  have hraw : p.τ * p.L * p.Δ * p.σ ^ 2 * Real.log (p.σ / p.ε) / (2 ^ 65 * p.ε ^ 4) =
      D * r ^ 2 * (p.τ * Real.log r) / 2 ^ 65 := by dsimp [D, r]; ring
  have hbudget : (b : ℝ) ≤ D * r ^ 2 * (p.τ * Real.log r) / 2 ^ 65 := by
    have hb' : b ≤ ⌊D * r ^ 2 * (p.τ * Real.log r) / 2 ^ 65⌋₊ := by
      simpa only [lowerCalls, hraw] using hb
    exact (Nat.cast_le.mpr hb').trans (Nat.floor_le (by positivity))
  have hm : rareMass p = 2 ^ 23 / r ^ 2 := mass_eq hv
  have hqpos := (mass_bounds hv).1
  have hhalf := half_bounds hv
  have hH : 0 < ((halfLength p + halfLength p : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < halfLength p + halfLength p)
  have hu : p.τ * Real.log r ≤ 16 * ((halfLength p + halfLength p : ℕ) : ℝ) := by
    dsimp only [r]
    push_cast
    linarith [hhalf.2.1]
  have hrate : D * r ^ 2 * (p.τ * Real.log r) / 2 ^ 65 * (2 * rareMass p) =
      D * (p.τ * Real.log r) / 2 ^ 41 := by
    rw [hm]
    field_simp [show r ≠ 0 by linarith]
  have hm1 := mul_le_mul_of_nonneg_right hbudget (by positivity : 0 ≤ 2 * rareMass p)
  rw [hrate] at hm1
  have hm2 := mul_le_mul_of_nonneg_left hu hD
  have hT : (b : ℝ) * (2 * rareMass p / ((halfLength p + halfLength p : ℕ) : ℝ)) ≤ D / 2 ^ 37 := by
    rw [← mul_div_assoc, div_le_iff₀ hH]
    linarith
  change _ ≤ (l : ℝ) / 3
  linarith

end LongTails.Proofs.MarkovFrontierScales
