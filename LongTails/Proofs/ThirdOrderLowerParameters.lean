import LongTails.Proofs.AbcLowerMeasure
import LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex

open scoped BigOperators

namespace LongTails.Proofs.ThirdOrderLowerParameters

open LongTails.Proofs.AbcHardOracle (Scale)
open LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex

noncomputable def complexity (q : Params) : ℝ :=
  min (q.L₁ / q.ε) (min (Real.sqrt (q.L₂ / q.ε)) ((q.L₃ / q.ε) ^ (1 / 3 : ℝ)))

noncomputable def lowerBudget (q : Params) : ℕ :=
  ⌊q.Δ * complexity q * (1 + q.σ ^ 2 / q.ε ^ 2) / (2 ^ 174 * q.ε)⌋₊

noncomputable def stepScale (q : Params) : ℝ :=
  max (2 ^ 58 * q.ε / q.L₁)
    (max (Real.sqrt (2 ^ 59 * q.ε / q.L₂)) ((2 ^ 63 * q.ε / q.L₃) ^ (1 / 3 : ℝ)))

noncomputable def amplitude (q : Params) : ℝ := 5 * q.ε * stepScale q

noncomputable def chainLength (q : Params) : ℕ := ⌊q.Δ / (20 * q.ε * stepScale q)⌋₊

noncomputable def secretScale (q : Params) : ℝ := (5 * 2 ^ 51 * q.ε) ^ 2

noncomputable def revealProb (q : Params) : ℝ := secretScale q / (secretScale q + q.σ ^ 2)

lemma cube_rpow {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma le_of_pow_le {y c : ℝ} (hc : 0 ≤ c) {k : ℕ} (hk : k ≠ 0) (h : y ^ k ≤ c ^ k) : y ≤ c := by
  by_contra hlt
  push Not at hlt
  exact absurd h (not_le.mpr (pow_lt_pow_left₀ hlt hc hk))

lemma stepScale_pos (q : Params) (hL : 0 < q.L₁) (hε : 0 < q.ε) : 0 < stepScale q :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

noncomputable def scaleOf (q : Params) (hL : 0 < q.L₁) (hε : 0 < q.ε) : Scale :=
  ⟨amplitude q, stepScale q, by have := stepScale_pos q hL hε; unfold amplitude; positivity,
    stepScale_pos q hL hε⟩

lemma amplitude_ratio (q : Params) (hL : 0 < q.L₁) (hε : 0 < q.ε) :
    amplitude q / stepScale q = 5 * q.ε := by
  have := stepScale_pos q hL hε
  unfold amplitude; field_simp

section Smoothness

variable (q : Params) (hL₁ : 0 < q.L₁) (hL₂ : 0 < q.L₂) (hL₃ : 0 < q.L₃) (hε : 0 < q.ε)
include hL₁ hε

lemma smooth_first : 2 ^ 55 * amplitude q / stepScale q ^ 2 ≤ q.L₁ := by
  have hl := stepScale_pos q hL₁ hε
  have h1 : 2 ^ 58 * q.ε / q.L₁ ≤ stepScale q := le_max_left _ _
  rw [div_le_iff₀ hL₁] at h1
  unfold amplitude
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h1 hl.le]

include hL₂ in
lemma smooth_second : 2 ^ 56 * amplitude q / stepScale q ^ 3 ≤ q.L₂ := by
  have hl := stepScale_pos q hL₁ hε
  have h1 : Real.sqrt (2 ^ 59 * q.ε / q.L₂) ≤ stepScale q :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h2 : 2 ^ 59 * q.ε / q.L₂ ≤ stepScale q ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (by positivity)] at this
  rw [div_le_iff₀ hL₂] at h2
  unfold amplitude
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h2 hl.le]

include hL₃ in
lemma smooth_third : 2 ^ 60 * amplitude q / stepScale q ^ 4 ≤ q.L₃ := by
  have hl := stepScale_pos q hL₁ hε
  have h1 : (2 ^ 63 * q.ε / q.L₃) ^ (1 / 3 : ℝ) ≤ stepScale q :=
    (le_max_right _ _).trans (le_max_right _ _)
  have h2 : 2 ^ 63 * q.ε / q.L₃ ≤ stepScale q ^ 3 := by
    have := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) h1 3
    rwa [cube_rpow (by positivity)] at this
  rw [div_le_iff₀ hL₃] at h2
  unfold amplitude
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h2 hl.le]

include hL₂ hL₃ in
lemma complexity_pos : 0 < complexity q := by
  unfold complexity
  exact lt_min (by positivity) (lt_min (Real.sqrt_pos.mpr (by positivity))
    (Real.rpow_pos_of_pos (by positivity) _))

include hL₂ hL₃ in
lemma stepScale_complexity_le : stepScale q * complexity q ≤ 2 ^ 58 := by
  have m1 : complexity q ≤ q.L₁ / q.ε := min_le_left _ _
  have m2 : complexity q ≤ Real.sqrt (q.L₂ / q.ε) := (min_le_left _ _).trans' (min_le_right _ _)
  have m3 : complexity q ≤ (q.L₃ / q.ε) ^ (1 / 3 : ℝ) := (min_le_right _ _).trans' (min_le_right _ _)
  unfold stepScale
  rcases max_choice (2 ^ 58 * q.ε / q.L₁)
    (max (Real.sqrt (2 ^ 59 * q.ε / q.L₂)) ((2 ^ 63 * q.ε / q.L₃) ^ (1 / 3 : ℝ))) with h | h
  · rw [h]
    calc _ ≤ 2 ^ 58 * q.ε / q.L₁ * (q.L₁ / q.ε) := mul_le_mul_of_nonneg_left m1 (by positivity)
      _ = 2 ^ 58 := by field_simp
  · rw [h]
    rcases max_choice (Real.sqrt (2 ^ 59 * q.ε / q.L₂)) ((2 ^ 63 * q.ε / q.L₃) ^ (1 / 3 : ℝ))
      with h' | h'
    · rw [h']
      refine (mul_le_mul_of_nonneg_left m2 (Real.sqrt_nonneg _)).trans ?_
      apply le_of_pow_le (by norm_num) two_ne_zero
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      have e : 2 ^ 59 * q.ε / q.L₂ * (q.L₂ / q.ε) = 2 ^ 59 := by field_simp
      rw [e]; norm_num
    · rw [h']
      refine (mul_le_mul_of_nonneg_left m3 (Real.rpow_nonneg (by positivity) _)).trans ?_
      apply le_of_pow_le (by norm_num) three_ne_zero
      rw [mul_pow, cube_rpow (by positivity), cube_rpow (by positivity)]
      have e : 2 ^ 63 * q.ε / q.L₃ * (q.L₃ / q.ε) = 2 ^ 63 := by field_simp
      rw [e]; norm_num

include hL₂ hL₃ in
lemma one_le_stepScale_complexity : 1 ≤ stepScale q * complexity q := by
  have s1 : 2 ^ 58 * q.ε / q.L₁ ≤ stepScale q := le_max_left _ _
  have s2 : Real.sqrt (2 ^ 59 * q.ε / q.L₂) ≤ stepScale q :=
    (le_max_left _ _).trans (le_max_right _ _)
  have s3 : (2 ^ 63 * q.ε / q.L₃) ^ (1 / 3 : ℝ) ≤ stepScale q :=
    (le_max_right _ _).trans (le_max_right _ _)
  unfold complexity
  rcases min_choice (q.L₁ / q.ε) (min (Real.sqrt (q.L₂ / q.ε)) ((q.L₃ / q.ε) ^ (1 / 3 : ℝ)))
    with h | h
  · rw [h]
    calc (1 : ℝ) ≤ 2 ^ 58 * q.ε / q.L₁ * (q.L₁ / q.ε) := by
          have e : 2 ^ 58 * q.ε / q.L₁ * (q.L₁ / q.ε) = 2 ^ 58 := by field_simp
          rw [e]; norm_num
      _ ≤ stepScale q * (q.L₁ / q.ε) := mul_le_mul_of_nonneg_right s1 (by positivity)
  · rw [h]
    rcases min_choice (Real.sqrt (q.L₂ / q.ε)) ((q.L₃ / q.ε) ^ (1 / 3 : ℝ)) with h' | h'
    · rw [h']
      refine le_trans ?_ (mul_le_mul_of_nonneg_right s2 (Real.sqrt_nonneg _))
      by_contra hc
      push Not at hc
      have hsq := pow_lt_one₀ (by positivity) hc two_ne_zero
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsq
      have e : 2 ^ 59 * q.ε / q.L₂ * (q.L₂ / q.ε) = 2 ^ 59 := by field_simp
      rw [e] at hsq
      norm_num at hsq
    · rw [h']
      refine le_trans ?_ (mul_le_mul_of_nonneg_right s3 (Real.rpow_nonneg (by positivity) _))
      by_contra hc
      push Not at hc
      have hsq := pow_lt_one₀ (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)) hc three_ne_zero
      rw [mul_pow, cube_rpow (by positivity), cube_rpow (by positivity)] at hsq
      have e : 2 ^ 63 * q.ε / q.L₃ * (q.L₃ / q.ε) = 2 ^ 63 := by field_simp
      rw [e] at hsq
      norm_num at hsq

end Smoothness

lemma secretScale_pos (q : Params) (hε : 0 < q.ε) : 0 < secretScale q := by
  unfold secretScale; positivity

lemma revealProb_pos (q : Params) (hε : 0 < q.ε) : 0 < revealProb q := by
  unfold revealProb
  exact div_pos (secretScale_pos q hε) (by have := secretScale_pos q hε; positivity)

lemma revealProb_le (q : Params) (hε : 0 < q.ε) : revealProb q ≤ 1 := by
  unfold revealProb
  rw [div_le_one (by have := secretScale_pos q hε; positivity)]
  nlinarith [sq_nonneg q.σ]

lemma variance_le (q : Params) (hε : 0 < q.ε) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s ≤ 5 * 2 ^ 51 * q.ε) : (1 / revealProb q - 1) * s ^ 2 ≤ q.σ ^ 2 := by
  have hc := secretScale_pos q hε
  have hinv : 1 / revealProb q - 1 = q.σ ^ 2 / secretScale q := by
    unfold revealProb
    rw [one_div, inv_div, add_div, div_self hc.ne']
    ring
  rw [hinv]
  have hs2 : s ^ 2 ≤ secretScale q := by
    unfold secretScale; exact pow_le_pow_left₀ hs0 hs 2
  calc _ ≤ q.σ ^ 2 / secretScale q * secretScale q :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
    _ = q.σ ^ 2 := div_mul_cancel₀ _ hc.ne'

lemma revealProb_noise (q : Params) (hε : 0 < q.ε) :
    revealProb q * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ 25 * 2 ^ 102 := by
  have hs : secretScale q = 25 * 2 ^ 102 * q.ε ^ 2 := by unfold secretScale; ring
  have h1 : 1 + q.σ ^ 2 / q.ε ^ 2 = (q.ε ^ 2 + q.σ ^ 2) / q.ε ^ 2 := by
    rw [add_div, div_self (by positivity)]
  unfold revealProb
  rw [hs, h1, div_mul_div_comm, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg q.σ, sq_nonneg q.ε, mul_nonneg (sq_nonneg q.σ) (sq_nonneg q.ε),
    mul_nonneg (sq_nonneg q.ε) (sq_nonneg q.ε)]

section Regime

variable (q : Params) (hv : spec.valid q)
include hv

lemma ratio_bounds :
    q.Δ * complexity q / (2 ^ 63 * q.ε) ≤ q.Δ / (20 * q.ε * stepScale q) ∧
      q.Δ / (20 * q.ε * stepScale q) ≤ q.Δ * complexity q / q.ε ∧ 0 ≤ q.Δ := by
  obtain ⟨hL₁, hL₂, hL₃, _, hε, hreg, _⟩ := hv
  have hl := stepScale_pos q hL₁ hε
  have hM := complexity_pos q hL₁ hL₂ hL₃ hε
  have hup := stepScale_complexity_le q hL₁ hL₂ hL₃ hε
  have hlo := one_le_stepScale_complexity q hL₁ hL₂ hL₃ hε
  have hΔ : 0 ≤ q.Δ := by
    have h1 : 0 ≤ q.Δ * complexity q := le_trans (by positivity) hreg
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos (neg_pos.mpr hneg) hM]
  refine ⟨?_, ?_, hΔ⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : q.Δ * complexity q * (20 * q.ε * stepScale q) =
        q.Δ * (20 * q.ε) * (stepScale q * complexity q) := by ring
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ q.Δ * (20 * q.ε))
    nlinarith [mul_nonneg hΔ hε.le]
  · rw [div_le_div_iff₀ (by positivity) hε]
    have : q.Δ * complexity q * (20 * q.ε * stepScale q) =
        q.Δ * (20 * q.ε) * (stepScale q * complexity q) := by ring
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ q.Δ * (20 * q.ε))
    nlinarith [mul_nonneg hΔ hε.le]

lemma scaled_ratio_ge : 2 ^ 7 ≤ q.Δ * complexity q / (2 ^ 63 * q.ε) := by
  obtain ⟨_, _, _, _, hε, hreg, _⟩ := hv
  rw [le_div_iff₀ (by positivity)]
  change 2 ^ 70 * q.ε ≤ q.Δ * complexity q at hreg
  nlinarith

lemma chainLength_ge : 8 ≤ chainLength q := by
  unfold chainLength
  apply Nat.le_floor
  have h1 := (ratio_bounds q hv).1
  have h2 := scaled_ratio_ge q hv
  push_cast
  linarith

lemma chainLength_le : (chainLength q : ℝ) ≤ q.Δ / (20 * q.ε * stepScale q) := by
  have h1 := (ratio_bounds q hv).1
  have h2 := scaled_ratio_ge q hv
  exact Nat.floor_le (by linarith)

lemma chainLength_le_ratio : (chainLength q : ℝ) ≤ q.Δ * complexity q / q.ε :=
  (chainLength_le q hv).trans (ratio_bounds q hv).2.1

lemma chainLength_lower : q.Δ * complexity q / (2 ^ 64 * q.ε) ≤ (chainLength q : ℝ) - 1 := by
  have hε := hv.2.2.2.2.1
  have h1 := (ratio_bounds q hv).1
  have h2 := scaled_ratio_ge q hv
  have h3 : q.Δ / (20 * q.ε * stepScale q) < (chainLength q : ℝ) + 1 := Nat.lt_floor_add_one _
  have e : q.Δ * complexity q / (2 ^ 64 * q.ε) = q.Δ * complexity q / (2 ^ 63 * q.ε) / 2 := by
    rw [div_div]
    congr 1
    ring
  rw [e]
  linarith

lemma amplitude_chain_le : amplitude q * (4 * (chainLength q : ℝ)) ≤ q.Δ := by
  have hL₁ := hv.1
  have hε := hv.2.2.2.2.1
  have hl := stepScale_pos q hL₁ hε
  have h := chainLength_le q hv
  rw [le_div_iff₀ (by positivity)] at h
  unfold amplitude
  nlinarith

lemma budget_le (N : ℕ) (hN : N ≤ lowerBudget q) :
    (N : ℝ) ≤ q.Δ * complexity q * (1 + q.σ ^ 2 / q.ε ^ 2) / (2 ^ 174 * q.ε) := by
  have hL₁ := hv.1
  have hL₂ := hv.2.1
  have hL₃ := hv.2.2.1
  have hε := hv.2.2.2.2.1
  have hΔ := (ratio_bounds q hv).2.2
  have hM := complexity_pos q hL₁ hL₂ hL₃ hε
  have h0 : 0 ≤ q.Δ * complexity q * (1 + q.σ ^ 2 / q.ε ^ 2) / (2 ^ 174 * q.ε) := by positivity
  exact (Nat.cast_le.mpr hN).trans (Nat.floor_le h0)

lemma budget_reveal (N : ℕ) (hN : N ≤ lowerBudget q) :
    8 * ((N : ℝ) * revealProb q) ≤ (chainLength q : ℝ) - 1 := by
  have hL₁ := hv.1
  have hL₂ := hv.2.1
  have hL₃ := hv.2.2.1
  have hε := hv.2.2.2.2.1
  have hΔ := (ratio_bounds q hv).2.2
  have hM := complexity_pos q hL₁ hL₂ hL₃ hε
  have hb := budget_le q hv N hN
  have hr := revealProb_noise q hε
  have hr0 := revealProb_pos q hε
  have hlow := chainLength_lower q hv
  have h1 : (N : ℝ) * revealProb q ≤
      q.Δ * complexity q / (2 ^ 174 * q.ε) * (25 * 2 ^ 102) := by
    calc (N : ℝ) * revealProb q
        ≤ q.Δ * complexity q * (1 + q.σ ^ 2 / q.ε ^ 2) / (2 ^ 174 * q.ε) * revealProb q :=
          mul_le_mul_of_nonneg_right hb hr0.le
      _ = q.Δ * complexity q / (2 ^ 174 * q.ε) * (revealProb q * (1 + q.σ ^ 2 / q.ε ^ 2)) := by ring
      _ ≤ q.Δ * complexity q / (2 ^ 174 * q.ε) * (25 * 2 ^ 102) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
  have h2 : 8 * (q.Δ * complexity q / (2 ^ 174 * q.ε) * (25 * 2 ^ 102)) ≤
      q.Δ * complexity q / (2 ^ 64 * q.ε) := by
    have hX : 0 ≤ q.Δ * complexity q / q.ε := by positivity
    have e1 : 8 * (q.Δ * complexity q / (2 ^ 174 * q.ε) * (25 * 2 ^ 102)) =
        q.Δ * complexity q / q.ε * (200 * 2 ^ 102 / 2 ^ 174) := by ring
    have e2 : q.Δ * complexity q / (2 ^ 64 * q.ε) = q.Δ * complexity q / q.ε * (1 / 2 ^ 64) := by
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (by norm_num) hX
  linarith

lemma dimension_room (N : ℕ) (hN : N ≤ lowerBudget q) :
    2 ^ 134 * ((N : ℝ) + 1) * (chainLength q : ℝ) ^ 3 + chainLength q ≤ q.d := by
  have hL₁ := hv.1
  have hL₂ := hv.2.1
  have hL₃ := hv.2.2.1
  have hε := hv.2.2.2.2.1
  have hd := hv.2.2.2.2.2.2
  have hΔ := (ratio_bounds q hv).2.2
  have hM := complexity_pos q hL₁ hL₂ hL₃ hε
  have hb := budget_le q hv N hN
  have hT := chainLength_le_ratio q hv
  have hT0 : (0 : ℝ) ≤ chainLength q := Nat.cast_nonneg _
  set Y := q.Δ * complexity q * (1 + q.σ ^ 2 / q.ε ^ 2) / q.ε with hY
  have hY0 : 0 ≤ Y := by positivity
  have hNX : (N : ℝ) + 1 ≤ 1 + Y := by
    have e : q.Δ * complexity q * (1 + q.σ ^ 2 / q.ε ^ 2) / (2 ^ 174 * q.ε) = Y / 2 ^ 174 := by
      rw [hY]; ring
    rw [e] at hb
    have : Y / 2 ^ 174 ≤ Y := div_le_self hY0 (by norm_num)
    linarith
  have hTX : (chainLength q : ℝ) ≤ 1 + Y := by
    have h1 : q.Δ * complexity q / q.ε ≤ Y := by
      rw [hY, div_le_div_iff_of_pos_right hε]
      have h0 : 0 ≤ q.Δ * complexity q := by positivity
      have h2 : (1 : ℝ) ≤ 1 + q.σ ^ 2 / q.ε ^ 2 := by
        have : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
        linarith
      nlinarith
    linarith
  change 2 ^ 140 * (1 + Y) ^ 4 ≤ (q.d : ℝ) at hd
  set X := 1 + Y
  have hX1 : 1 ≤ X := by linarith
  have h3 : (chainLength q : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hT0 hTX 3
  have hX3 : 0 ≤ X ^ 3 := by positivity
  have hprod : ((N : ℝ) + 1) * (chainLength q : ℝ) ^ 3 ≤ X * X ^ 3 :=
    mul_le_mul hNX h3 (by positivity) (by linarith)
  have hX4 : X ≤ X ^ 4 := le_self_pow₀ hX1 (by norm_num)
  have e4 : X * X ^ 3 = X ^ 4 := by ring
  rw [e4] at hprod
  have hX40 : 0 ≤ X ^ 4 := by positivity
  nlinarith [hprod, hX4, hTX, hd, hX40]

end Regime

end LongTails.Proofs.ThirdOrderLowerParameters
