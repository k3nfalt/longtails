import LongTails.Proofs.GeneralizedMirrorRun
import Mathlib.Analysis.Complex.ExponentialBounds

open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorWeights

namespace LongTails.Proofs.GeneralizedMirrorBudget

noncomputable def confidence (H δ : ℝ) : ℝ := Real.log (64 * H / δ)

lemma confidence_lower {H δ : ℝ} (hH : 2 ≤ H) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 ≤ confidence H δ := by
  have hratio : 4 ≤ 64 * H / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [he] at hl
  unfold confidence
  linarith [Real.log_two_gt_d9]

lemma pilotSize_pos {ell : ℝ} (hell : 1 ≤ ell) : 0 < ⌈8 * ell⌉₊ :=
  Nat.ceil_pos.mpr (by linarith)

lemma pilotSize_tail {ell : ℝ} :
    (1 / 2 : ℝ) ^ ⌈8 * ell⌉₊ ≤ Real.exp (-4 * ell) := by
  have hm := Nat.le_ceil (8 * ell)
  have hlog : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he (m : ℕ) : (1 / 2 : ℝ) ^ m = Real.exp (-(m : ℝ) * Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp
  rw [he]
  apply Real.exp_le_exp.mpr
  have hp := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg ⌈8 * ell⌉₊)
  linarith

lemma iterations_upper {H ell : ℝ} (hH : 2 ≤ H) (hell : 1 ≤ ell) :
    (⌈H * ell⌉₊ : ℝ) ≤ 2 * H * ell := by
  have hH0 : 0 < H := by linarith
  have hell0 : 0 < ell := by linarith
  have hm : 1 ≤ H * ell := by nlinarith
  have hh := Nat.ceil_lt_add_one (show 0 ≤ H * ell by positivity)
  linarith

lemma confidence_failure {H δ : ℝ} (hH : 2 ≤ H) (hδ : 0 < δ) (hδ1 : δ < 1) :
    3 * (⌈H * confidence H δ⌉₊ : ℝ) * Real.exp (-4 * confidence H δ) ≤ δ := by
  let ell := confidence H δ
  have hell : 1 ≤ ell := confidence_lower hH hδ hδ1
  have hH0 : 0 < H := by linarith
  have hK := iterations_upper hH hell
  have he : ell ≤ Real.exp ell := by linarith [Real.add_one_le_exp ell]
  have hprod : Real.exp ell * Real.exp (-4 * ell) = Real.exp (-3 * ell) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hex : Real.exp (-ell) = δ / (64 * H) := by
    dsimp [ell, confidence]
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 64 * H / δ)]
    field_simp
  calc
    _ ≤ 6 * H * ell * Real.exp (-4 * ell) := by
      have ht := mul_le_mul_of_nonneg_right hK (Real.exp_nonneg (-4 * ell))
      nlinarith only [ht]
    _ ≤ 6 * H * Real.exp ell * Real.exp (-4 * ell) := by gcongr
    _ = 6 * H * Real.exp (-3 * ell) := by rw [mul_assoc (6 * H), hprod]
    _ ≤ 6 * H * Real.exp (-ell) := by gcongr; linarith
    _ = 3 * δ / 32 := by rw [hex]; field_simp; ring
    _ ≤ δ := by linarith

lemma oracle_calls_upper {H ell : ℝ} (hH : 2 ≤ H) (hell : 1 ≤ ell) :
    (⌈H * ell⌉₊ * (⌈8 * ell⌉₊ + 2) : ℕ) ≤ ⌈22 * H * ell ^ 2⌉₊ := by
  have hH0 : 0 < H := by linarith
  have hell0 : 0 < ell := by linarith
  have hK := iterations_upper hH hell
  have hm := Nat.ceil_lt_add_one (show 0 ≤ 8 * ell by positivity)
  have hm' : (⌈8 * ell⌉₊ : ℝ) + 2 ≤ 11 * ell := by linarith
  have hp := mul_le_mul hK hm' (by positivity) (by positivity)
  have hcast : ((⌈H * ell⌉₊ * (⌈8 * ell⌉₊ + 2) : ℕ) : ℝ) ≤
      (⌈22 * H * ell ^ 2⌉₊ : ℝ) := by
    calc
      _ = (⌈H * ell⌉₊ : ℝ) * ((⌈8 * ell⌉₊ : ℝ) + 2) := by norm_cast
      _ ≤ (2 * H * ell) * (11 * ell) := hp
      _ = 22 * H * ell ^ 2 := by ring
      _ ≤ _ := Nat.le_ceil _
  exact Nat.cast_le.mp hcast

lemma scaled_power {σ ρ α : ℝ} (hσ : 0 ≤ σ) (hρ : 0 < ρ) (hα : 1 < α) :
    (256 * σ ^ α * ρ) ^ (1 / (α - 1)) * ρ =
      (256 : ℝ) ^ (1 / (α - 1)) * (σ * ρ) ^ (α / (α - 1)) := by
  have hden : α - 1 ≠ 0 := by linarith
  have he : α * (1 / (α - 1)) = 1 / (α - 1) + 1 := by field_simp [hden]; ring
  have hex : α / (α - 1) = α * (1 / (α - 1)) := by ring
  rw [hex, Real.mul_rpow (by positivity : 0 ≤ 256 * σ ^ α) hρ.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 256) (Real.rpow_nonneg hσ _),
    ← Real.rpow_mul hσ, Real.mul_rpow hσ hρ.le]
  have hp : ρ ^ (1 / (α - 1)) * ρ = ρ ^ (α * (1 / (α - 1))) := by
    rw [he, Real.rpow_add hρ, Real.rpow_one]
  calc
    _ = (256 : ℝ) ^ (1 / (α - 1)) * σ ^ (α * (1 / (α - 1))) *
        (ρ ^ (1 / (α - 1)) * ρ) := by ring
    _ = _ := by rw [hp]; ring

lemma scaled_clipRadius (q : Public) (hq : spec.valid q) :
    clipRadius q * q.R / q.ε = 96 * (q.σ * q.R / q.ε) + 1 +
      2 * (256 : ℝ) ^ (1 / (q.α - 1)) * (q.σ * q.R / q.ε) ^ (q.α / (q.α - 1)) := by
  rcases hq with ⟨_, _, hR, _, _, hσ, hα, _, hε, _⟩
  have hp := scaled_power hσ (div_pos hR hε) hα
  have harg : 256 * q.σ ^ q.α * q.R / q.ε = 256 * q.σ ^ q.α * (q.R / q.ε) := by ring
  have he : q.ε / q.R * (q.R / q.ε) = 1 := by field_simp
  unfold clipRadius
  rw [harg]
  calc
    _ = 96 * q.σ * (q.R / q.ε) + q.ε / q.R * (q.R / q.ε) +
        2 * ((256 * q.σ ^ q.α * (q.R / q.ε)) ^ (1 / (q.α - 1)) * (q.R / q.ε)) := by ring
    _ = _ := by rw [he, hp]; simp only [mul_div_assoc]; ring

lemma heavy_scaled_bound {α t D Λ : ℝ} (hα : 1 < α) (hα2 : α ≤ 2)
    (ht : 0 ≤ t) (hD : 1 ≤ D) (hΛ : Λ = 96 * t + 1 + 2 * D * t ^ (α / (α - 1))) :
    1 + Λ + 4 * Λ ^ (2 - α) * t ^ α ≤ 512 * (1 + D * t ^ (α / (α - 1))) := by
  have hden : 0 < α - 1 := by linarith
  have hq : 1 ≤ α / (α - 1) := (le_div_iff₀ hden).mpr (by linarith)
  have hqpos : 0 < α / (α - 1) := by positivity
  have he0 : 0 ≤ 2 - α := by linarith
  have he1 : 2 - α ≤ 1 := by linarith
  have hD0 : 0 ≤ D := by linarith
  have htp : 0 ≤ t ^ (α / (α - 1)) := Real.rpow_nonneg ht _
  have hw : 0 ≤ D * t ^ (α / (α - 1)) := mul_nonneg hD0 htp
  have hM1 : 1 ≤ max 1 (D * t ^ (α / (α - 1))) := le_max_left _ _
  have hMw : D * t ^ (α / (α - 1)) ≤ max 1 (D * t ^ (α / (α - 1))) := le_max_right _ _
  have htM : t ≤ max 1 (D * t ^ (α / (α - 1))) := by
    by_cases ht1 : t ≤ 1
    · exact ht1.trans hM1
    · have hh := Real.self_le_rpow_of_one_le (le_of_not_ge ht1) hq
      have hd := mul_le_mul_of_nonneg_right hD htp
      nlinarith
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hΛM : Λ ≤ 100 * max 1 (D * t ^ (α / (α - 1))) := by rw [hΛ]; nlinarith
  have h100 : (100 : ℝ) ^ (2 - α) ≤ 100 := Real.rpow_le_self_of_one_le (by norm_num) he1
  have hnoise : Λ ^ (2 - α) * t ^ α ≤ 100 * max 1 (D * t ^ (α / (α - 1))) := by
    by_cases hcase : D * t ^ (α / (α - 1)) ≤ 1
    · rw [max_eq_left hcase] at hΛM htM ⊢
      simp only [mul_one] at hΛM ⊢
      have hp := (Real.rpow_le_rpow hΛ0 hΛM he0).trans h100
      have htα := Real.rpow_le_one ht htM (by linarith : 0 ≤ α)
      have hh := mul_le_mul hp htα (Real.rpow_nonneg ht _) (by norm_num : (0 : ℝ) ≤ 100)
      simpa using hh
    · have hw1 : 1 ≤ D * t ^ (α / (α - 1)) := le_of_not_ge hcase
      rw [max_eq_right hw1] at hΛM ⊢
      have htpos : 0 < t := by
        by_contra hn
        have hz : t = 0 := le_antisymm (not_lt.mp hn) ht
        rw [hz, Real.zero_rpow hqpos.ne', mul_zero] at hw1
        norm_num at hw1
      have hpow := Real.rpow_le_rpow hΛ0 hΛM he0
      have hd := Real.rpow_le_self_of_one_le hD he1
      have hcomb : α / (α - 1) * (2 - α) + α = α / (α - 1) := by
        field_simp [hden.ne']
        ring
      have heq : (100 * (D * t ^ (α / (α - 1)))) ^ (2 - α) * t ^ α =
          (100 : ℝ) ^ (2 - α) * D ^ (2 - α) * t ^ (α / (α - 1)) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 100) hw,
          Real.mul_rpow hD0 htp, ← Real.rpow_mul ht]
        rw [mul_assoc, mul_assoc, ← Real.rpow_add htpos, hcomb]
        ring
      have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg ht α)
      rw [heq] at hh
      apply hh.trans
      have hc := mul_le_mul h100 hd (Real.rpow_nonneg hD0 _) (by norm_num : (0 : ℝ) ≤ 100)
      nlinarith [mul_le_mul_of_nonneg_right hc htp]
  have hM : max 1 (D * t ^ (α / (α - 1))) ≤ 1 + D * t ^ (α / (α - 1)) :=
    max_le (by linarith) (by linarith)
  nlinarith

lemma scaled_noiseMoment (q : Public) (hq : spec.valid q) :
    noiseMoment q * q.R ^ 2 / q.ε ^ 2 =
      4 * (clipRadius q * q.R / q.ε) ^ (2 - q.α) * (q.σ * q.R / q.ε) ^ q.α := by
  rcases hq with ⟨_, _, hR, _, _, hσ, _, _, hε, _⟩
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hσ hε
  have hρ : 0 < q.R / q.ε := div_pos hR hε
  have hr : (q.R / q.ε) ^ (2 - q.α) * (q.R / q.ε) ^ q.α = (q.R / q.ε) ^ 2 := by
    rw [← Real.rpow_add hρ, sub_add_cancel, Real.rpow_two]
  simp only [mul_div_assoc]
  rw [Real.mul_rpow hB.le hρ.le, Real.mul_rpow hσ hρ.le]
  calc
    _ = 4 * clipRadius q ^ (2 - q.α) * q.σ ^ q.α * (q.R / q.ε) ^ 2 := by
      unfold noiseMoment
      ring
    _ = 4 * clipRadius q ^ (2 - q.α) * q.σ ^ q.α *
        ((q.R / q.ε) ^ (2 - q.α) * (q.R / q.ε) ^ q.α) := by rw [hr]
    _ = _ := by ring

lemma noise_cost_bound (q : Public) (hq : spec.valid q) :
    1 + clipRadius q * q.R / q.ε + noiseMoment q * q.R ^ 2 / q.ε ^ 2 ≤
      512 * (1 + (256 : ℝ) ^ (1 / (q.α - 1)) * (q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))) := by
  have he := scaled_clipRadius q hq
  have hn := scaled_noiseMoment q hq
  rcases hq with ⟨_, _, hR, _, _, hσ, hα, hα2, hε, _⟩
  have hD : 1 ≤ (256 : ℝ) ^ (1 / (q.α - 1)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hh := heavy_scaled_bound hα hα2 (show 0 ≤ q.σ * q.R / q.ε by positivity) hD he
  rwa [← hn] at hh

noncomputable def rateScale (q : Public) : ℝ :=
  1 + (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) +
    Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) +
      (256 : ℝ) ^ (1 / (q.α - 1)) * (q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))

lemma rateScale_lower (q : Public) (hq : spec.valid q) : 1 ≤ rateScale q := by
  rcases hq with ⟨_, h1, hR, hΔ, _, hσ, _, _, hε, _⟩
  have hl : 0 ≤ Real.log (8 + 8 * q.Δ / q.ε) := Real.log_nonneg (by
    have ht : 0 ≤ 8 * q.Δ / q.ε := by positivity
    linarith)
  have hfirst : 0 ≤ (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) := by positivity
  have hlast : 0 ≤ (256 : ℝ) ^ (1 / (q.α - 1)) *
      (q.σ * q.R / q.ε) ^ (q.α / (q.α - 1)) := by positivity
  unfold rateScale
  nlinarith [Real.sqrt_nonneg ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε)]

lemma horizonScale_upper (q : Public) (hq : spec.valid q) :
    horizonScale q ≤ 134217728 * rateScale q := by
  have hn := noise_cost_bound q hq
  rcases hq with ⟨_, h1, hR, hΔ, _, hσ, _, _, hε, _⟩
  have hl : 0 ≤ Real.log (8 + 8 * q.Δ / q.ε) := Real.log_nonneg (by
    have ht : 0 ≤ 8 * q.Δ / q.ε := by positivity
    linarith)
  have ht : 0 ≤ (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) := by positivity
  unfold horizonScale rateScale
  nlinarith only [hn, ht, Real.sqrt_nonneg ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε)]

lemma explicit_calls_bound (q : Public) (hq : spec.valid q) :
    ⌈horizonScale q * confidence (horizonScale q) q.δ⌉₊ *
      (⌈8 * confidence (horizonScale q) q.δ⌉₊ + 2) ≤
        ⌈8589934592 * rateScale q * (Real.log (8589934592 * rateScale q / q.δ)) ^ 2⌉₊ := by
  have hH := horizonScale_lower q hq
  have hS := rateScale_lower q hq
  have hHS := horizonScale_upper q hq
  have hδ := hq.2.2.2.2.2.2.2.2.2.1
  have hδ1 := hq.2.2.2.2.2.2.2.2.2.2
  have hell := confidence_lower (by linarith : 2 ≤ horizonScale q) hδ hδ1
  have hc := oracle_calls_upper (by linarith : 2 ≤ horizonScale q) hell
  apply hc.trans
  apply Nat.ceil_mono
  have hlog : confidence (horizonScale q) q.δ ≤ Real.log (8589934592 * rateScale q / q.δ) := by
    apply Real.log_le_log (by positivity : 0 < 64 * horizonScale q / q.δ)
    apply (div_le_div_iff_of_pos_right hδ).mpr
    nlinarith only [hHS]
  have hsquare := pow_le_pow_left₀ (by linarith : 0 ≤ confidence (horizonScale q) q.δ) hlog 2
  have hcoeff : 22 * horizonScale q ≤ 8589934592 * rateScale q := by nlinarith
  exact mul_le_mul hcoeff hsquare (sq_nonneg _) (by positivity)

end LongTails.Proofs.GeneralizedMirrorBudget
