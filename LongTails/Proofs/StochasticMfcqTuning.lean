import LongTails.Algorithms.StochasticMfcqDirection
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace LongTails.Proofs.StochasticMfcqTuning

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection

lemma precision_bounds (p : Params) (hp : spec.valid p) :
    0 < precision p ∧ precision p ≤ 1 ∧ 10 * precision p ≤ p.μ ∧
      5 * precision p ≤ p.τ ∧ 20 * p.H * precision p ≤ p.μ * p.ε := by
  rcases hp with ⟨hm, hH, hσ, hL, hμ, hμH, hτ, hΔ, hε, hρ, hρ1⟩
  have hH0 : 0 < p.H := by linarith
  let t := min p.ε (min 1 p.τ)
  have ht : 0 < t := lt_min hε (lt_min (by norm_num) hτ)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have htτ : t ≤ p.τ := (min_le_right _ _).trans (min_le_right _ _)
  have htε : t ≤ p.ε := min_le_left _ _
  have he : 40 * p.H * precision p = p.μ * t := by
    dsimp [precision, t]
    field_simp
  have hd : 0 < precision p := div_pos (mul_pos hμ ht) (by positivity)
  have hμt : p.μ * t ≤ p.μ := by nlinarith [mul_le_mul_of_nonneg_left ht1 hμ.le]
  have hτt : p.μ * t ≤ p.H * p.τ :=
    mul_le_mul hμH htτ ht.le hH0.le
  have hεt : p.μ * t ≤ p.μ * p.ε := mul_le_mul_of_nonneg_left htε hμ.le
  have hd1 : precision p ≤ 1 := by nlinarith
  have hdμ : 10 * precision p ≤ p.μ := by nlinarith
  have hdτ : 5 * precision p ≤ p.τ := by nlinarith
  exact ⟨hd, hd1, hdμ, hdτ, by nlinarith⟩

lemma stepSize_pos (p : Params) (hp : spec.valid p) : 0 < stepSize p := by
  have hH := hp.2.1
  exact div_pos (precision_bounds p hp).1 (by positivity)

lemma outerSteps_positive (p : Params) : 0 < outerSteps p := by
  unfold outerSteps
  omega

lemma outerSteps_gap (p : Params) (hp : spec.valid p) :
    p.Δ < outerSteps p * (precision p ^ 2 / (2 * p.H)) := by
  have hH : 0 < p.H := by linarith [hp.2.1]
  have hδ := (precision_bounds p hp).1
  have hc := Nat.le_ceil (2 * p.H * p.Δ / precision p ^ 2)
  have hn : 2 * p.H * p.Δ / precision p ^ 2 < (outerSteps p : ℝ) := by
    dsimp [outerSteps]
    push_cast
    linarith
  have hd : 0 < precision p ^ 2 := sq_pos_of_pos hδ
  have hmul := (div_lt_iff₀ hd).mp hn
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ (by positivity : 0 < 2 * p.H)).2
  nlinarith

lemma hullSteps_sufficient (p : Params) (hp : spec.valid p) :
    0 < hullSteps p ∧ 10 * (p.H + 1) ^ 2 / hullSteps p ≤ precision p ^ 2 := by
  have hδ := (precision_bounds p hp).1
  have hn : 0 < hullSteps p := by unfold hullSteps; omega
  refine ⟨hn, (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < hullSteps p)).2 ?_⟩
  have hc := Nat.le_ceil (10 * (p.H + 1) ^ 2 / precision p ^ 2)
  have hc' : 10 * (p.H + 1) ^ 2 / precision p ^ 2 ≤ (hullSteps p : ℝ) := by
    dsimp [hullSteps]
    push_cast
    linarith
  have hmul := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hc'
  nlinarith

lemma batch_sizes_positive (p : Params) :
    0 < epochLength p ∧ 0 < resetBatch p ∧ 0 < incrementBatch p ∧ 0 < replicas p := by
  unfold epochLength resetBatch incrementBatch replicas
  omega

lemma reset_variance_bound (p : Params) (hp : spec.valid p) :
    p.σ ^ 2 / resetBatch p ≤ precision p ^ 2 / 1152 := by
  have hδ := (precision_bounds p hp).1
  have hn : (0 : ℝ) < resetBatch p := by exact_mod_cast (batch_sizes_positive p).2.1
  have hc : 1152 * p.σ ^ 2 / precision p ^ 2 ≤ (resetBatch p : ℝ) := by
    have h := Nat.le_ceil (1152 * p.σ ^ 2 / precision p ^ 2)
    unfold resetBatch
    push_cast
    linarith
  have hm := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hc
  apply (div_le_iff₀ hn).2
  nlinarith

lemma epoch_increment_variance_bound (p : Params) (hp : spec.valid p) :
    (epochLength p : ℝ) * (p.L ^ 2 * stepSize p ^ 2 / incrementBatch p) ≤
      precision p ^ 2 / 1152 := by
  have hH : 0 < p.H := by linarith [hp.2.1]
  have hn : (0 : ℝ) < incrementBatch p := by exact_mod_cast (batch_sizes_positive p).2.2.1
  have hc : 72 * (epochLength p : ℝ) * p.L ^ 2 / p.H ^ 2 ≤ (incrementBatch p : ℝ) := by
    have h := Nat.le_ceil (72 * (epochLength p : ℝ) * p.L ^ 2 / p.H ^ 2)
    unfold incrementBatch
    push_cast
    linarith
  have hm := (div_le_iff₀ (sq_pos_of_pos hH)).mp hc
  have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg (precision p))
  unfold stepSize
  field_simp
  nlinarith

lemma epoch_variance_bound (p : Params) (hp : spec.valid p) (k : ℕ)
    (hk : k ≤ epochLength p) :
    p.σ ^ 2 / resetBatch p + k * (p.L ^ 2 * stepSize p ^ 2 / incrementBatch p) ≤
      precision p ^ 2 / 576 := by
  have hk' : (k : ℝ) ≤ epochLength p := by exact_mod_cast hk
  have hv : 0 ≤ p.L ^ 2 * stepSize p ^ 2 / incrementBatch p := by positivity
  have hb := mul_le_mul_of_nonneg_right hk' hv
  linarith [reset_variance_bound p hp, epoch_increment_variance_bound p hp]

lemma epochLength_le_outerSteps (p : Params) (hp : spec.valid p) :
    epochLength p ≤ outerSteps p := by
  have hH : 0 < p.H := by linarith [hp.2.1]
  have hσ : 0 ≤ p.σ := hp.2.2.1
  have hL : 0 ≤ p.L := hp.2.2.2.1
  have hδ := (precision_bounds p hp).1
  have hN : (0 : ℝ) ≤ outerSteps p := Nat.cast_nonneg _
  have hden : 0 < outerSteps p * p.L * precision p + p.H * (p.σ + precision p) := by
    positivity
  unfold epochLength
  apply max_le (outerSteps_positive p)
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hden).mpr
  have hnon : 0 ≤ outerSteps p * p.L * precision p + p.H * precision p := by positivity
  nlinarith [mul_nonneg hN hnon]

lemma confidence_bound (p : Params) (hp : spec.valid p) :
    (outerSteps p : ℝ) * (1 / 4 : ℝ) ^ replicas p ≤ p.ρ := by
  rcases hp with ⟨hm, hH, hσ, hL, hμ, hμH, hτ, hΔ, hε, hρ, hρ1⟩
  have hN : 0 < (outerSteps p : ℝ) := by unfold outerSteps; positivity
  have hpow : (outerSteps p : ℝ) / p.ρ ≤ (4 : ℝ) ^ replicas p := by
    calc
      _ = (4 : ℝ) ^ (Real.log (outerSteps p / p.ρ) / Real.log 4) :=
        (Real.rpow_logb (by norm_num) (by norm_num) (div_pos hN hρ)).symm
      _ ≤ (4 : ℝ) ^ ((replicas p : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hh := Nat.le_ceil (Real.log (outerSteps p / p.ρ) / Real.log 4)
        unfold replicas
        push_cast
        linarith
      _ = _ := Real.rpow_natCast _ _
  have hNle : (outerSteps p : ℝ) ≤ p.ρ * (4 : ℝ) ^ replicas p := by
    have := (div_le_iff₀ hρ).mp hpow
    nlinarith
  rw [one_div_pow, mul_one_div, div_le_iff₀ (by positivity)]
  exact hNle

end LongTails.Proofs.StochasticMfcqTuning
