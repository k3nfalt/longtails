import LongTails.Setups.StretchedExponentialMarkovConvex
import LongTails.Includes
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

namespace OracleTemplate.StretchedExponentialMarkov

lemma log_one_add_le_rpow_div {x γ : ℝ} (hx : 0 ≤ x) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) : Real.log (1 + x) ≤ x ^ γ / γ := by
  have hpos : 0 < 1 + x := by positivity
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos γ)
  rw [Real.log_rpow hpos] at hlog
  have hpow := Real.rpow_add_le_add_rpow (show (0 : ℝ) ≤ 1 by norm_num) hx hγ.le hγ1
  rw [Real.one_rpow] at hpow
  apply (le_div_iff₀ hγ).mpr
  nlinarith

lemma stretched_le_polynomial {t τ γ β : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hβ : 0 < β) :
    Real.exp (-((t / τ) ^ γ)) ≤
      (1 + t / (τ * (β / γ) ^ (1 / γ))) ^ (-β) := by
  have hc : 0 < β / γ := div_pos hβ hγ
  have hs : 0 < τ * (β / γ) ^ (1 / γ) := by positivity
  have hx : 0 ≤ t / (τ * (β / γ) ^ (1 / γ)) := div_nonneg ht hs.le
  have hr : (t / (τ * (β / γ) ^ (1 / γ))) ^ γ =
      (t / τ) ^ γ / (β / γ) := by
    rw [div_mul_eq_div_div, Real.div_rpow (div_nonneg ht hτ.le)
      (Real.rpow_nonneg hc.le _), ← Real.rpow_mul hc.le]
    rw [one_div_mul_cancel hγ.ne', Real.rpow_one]
  have hl := log_one_add_le_rpow_div hx hγ hγ1
  rw [hr] at hl
  have hb := mul_le_mul_of_nonneg_left hl hβ.le
  have he : β * ((t / τ) ^ γ / (β / γ) / γ) = (t / τ) ^ γ := by
    field_simp
  rw [he] at hb
  rw [Real.rpow_def_of_pos (show 0 < 1 + t / (τ * (β / γ) ^ (1 / γ)) by linarith)]
  apply Real.exp_le_exp.mpr
  nlinarith

open LongTails.Setups
open StretchedExponentialMarkovConvex
open MeasureTheory ProbabilityTheory

noncomputable def polynomialInclusion (β : ℝ) (hβ : 0 < β) :
    Inclusion HeavyTailedMarkovSmoothAndConvex.spec
      StretchedExponentialMarkovConvex.spec where
  numOracles_eq := rfl
  mapParams p := p.polynomial β
  mapPublic p := p.polynomial β
  instance_eq _ := rfl
  query_eq _ := rfl
  reply_eq _ := rfl
  output_eq _ := rfl
  public_eq _ := rfl
  valid p hp := by
    rcases hp with ⟨_, hL, hR, hσ, hα, hα2, hτ, hγ, _, hε, _⟩
    exact ⟨hL, hR.le, hσ.le, hα, hα2,
      mul_pos (by linarith) (Real.rpow_pos_of_pos (div_pos hβ hγ) _), hβ, hε⟩
  admissible p hp f O h := by
    rcases hp with ⟨_, _, _, _, _, _, hτ, hγ, hγ1, _⟩
    rcases h with ⟨g, κ, hκ, π, hO, hπ, hi, hm, rest⟩
    refine ⟨g, κ, hκ, π, hO, hπ, hi, ?_, rest⟩
    intro t
    exact (hm t).trans (stretched_le_polynomial (Nat.cast_nonneg t)
      (by linarith) hγ hγ1 hβ)
  successful := by
    intro p hp I O ha Ω m output P h
    exact h
  allowedAlgorithm _ _ _ := trivial

lemma valid_nonempty : ∃ p, StretchedExponentialMarkovConvex.spec.valid p := by
  refine ⟨{ d := 1, L := 1, R := 1, σ := 1, α := 2, τ := 1, γ := 1, ε := 1 / 1024, x0 := 0 }, ?_⟩
  norm_num [StretchedExponentialMarkovConvex.spec, Real.rpow_two]

end OracleTemplate.StretchedExponentialMarkov
