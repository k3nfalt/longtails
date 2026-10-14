import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset

namespace OracleTemplate.MomentumConvex

noncomputable def wt (γ κ τ : ℝ) : ℝ := 2 * (τ + 1 + κ) / (γ * τ ^ 2 * (τ + 1 + 3 * κ))

noncomputable def lam (κ τ : ℝ) : ℝ := τ * (τ + 2 + κ) / ((τ + 1) * (τ + 2 + 3 * κ))

noncomputable def nu (κ τ : ℝ) : ℝ := 2 * κ / (τ + 1 + 3 * κ)

noncomputable def rho (κ τ : ℝ) : ℝ := 2 * (τ + 1 + κ) / (τ * (τ + 1 + 3 * κ))

noncomputable def sig (κ τ : ℝ) : ℝ := (τ + 1) * (τ + 1 + κ) / (τ * (τ + 1 + 3 * κ))

noncomputable def uu (κ τ : ℝ) : ℝ := lam κ τ + nu κ τ

lemma wt_pos {γ κ τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 0 < τ) : 0 < wt γ κ τ := by
  unfold wt; positivity

lemma wt_anti {γ κ τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 0 < τ) : wt γ κ (τ + 1) ≤ wt γ κ τ := by
  unfold wt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : 0 ≤ 2 * γ * (6 * κ ^ 2 * τ + 3 * κ ^ 2 + 6 * κ * τ ^ 2 + 14 * κ * τ + 5 * κ + 2 * τ ^ 3 +
      7 * τ ^ 2 + 7 * τ + 2) := by positivity
  linear_combination h

lemma rho_eq {γ κ τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 0 < τ) :
    γ * τ * wt γ κ τ = rho κ τ := by
  unfold wt rho
  have h1 : τ + 1 + 3 * κ ≠ 0 := by positivity
  field_simp

lemma nu_eq {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 < τ) :
    κ * τ / (τ + 1 + κ) * rho κ τ = nu κ τ := by
  unfold rho nu
  have h1 : τ + 1 + 3 * κ ≠ 0 := by positivity
  have h2 : τ + 1 + κ ≠ 0 := by positivity
  field_simp

lemma lam_eq {γ κ τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 0 < τ) :
    γ * τ * (τ + 1) / 2 * wt γ κ (τ + 1) = lam κ τ := by
  unfold wt lam
  have h1 : τ + 1 + 1 + 3 * κ ≠ 0 := by positivity
  have h2 : τ + 2 + 3 * κ ≠ 0 := by positivity
  have h3 : τ + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma sig_eq {γ κ τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 0 < τ) :
    γ * τ * (τ + 1) / 2 * wt γ κ τ = sig κ τ := by
  unfold wt sig
  have h1 : τ + 1 + 3 * κ ≠ 0 := by positivity
  field_simp

lemma lam_pred_add_rho {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 1 ≤ τ) :
    lam κ (τ - 1) + rho κ τ = sig κ τ := by
  unfold lam rho sig
  have h0 : (0 : ℝ) < τ := by linarith
  have e1 : τ - 1 + 2 + κ = τ + 1 + κ := by ring
  have e2 : τ - 1 + 1 = τ := by ring
  have e3 : τ - 1 + 2 + 3 * κ = τ + 1 + 3 * κ := by ring
  rw [e1, e2, e3]
  have h1 : τ + 1 + 3 * κ ≠ 0 := by positivity
  field_simp
  ring

lemma lam_nonneg {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 ≤ τ) : 0 ≤ lam κ τ := by
  unfold lam; positivity

lemma nu_nonneg {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 ≤ τ) : 0 ≤ nu κ τ := by
  unfold nu; positivity

lemma rho_pos {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 < τ) : 0 < rho κ τ := by
  unfold rho; positivity

lemma nu_le {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 ≤ τ) : nu κ τ ≤ 2 * κ / (τ + 1) := by
  unfold nu
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

lemma uu_mono {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 2 ≤ τ) : uu κ (τ - 1) ≤ uu κ τ := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ τ = s + 2 := ⟨τ - 2, by linarith, by ring⟩
  unfold uu lam nu
  have e : s + 2 - 1 = s + 1 := by ring
  rw [e]
  rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h : 0 ≤ (s + 3 * κ + 2) * (s + 3 * κ + 4) *
      (s ^ 3 + s ^ 2 * κ + 9 * s ^ 2 + 9 * s * κ ^ 2 + 14 * s * κ + 26 * s + 9 * κ ^ 3 + 33 * κ ^ 2 +
        30 * κ + 24) := by positivity
  nlinarith [h]

lemma uu_one {κ : ℝ} (hκ : 0 ≤ κ) : 1 / 2 ≤ uu κ 1 := by
  unfold uu lam nu
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hκ hκ, hκ]

lemma noise_le {γ κ τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 0 < τ) :
    wt γ κ τ * (γ * τ) ^ 2 ≤ 2 * γ := by
  unfold wt
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h : 0 ≤ γ ^ 2 * τ ^ 2 * (4 * κ) := by positivity
  nlinarith [h]

lemma jensen_le {γ κ τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 1 ≤ τ) :
    (wt γ κ τ - wt γ κ (τ + 1)) * (κ * γ * τ) ^ 2 ≤ 4 * κ ^ 2 * γ / (τ + 1) := by
  have h0 : 0 < τ := by linarith
  have key : wt γ κ τ - wt γ κ (τ + 1) ≤ 4 / (γ * τ ^ 2 * (τ + 1)) := by
    unfold wt
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ τ = s + 1 := ⟨τ - 1, by linarith, by ring⟩
    have h : 0 ≤ γ ^ 2 * (s + 1) ^ 2 * (s + 2) *
        (12 * s ^ 2 * κ + 2 * s ^ 2 + 24 * s * κ ^ 2 + 56 * s * κ + 10 * s + 54 * κ ^ 2 + 70 * κ + 12) := by
      positivity
    nlinarith [h]
  have h2 : 0 ≤ (κ * γ * τ) ^ 2 := sq_nonneg _
  calc (wt γ κ τ - wt γ κ (τ + 1)) * (κ * γ * τ) ^ 2
      ≤ 4 / (γ * τ ^ 2 * (τ + 1)) * (κ * γ * τ) ^ 2 := mul_le_mul_of_nonneg_right key h2
    _ = 4 * κ ^ 2 * γ / (τ + 1) := by field_simp

lemma wt_top_le {γ κ τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 0 < τ) :
    wt γ κ τ ≤ 2 / (γ * τ ^ 2) := by
  unfold wt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : 0 ≤ γ * τ ^ 2 * (4 * κ) := by positivity
  nlinarith [h]

end OracleTemplate.MomentumConvex
