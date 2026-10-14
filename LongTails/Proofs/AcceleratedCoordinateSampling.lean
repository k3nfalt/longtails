import LongTails.Algorithms.AcceleratedCoordinate
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.AcceleratedCoordinate

open LongTails.Setups.CoordinateSmoothStronglyConvex

lemma weight_pos (p : Params) (i : Fin p.d) : 0 < weight p i :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma card_choice (p : Params) : Fintype.card (CoordinateChoice p) = totalWeight p := by
  change Fintype.card (Σ i : Fin p.d, Fin (weight p i)) = totalWeight p
  simp [Fintype.card_sigma, totalWeight]

lemma totalWeight_pos (p : Params) : 0 < totalWeight p := by
  rw [← card_choice]
  exact Fintype.card_pos

lemma expect_choice (p : Params) (f : Fin p.d → ℝ) :
    (𝔼 choice : CoordinateChoice p, f choice.1) =
      (∑ i, (weight p i : ℝ) * f i) / (totalWeight p : ℝ) := by
  change (𝔼 choice : Σ i : Fin p.d, Fin (weight p i), f choice.1) = _
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_sigma, Fintype.card_sigma]
  simp [totalWeight]

lemma importance_unbiased (p : Params) (f : Fin p.d → ℝ) :
    (𝔼 choice : CoordinateChoice p,
      (totalWeight p : ℝ) / (weight p choice.1 : ℝ) * f choice.1) = ∑ i, f i := by
  rw [expect_choice p (fun i => (totalWeight p : ℝ) / (weight p i : ℝ) * f i)]
  have hw (i : Fin p.d) : (weight p i : ℝ) ≠ 0 := by exact_mod_cast (weight_pos p i).ne'
  have hM : (totalWeight p : ℝ) ≠ 0 := by exact_mod_cast (totalWeight_pos p).ne'
  simp_rw [show ∀ i, (weight p i : ℝ) *
      ((totalWeight p : ℝ) / (weight p i : ℝ) * f i) = (totalWeight p : ℝ) * f i
    from fun i => by field_simp [hw i]]
  rw [← Finset.mul_sum]
  field_simp

lemma weight_smoothness (p : Params) (hμ : 0 < p.μ)
    (hL : ∀ i, p.μ ≤ p.L i) (i : Fin p.d) : p.L i ≤ p.μ * (weight p i : ℝ) ^ 2 := by
  have hLi : 0 ≤ p.L i := (hμ.le).trans (hL i)
  have hs := Real.sq_sqrt (div_nonneg hLi hμ.le)
  have hw : Real.sqrt (p.L i / p.μ) ≤ (weight p i : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈Real.sqrt (p.L i / p.μ)⌉₊)
  have hh : p.L i / p.μ ≤ (weight p i : ℝ) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (p.L i / p.μ), (Nat.cast_nonneg (weight p i) : (0 : ℝ) ≤ weight p i)]
  have h := (div_le_iff₀ hμ).mp hh
  nlinarith only [h]

lemma tuning (p : Params) (hμ : 0 < p.μ) :
    0 < tau p ∧ tau p < 1 ∧ 0 < eta p ∧
      eta p * p.μ * (1 - tau p) = tau p ∧
      eta p * tau p * p.μ * (totalWeight p : ℝ) ^ 2 ≤ 1 := by
  have hM : (1 : ℝ) ≤ totalWeight p := by exact_mod_cast totalWeight_pos p
  have hM0 : (0 : ℝ) < totalWeight p := lt_of_lt_of_le zero_lt_one hM
  have hD : 0 < 2 * (totalWeight p : ℝ) - 1 := by linarith
  refine ⟨by unfold tau; positivity, ?_, by unfold eta; positivity, ?_, ?_⟩
  · unfold tau
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (totalWeight p : ℝ))).mpr
    linarith
  · unfold eta tau
    field_simp
  · unfold eta tau
    have heq : 1 / (p.μ * (2 * (totalWeight p : ℝ) - 1)) *
        (1 / (2 * (totalWeight p : ℝ))) * p.μ * (totalWeight p : ℝ) ^ 2 =
        (totalWeight p : ℝ) / (2 * (2 * (totalWeight p : ℝ) - 1)) := by
      field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (2 * (totalWeight p : ℝ) - 1))).mpr
    linarith

lemma weight_le_two_sqrt (p : Params) (hμ : 0 < p.μ) (hL : ∀ i, p.μ ≤ p.L i)
    (i : Fin p.d) : (weight p i : ℝ) ≤ 2 * Real.sqrt (p.L i / p.μ) := by
  have hr : 1 ≤ p.L i / p.μ := (le_div_iff₀ hμ).mpr (by simpa using hL i)
  have hs := Real.sq_sqrt (show 0 ≤ p.L i / p.μ by linarith)
  have hs0 := Real.sqrt_nonneg (p.L i / p.μ)
  have hs1 : 1 ≤ Real.sqrt (p.L i / p.μ) := by nlinarith
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (p.L i / p.μ))
  have hw : (weight p i : ℝ) ≤ Real.sqrt (p.L i / p.μ) + 1 := by
    unfold weight
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) hc.le
  linarith

lemma totalWeight_le (p : Params) (hμ : 0 < p.μ) (hL : ∀ i, p.μ ≤ p.L i) :
    (totalWeight p : ℝ) ≤ 2 * ∑ i, Real.sqrt (p.L i / p.μ) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => weight_le_two_sqrt p hμ hL i)
  simpa [totalWeight, Finset.mul_sum] using h

end OracleTemplate.AcceleratedCoordinate
