import LongTails.Algorithms.PolynomialMixingSelection
import LongTails.Proofs.HeavyTailedMomentBounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace LongTails.Proofs.PolynomialMixingValidation

lemma chord_sum_bounds (n : ℕ) (value slope : ℕ → ℝ) (h : ℝ)
    (hleft : ∀ i < n, h * slope i ≤ value (i + 1) - value i)
    (hright : ∀ i < n, value (i + 1) - value i ≤ h * slope (i + 1)) :
    h * ∑ i ∈ Finset.range n, slope i ≤ value n - value 0 ∧
    value n - value 0 ≤ h * ∑ i ∈ Finset.range n, slope i + h * (slope n - slope 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hl, hr⟩ := ih (fun i hi => hleft i (Nat.lt_succ_of_lt hi))
      (fun i hi => hright i (Nat.lt_succ_of_lt hi))
    rw [Finset.sum_range_succ, mul_add]
    constructor
    · linarith [hleft n (Nat.lt_succ_self n)]
    · linarith only [hr, hright n (Nat.lt_succ_self n),
        mul_sub h (slope (n + 1)) (slope 0), mul_sub h (slope n) (slope 0)]

lemma chord_bias (n : ℕ) (value slope : ℕ → ℝ) (B : ℝ)
    (hleft : ∀ i < n, (n : ℝ)⁻¹ * slope i ≤ value (i + 1) - value i)
    (hright : ∀ i < n, value (i + 1) - value i ≤ (n : ℝ)⁻¹ * slope (i + 1))
    (hstart : -B ≤ slope 0) (hstop : slope n ≤ B) :
    |value n - value 0 - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, slope i| ≤ 2 * B / n := by
  obtain ⟨hl, hr⟩ := chord_sum_bounds n value slope _ hleft hright
  rw [abs_of_nonneg (sub_nonneg.mpr hl), div_eq_inv_mul]
  have hdiff : slope n - slope 0 ≤ 2 * B := by linarith
  linarith only [hr, mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (Nat.cast_nonneg n))]


open MeasureTheory LongTails.Setups.PolynomialMixingSubgradient
open LongTails.Algorithms.PolynomialMixingSelection
open scoped RealInnerProductSpace

variable {q : Params} {f : Space q → ℝ} {g : Point q → ℝ → Space q} {π : Measure ℝ}
  [IsProbabilityMeasure π]

lemma mean_norm (h : SubgradientOracle q f g π) (hp : 1 < q.p) (hG : 0 ≤ q.G)
    (x : Point q) : ‖∫ z, g x z ∂π‖ ≤ q.G := by
  have hi := HeavyTailedMomentBounds.integral_norm_le_root_moment hp
    (h.integrable x).aestronglyMeasurable (h.momentIntegrable x)
  apply (norm_integral_le_integral_norm _).trans (hi.trans ?_)
  have h₁ := Real.rpow_le_rpow (integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg (g x z)) _))
    (h.moment x) (show 0 ≤ 1 / q.p by positivity)
  rwa [← Real.rpow_mul hG, mul_one_div_cancel (by linarith : q.p ≠ 0), Real.rpow_one] at h₁

lemma objective_lipschitz (h : SubgradientOracle q f g π) (hp : 1 < q.p) (hG : 0 ≤ q.G)
    (x y : Point q) : |f x.val - f y.val| ≤ q.G * ‖x.val - y.val‖ := by
  have one (a b : Point q) : f a.val - f b.val ≤ q.G * ‖a.val - b.val‖ := by
    have hs := h.support a b
    rw [← neg_sub a.val b.val, inner_neg_right] at hs
    have hb := (real_inner_le_norm (∫ z, g a z ∂π) (a.val - b.val)).trans
      (mul_le_mul_of_nonneg_right (mean_norm h hp hG a) (norm_nonneg _))
    linarith
  have h' := one y x
  rw [norm_sub_rev] at h'
  exact abs_le.mpr ⟨by linarith, one x y⟩

lemma chordPoint_val (x : Point q) {n i : ℕ} (hi : i ≤ n) :
    (chordPoint q x n i).val = ((i : ℝ) / n) • x.val := by
  change OracleTemplate.clip q.R _ = _
  apply OracleTemplate.clip_eq_self
  have hx : ‖x.val‖ ≤ q.R := by simpa only [Domain, Metric.mem_closedBall, dist_zero_right] using x.property
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (i : ℝ) / n)]
  exact (mul_le_mul_of_nonneg_right (div_le_one_of_le₀ (by exact_mod_cast hi)
    (Nat.cast_nonneg n)) (norm_nonneg _)).trans (by simpa using hx)

lemma chord_oracle_bias (h : SubgradientOracle q f g π) (hp : 1 < q.p) (hG : 0 ≤ q.G)
    (x : Point q) {n : ℕ} (hn : 0 < n) :
    |f x.val - f 0 - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      ⟪∫ z, g (chordPoint q x n i) z ∂π, x.val⟫| ≤ 2 * (q.G * q.R) / n := by
  let pt := chordPoint q x n
  let slope := fun i => ⟪∫ z, g (pt i) z ∂π, x.val⟫
  have diff {i : ℕ} (hi : i < n) : (pt (i + 1)).val - (pt i).val = (n : ℝ)⁻¹ • x.val := by
    rw [chordPoint_val x (Nat.succ_le_of_lt hi), chordPoint_val x hi.le, ← sub_smul]
    congr 1
    push_cast
    ring
  have hs (i : ℕ) : |slope i| ≤ q.G * q.R := by
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (mean_norm h hp hG (pt i))
      (by simpa only [Domain, Metric.mem_closedBall, dist_zero_right] using x.property) (norm_nonneg _) hG)
  have hb := chord_bias n (fun i => f (pt i).val) slope (q.G * q.R) (fun i hi => by
    have h' := h.support (pt i) (pt (i + 1))
    rw [diff hi, real_inner_smul_right] at h'
    dsimp [slope]; linarith) (fun i hi => by
    have h' := h.support (pt (i + 1)) (pt i)
    rw [← neg_sub (pt (i + 1)).val (pt i).val, diff hi, inner_neg_right, real_inner_smul_right] at h'
    dsimp [slope]; linarith) (abs_le.mp (hs 0)).1 (abs_le.mp (hs n)).2
  have he := chordPoint_val x (le_refl n)
  have h₀ := chordPoint_val x (Nat.zero_le n)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simpa only [pt, he, h₀, div_self hn', Nat.cast_zero, zero_div, zero_smul, one_smul, slope] using hb

end LongTails.Proofs.PolynomialMixingValidation
