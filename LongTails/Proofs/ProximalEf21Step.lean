import LongTails.Proofs.ProximalEf21Tuning
import LongTails.Setups.StochasticProximalEf21
import Mathlib.Algebra.Module.NatInt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

section Geometry

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def modelDecrease (ψ : E → ℝ) (τ : ℝ) (x m z : E) : ℝ :=
  ψ x - ψ z - ⟪m, z - x⟫_ℝ - ‖z - x‖ ^ 2 / (2 * τ)

noncomputable def functionalEnergy (F ψ : E → ℝ)
    (μ τ : ℝ) (xstar x m z : E) : ℝ :=
  F x + ψ x - (F xstar + ψ xstar) -
    (ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ) / 8 +
    modelDecrease ψ τ x m z / (μ * τ)

lemma inner_self_eq (u : E) : ⟪u, u⟫_ℝ = ‖u‖ ^ 2 := by
  exact real_inner_self_eq_norm_sq u

lemma square_add (u v : E) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := by
  rw [← inner_self_eq, inner_add_left, inner_add_right, inner_add_right]
  rw [inner_self_eq, inner_self_eq, real_inner_comm v u]
  ring

lemma square_sub (u v : E) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := by
  rw [← inner_self_eq, inner_sub_left, inner_sub_right, inner_sub_right]
  rw [inner_self_eq, inner_self_eq, real_inner_comm v u]
  ring

lemma square_smul (a : ℝ) (u : E) :
    ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma square_add_smul (u v : E) (a : ℝ) :
    ‖u + a • v‖ ^ 2 =
      ‖u‖ ^ 2 + 2 * a * ⟪u, v⟫_ℝ + a ^ 2 * ‖v‖ ^ 2 := by
  rw [square_add, square_smul, real_inner_smul_right]
  ring

lemma square_sub_smul (u v : E) (a : ℝ) :
    ‖u - a • v‖ ^ 2 =
      ‖u‖ ^ 2 - 2 * a * ⟪u, v⟫_ℝ + a ^ 2 * ‖v‖ ^ 2 := by
  rw [square_sub, square_smul, real_inner_smul_right]
  ring

lemma twice_inner_young (a : ℝ) (ha : 0 < a) (u v : E) :
    2 * ⟪u, v⟫_ℝ ≤ a * ‖u‖ ^ 2 + a⁻¹ * ‖v‖ ^ 2 := by
  have h := sq_nonneg ‖a • u - v‖
  rw [square_sub, square_smul, real_inner_smul_left] at h
  apply (mul_le_mul_iff_of_pos_left ha).mp
  calc
    a * (2 * ⟪u, v⟫_ℝ) ≤ a ^ 2 * ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
      linarith only [h]
    _ = a * (a * ‖u‖ ^ 2 + a⁻¹ * ‖v‖ ^ 2) := by
      field_simp [ne_of_gt ha]

lemma inner_young (a : ℝ) (ha : 0 < a) (u v : E) :
    ⟪u, v⟫_ℝ ≤ a / 2 * ‖u‖ ^ 2 + 1 / (2 * a) * ‖v‖ ^ 2 := by
  have h := twice_inner_young a ha u v
  have heq : (1 : ℝ) / (2 * a) = a⁻¹ / 2 := by ring
  rw [heq]
  linarith

lemma neg_inner_young (a : ℝ) (ha : 0 < a) (u v : E) :
    -⟪u, v⟫_ℝ ≤ a / 2 * ‖u‖ ^ 2 + 1 / (2 * a) * ‖v‖ ^ 2 := by
  simpa only [inner_neg_right, norm_neg] using inner_young a ha u (-v)

lemma square_two (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := twice_inner_young 1 (by norm_num) u v
  norm_num at h
  rw [square_add]
  linarith

lemma square_three (u v w : E) :
    ‖u + v + w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have huv := twice_inner_young 1 (by norm_num) u v
  have huw := twice_inner_young 1 (by norm_num) u w
  have hvw := twice_inner_young 1 (by norm_num) v w
  norm_num at huv huw hvw
  rw [square_add, square_add, inner_add_left]
  linarith

lemma square_convex_combination (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (u v : E) :
    ‖(1 - a) • u + a • v‖ ^ 2 ≤ (1 - a) * ‖u‖ ^ 2 + a * ‖v‖ ^ 2 := by
  have hnonneg : 0 ≤ a * (1 - a) * ‖u - v‖ ^ 2 :=
    mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (sq_nonneg ‖u - v‖)
  have hid :
      (1 - a) * ‖u‖ ^ 2 + a * ‖v‖ ^ 2 - ‖(1 - a) • u + a • v‖ ^ 2 =
        a * (1 - a) * ‖u - v‖ ^ 2 := by
    rw [square_add, square_smul, square_smul,
      real_inner_smul_left, real_inner_smul_right, square_sub]
    ring
  exact sub_nonneg.mp (hid.symm ▸ hnonneg)

lemma complete_model_square (ψ : E → ℝ) {τ : ℝ} (hτ : τ ≠ 0)
    (x m z : E) :
    ψ z + ⟪m, z - x⟫_ℝ + ‖z - x‖ ^ 2 / (2 * τ) =
      ψ z + ‖z - (x - τ • m)‖ ^ 2 / (2 * τ) - τ / 2 * ‖m‖ ^ 2 := by
  have hz : z - (x - τ • m) = (z - x) + τ • m := by abel
  rw [hz, square_add_smul, real_inner_comm (z - x) m]
  field_simp [hτ]
  ring

lemma modelDecrease_completed_square (ψ : E → ℝ) {τ : ℝ}
    (hτ : τ ≠ 0) (x m z : E) :
    modelDecrease ψ τ x m z =
      ψ x + τ / 2 * ‖m‖ ^ 2 - ψ z -
        ‖z - (x - τ • m)‖ ^ 2 / (2 * τ) := by
  have h := complete_model_square ψ hτ x m z
  unfold modelDecrease
  linarith

lemma quadratic_lower_bound {τ : ℝ} (hτ : 0 < τ) (a u : E) :
    -τ / 2 * ‖a‖ ^ 2 ≤ ⟪a, u⟫_ℝ + ‖u‖ ^ 2 / (2 * τ) := by
  have h := sq_nonneg ‖u + τ • a‖
  rw [square_add_smul] at h
  rw [real_inner_comm a u] at h
  apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * τ by positivity)).mp
  have heq : (2 * τ) * (⟪a, u⟫_ℝ + ‖u‖ ^ 2 / (2 * τ)) =
      2 * τ * ⟪a, u⟫_ℝ + ‖u‖ ^ 2 := by
    field_simp [ne_of_gt hτ]
  rw [heq]
  linarith only [h]

lemma next_model_lower_bound (ψ : E → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (x y m mnext z znext : E)
    (hsupport : ψ z + ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ ≤ ψ znext) :
    ψ z + ⟪τ⁻¹ • (x - z) - m, y - z⟫_ℝ -
        τ / 2 * ‖mnext - m + τ⁻¹ • (x - z)‖ ^ 2 ≤
      ψ znext + ⟪mnext, znext - y⟫_ℝ + ‖znext - y‖ ^ 2 / (2 * τ) := by
  have hquad := quadratic_lower_bound hτ
    (mnext - m + τ⁻¹ • (x - z)) (znext - y)
  have hsplit :
      ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ + ⟪mnext, znext - y⟫_ℝ =
        ⟪τ⁻¹ • (x - z) - m, y - z⟫_ℝ +
          ⟪mnext - m + τ⁻¹ • (x - z), znext - y⟫_ℝ := by
    have hv : znext - z = (znext - y) + (y - z) := by abel
    rw [hv]
    simp only [inner_add_right, inner_add_left, inner_sub_left]
    ring
  linarith [hsplit]

lemma proximal_model_change (ψ : E → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (x y m mnext z znext : E)
    (hsupport : ψ z + ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ ≤ ψ znext) :
    modelDecrease ψ τ y mnext znext - modelDecrease ψ τ x m z ≤
      ψ y - ψ x - ⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
        ⟪x - z, mnext - m⟫_ℝ + τ / 2 * ‖mnext - m‖ ^ 2 := by
  have hmin := next_model_lower_bound ψ hτ x y m mnext z znext hsupport
  have hquad :
      τ / 2 * ‖mnext - m + τ⁻¹ • (x - z)‖ ^ 2 =
        τ / 2 * ‖mnext - m‖ ^ 2 +
          ⟪x - z, mnext - m⟫_ℝ + ‖x - z‖ ^ 2 / (2 * τ) := by
    rw [square_add_smul, real_inner_comm (mnext - m) (x - z)]
    field_simp [ne_of_gt hτ]
  have hv : y - z = (y - x) + (x - z) := by abel
  have hinner :
      ⟪τ⁻¹ • (x - z) - m, y - z⟫_ℝ =
        ⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          τ⁻¹ * ‖x - z‖ ^ 2 - ⟪m, x - z⟫_ℝ := by
    have hself :
        ⟪τ⁻¹ • (x - z) - m, x - z⟫_ℝ =
          τ⁻¹ * ‖x - z‖ ^ 2 - ⟪m, x - z⟫_ℝ := by
      rw [inner_sub_left, real_inner_smul_left, inner_self_eq]
    rw [hv, inner_add_right, hself]
    ring
  have hneg : ⟪m, z - x⟫_ℝ = -⟪m, x - z⟫_ℝ := by
    rw [show z - x = -(x - z) by abel, inner_neg_right]
  have hnorm : ‖z - x‖ ^ 2 = ‖x - z‖ ^ 2 := by rw [norm_sub_rev]
  have hinv : τ⁻¹ * ‖x - z‖ ^ 2 = 2 * (‖x - z‖ ^ 2 / (2 * τ)) := by ring
  rw [hquad, hinner] at hmin
  unfold modelDecrease
  rw [hneg, hnorm]
  linarith [hinv]

lemma modelDecrease_nonnegative (ψ : E → ℝ) (τ : ℝ) (x m z : E)
    (hmin : ψ z + ⟪m, z - x⟫_ℝ + ‖z - x‖ ^ 2 / (2 * τ) ≤ ψ x) :
    0 ≤ modelDecrease ψ τ x m z := by
  unfold modelDecrease
  linarith

lemma modelDecrease_upper_from_support (ψ : E → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (x y m z η : E)
    (hsupport : ψ y + ⟪η, z - y⟫_ℝ ≤ ψ z) :
    modelDecrease ψ τ x m z ≤
      ψ x - ψ y - ⟪η, x - y⟫_ℝ + τ / 2 * ‖m + η‖ ^ 2 := by
  have hq := quadratic_lower_bound hτ (m + η) (z - x)
  have hv : z - y = (z - x) + (x - y) := by abel
  rw [hv, inner_add_right] at hsupport
  rw [inner_add_left] at hq
  unfold modelDecrease
  linarith

lemma subgradient_monotonicity (ψ : E → ℝ) (x y ηx ηy : E)
    (hxy : ψ x + ⟪ηx, y - x⟫_ℝ ≤ ψ y)
    (hyx : ψ y + ⟪ηy, x - y⟫_ℝ ≤ ψ x) :
    0 ≤ ⟪ηx - ηy, x - y⟫_ℝ := by
  have hv : y - x = -(x - y) := by abel
  rw [hv, inner_neg_right] at hxy
  rw [inner_sub_left]
  linarith

lemma proximal_displacement_identity {γ τ : ℝ} (hγ : γ ≠ 0) (hτ : τ ≠ 0)
    (x y z : E) :
    y - z = (τ - γ) • (γ⁻¹ • (x - y)) -
      τ • (γ⁻¹ • (x - y) - τ⁻¹ • (x - z)) := by
  have hcoeff : (τ - γ) * γ⁻¹ = τ * γ⁻¹ - 1 := by
    rw [sub_mul, mul_inv_cancel₀ hγ]
  symm
  calc
    (τ - γ) • (γ⁻¹ • (x - y)) -
        τ • (γ⁻¹ • (x - y) - τ⁻¹ • (x - z)) =
        ((τ - γ) * γ⁻¹) • (x - y) -
          (τ * γ⁻¹) • (x - y) + (τ * τ⁻¹) • (x - z) := by
      simp only [smul_sub, smul_smul]
      abel
    _ = y - z := by
      rw [hcoeff, sub_smul, one_smul, mul_inv_cancel₀ hτ, one_smul]
      abel

lemma proximal_displacement_comparison {γ τ : ℝ}
    (hγ : 0 < γ) (hτγ : γ < τ) (x y z m v : E)
    (hmono : 0 ≤
      ⟪γ⁻¹ • (x - y) - v - (τ⁻¹ • (x - z) - m), y - z⟫_ℝ) :
    τ / (τ - γ) *
        (‖γ⁻¹ • (x - y) - τ⁻¹ • (x - z)‖ ^ 2 -
          ⟪v - m, γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ) ≤
      ⟪γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m),
        γ⁻¹ • (x - y)⟫_ℝ := by
  have hτ : 0 < τ := lt_trans hγ hτγ
  have hden : 0 < τ - γ := sub_pos.mpr hτγ
  have hv : γ⁻¹ • (x - y) - v - (τ⁻¹ • (x - z) - m) =
      γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m) := by abel
  rw [hv, proximal_displacement_identity (ne_of_gt hγ) (ne_of_gt hτ) x y z,
    inner_sub_right] at hmono
  rw [real_inner_smul_right _ (γ⁻¹ • (x - y)) (τ - γ),
    real_inner_smul_right _
      (γ⁻¹ • (x - y) - τ⁻¹ • (x - z)) τ] at hmono
  have hi :
      ⟪γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m),
        γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ =
      ‖γ⁻¹ • (x - y) - τ⁻¹ • (x - z)‖ ^ 2 -
        ⟪v - m, γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ := by
    rw [inner_sub_left, inner_self_eq]
  rw [hi] at hmono
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  linarith only [hmono]

lemma mixed_proximal_products {γ μ τ : ℝ}
    (hγ : 0 < γ) (hμ : 0 < μ) (hτγ : γ < τ)
    (a r rτ c : E)
    (hmono : τ / (τ - γ) * (‖r - rτ‖ ^ 2 - ⟪c, r - rτ⟫_ℝ) ≤
      ⟪r - rτ - c, r⟫_ℝ) :
    -γ * ⟪a, r - rτ⟫_ℝ - γ / (μ * τ) * ⟪r - rτ - c, r⟫_ℝ ≤
      -γ / (2 * μ * (τ - γ)) * ‖r - rτ‖ ^ 2 +
        γ * μ * (τ - γ) * ‖a‖ ^ 2 +
        γ / (μ * (τ - γ)) * ‖c‖ ^ 2 := by
  have hτ : 0 < τ := lt_trans hγ hτγ
  have hd : 0 < τ - γ := sub_pos.mpr hτγ
  have hscaled := mul_le_mul_of_nonneg_left hmono
    (show 0 ≤ γ / (μ * τ) by positivity)
  have hcancel : γ / (μ * τ) * (τ / (τ - γ)) = γ / (μ * (τ - γ)) := by
    field_simp [ne_of_gt hμ, ne_of_gt hτ, ne_of_gt hd]
  have hmono' :
      γ / (μ * (τ - γ)) * (‖r - rτ‖ ^ 2 - ⟪c, r - rτ⟫_ℝ) ≤
        γ / (μ * τ) * ⟪r - rτ - c, r⟫_ℝ := by
    simpa only [← mul_assoc, hcancel] using hscaled
  have hy₁ := neg_inner_young (1 / (2 * μ * (τ - γ)))
    (by positivity) (r - rτ) a
  rw [real_inner_comm a (r - rτ)] at hy₁
  have hc₁ : (1 / (2 * μ * (τ - γ)) : ℝ) / 2 =
      1 / (4 * μ * (τ - γ)) := by
    rw [div_div,
      show (2 * μ * (τ - γ)) * 2 = 4 * μ * (τ - γ) by ring]
  have hc₂ : (1 : ℝ) / (2 * (1 / (2 * μ * (τ - γ)))) =
      μ * (τ - γ) := by
    field_simp [ne_of_gt hμ, ne_of_gt hd]
  rw [hc₁, hc₂] at hy₁
  have hy₁' := mul_le_mul_of_nonneg_left hy₁ (le_of_lt hγ)
  have hy₂ := inner_young (1 / 2 : ℝ) (by norm_num) (r - rτ) c
  norm_num at hy₂
  rw [real_inner_comm c (r - rτ)] at hy₂
  have hy₂' := mul_le_mul_of_nonneg_left hy₂
    (show 0 ≤ γ / (μ * (τ - γ)) by positivity)
  have hy₁'' :
      -γ * ⟪a, r - rτ⟫_ℝ ≤
        (γ / (μ * (τ - γ))) / 4 * ‖r - rτ‖ ^ 2 +
          γ * μ * (τ - γ) * ‖a‖ ^ 2 := by
    convert hy₁' using 1 <;>
      field_simp [ne_of_gt hμ, ne_of_gt hd]
  have hy₂'' :
      γ / (μ * (τ - γ)) * ⟪c, r - rτ⟫_ℝ ≤
        (γ / (μ * (τ - γ))) / 4 * ‖r - rτ‖ ^ 2 +
          γ / (μ * (τ - γ)) * ‖c‖ ^ 2 := by
    convert hy₂' using 1
    ring
  have hhalf : -γ / (2 * μ * (τ - γ)) =
      -(γ / (μ * (τ - γ))) / 2 := by
    rw [← neg_div, div_div,
      show (μ * (τ - γ)) * 2 = 2 * μ * (τ - γ) by ring]
  rw [hhalf]
  linarith only [hmono', hy₁'', hy₂'']

lemma objective_cross_lower_bound (F ψ : E → ℝ) (μ γ : ℝ)
    (x y xstar g m v b : E)
    (hstrong : F y + ⟪g, xstar - y⟫_ℝ + μ / 2 * ‖xstar - y‖ ^ 2 ≤ F xstar) :
    F y + ψ y - (F xstar + ψ xstar) + μ / 2 * ‖y - xstar‖ ^ 2 +
      (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) -
      ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ + ⟪y - xstar, v - m + b⟫_ℝ ≤
        ⟪y - xstar, g - m + b⟫_ℝ := by
  have hv : xstar - y = -(y - xstar) := by abel
  rw [hv, inner_neg_right, norm_neg, real_inner_comm (y - xstar) g] at hstrong
  have hprox :
      ⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ =
        ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ - ⟪y - xstar, v⟫_ℝ := by
    rw [real_inner_comm (y - xstar) (γ⁻¹ • (x - y) - v), inner_sub_right]
  have herror :
      ⟪y - xstar, v - m + b⟫_ℝ =
        ⟪y - xstar, v⟫_ℝ - ⟪y - xstar, m⟫_ℝ + ⟪y - xstar, b⟫_ℝ := by
    rw [inner_add_right, inner_sub_right]
  have hgrad :
      ⟪y - xstar, g - m + b⟫_ℝ =
        ⟪y - xstar, g⟫_ℝ - ⟪y - xstar, m⟫_ℝ + ⟪y - xstar, b⟫_ℝ := by
    rw [inner_add_right, inner_sub_right]
  rw [hprox, herror, hgrad]
  linarith only [hstrong]

lemma subgradient_remainders_nonnegative (ψ : E → ℝ) (x y xstar η : E)
    (hx : ψ y + ⟪η, x - y⟫_ℝ ≤ ψ x)
    (hstar : ψ y + ⟪η, xstar - y⟫_ℝ ≤ ψ xstar) :
    0 ≤ ψ x - ψ y - ⟪η, x - y⟫_ℝ ∧
      0 ≤ ⟪η, y - xstar⟫_ℝ - ψ y + ψ xstar := by
  have hv : xstar - y = -(y - xstar) := by abel
  rw [hv, inner_neg_right] at hstar
  constructor <;> linarith

lemma model_lower_from_segment (ψ : E → ℝ) {μ τ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (x xstar m z : E)
    (hconvex : ψ ((1 - μ * τ) • x + (μ * τ) • xstar) ≤
      (1 - μ * τ) * ψ x + μ * τ * ψ xstar)
    (hmin : ψ z + ⟪m, z - x⟫_ℝ + ‖z - x‖ ^ 2 / (2 * τ) ≤
      ψ ((1 - μ * τ) • x + (μ * τ) • xstar) +
        ⟪m, (1 - μ * τ) • x + (μ * τ) • xstar - x⟫_ℝ +
        ‖(1 - μ * τ) • x + (μ * τ) • xstar - x‖ ^ 2 / (2 * τ)) :
    ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ - μ / 2 * ‖x - xstar‖ ^ 2 ≤
      modelDecrease ψ τ x m z / (μ * τ) := by
  have hv : (1 - μ * τ) • x + (μ * τ) • xstar - x =
      -(μ * τ) • (x - xstar) := by
    simp only [sub_smul, one_smul, smul_sub, neg_smul]
    abel
  rw [hv, real_inner_smul_right, square_smul] at hmin
  have hq : (-(μ * τ)) ^ 2 * ‖x - xstar‖ ^ 2 / (2 * τ) =
      μ * τ * (μ / 2 * ‖x - xstar‖ ^ 2) := by
    field_simp [ne_of_gt hτ]
  rw [hq] at hmin
  apply (le_div_iff₀ (mul_pos hμ hτ)).2
  unfold modelDecrease
  linarith only [hconvex, hmin]

lemma functionalEnergy_nonnegative (F ψ : E → ℝ) {μ τ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (xstar x m z : E)
    (hgap : 0 ≤ F x + ψ x - (F xstar + ψ xstar))
    (hstronggap : μ / 2 * ‖x - xstar‖ ^ 2 ≤ F x + ψ x - (F xstar + ψ xstar))
    (hmodel : 0 ≤ modelDecrease ψ τ x m z)
    (hlower : ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ -
      μ / 2 * ‖x - xstar‖ ^ 2 ≤ modelDecrease ψ τ x m z / (μ * τ)) :
    (7 / 8 : ℝ) * (F x + ψ x - (F xstar + ψ xstar) +
      modelDecrease ψ τ x m z / (μ * τ)) ≤
        functionalEnergy F ψ μ τ xstar x m z ∧
      0 ≤ functionalEnergy F ψ μ τ xstar x m z := by
  have hscaledmodel : 0 ≤ modelDecrease ψ τ x m z / (μ * τ) := by positivity
  have hbound : ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ ≤
      F x + ψ x - (F xstar + ψ xstar) + modelDecrease ψ τ x m z / (μ * τ) := by
    linarith
  constructor
  · unfold functionalEnergy
    linarith
  · unfold functionalEnergy
    linarith

end LongTails.Proofs.ProximalEf21Geometry


end Geometry


section Averages

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21Averages

open LongTails.Proofs.ProximalEf21Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def workerMean {n : ℕ} (u : Fin n → E) : E :=
  (n : ℝ)⁻¹ • ∑ i, u i

noncomputable def weightedSquare {n : ℕ} (w : Fin n → ℝ) (u : Fin n → E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, w i * ‖u i‖ ^ 2

lemma workerMean_add {n : ℕ} (u v : Fin n → E) :
    workerMean (fun i => u i + v i) = workerMean u + workerMean v := by
  simp only [workerMean, Finset.sum_add_distrib, smul_add]

lemma workerMean_sub {n : ℕ} (u v : Fin n → E) :
    workerMean (fun i => u i - v i) = workerMean u - workerMean v := by
  simp only [workerMean, Finset.sum_sub_distrib, smul_sub]

lemma workerMean_smul {n : ℕ} (a : ℝ) (u : Fin n → E) :
    workerMean (fun i => a • u i) = a • workerMean u := by
  simp only [workerMean, ← Finset.smul_sum, smul_smul]
  rw [mul_comm]

lemma workerMean_const {n : ℕ} (hn : 0 < n) (u : E) :
    workerMean (fun _ : Fin n => u) = u := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [workerMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ n u, smul_smul, inv_mul_cancel₀ hnR, one_smul]

lemma workerMean_momentum {n : ℕ} (hn : 0 < n) (α : ℝ)
    (m g ζ : Fin n → E) (b : E) :
    workerMean (fun i => (1 - α) • m i + α • (g i + b + ζ i)) =
      workerMean m + α • (workerMean g - workerMean m + b + workerMean ζ) := by
  calc
    workerMean (fun i => (1 - α) • m i + α • (g i + b + ζ i)) =
        (1 - α) • workerMean m + α • (workerMean g + b + workerMean ζ) := by
      rw [workerMean_add, workerMean_smul, workerMean_smul,
        workerMean_add, workerMean_add, workerMean_const hn]
    _ = workerMean m + α • (workerMean g - workerMean m + b + workerMean ζ) := by
      simp only [sub_smul, one_smul, smul_add, smul_sub]
      abel

lemma weightedSquare_nonnegative {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (u : Fin n → E) : 0 ≤ weightedSquare w u := by
  unfold weightedSquare
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg ‖u i‖))

lemma weighted_sum_le {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (u v : Fin n → ℝ) (huv : ∀ i, u i ≤ v i) :
    (n : ℝ)⁻¹ * ∑ i, w i * u i ≤ (n : ℝ)⁻¹ * ∑ i, w i * v i := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (huv i) (hw i))

lemma weighted_constant_le {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∀ i, w i ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    (n : ℝ)⁻¹ * ∑ i, w i * a ≤ a := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  calc
    (n : ℝ)⁻¹ * ∑ i, w i * a ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n, a := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      exact Finset.sum_le_sum (fun i _ => by
        simpa using mul_le_mul_of_nonneg_right (hw i) ha)
    _ = a := by simp [hnR]

end LongTails.Proofs.ProximalEf21Averages


end Averages


section WeightedErrors

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21WeightedErrors

open LongTails.Proofs.ProximalEf21Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weighted_cauchy_schwarz {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (u : ι → E) :
    ‖∑ i, u i‖ ^ 2 ≤ (∑ i, (w i)⁻¹) * ∑ i, w i * ‖u i‖ ^ 2 := by
  classical
  let a : ℝ := ∑ i, (w i)⁻¹
  have ha : 0 < a := by
    exact Finset.sum_pos (fun i _ => inv_pos.mpr (hw i)) Finset.univ_nonempty
  let z : E := a⁻¹ • ∑ i, u i
  have hs :
      2 * ⟪∑ i, u i, z⟫_ℝ ≤
        (∑ i, w i * ‖u i‖ ^ 2) + a * ‖z‖ ^ 2 := by
    calc
      2 * ⟪∑ i, u i, z⟫_ℝ = ∑ i, 2 * ⟪u i, z⟫_ℝ := by
        simp only [sum_inner, Finset.mul_sum]
      _ ≤ ∑ i, (w i * ‖u i‖ ^ 2 + (w i)⁻¹ * ‖z‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact twice_inner_young (w i) (hw i) (u i) z
      _ = (∑ i, w i * ‖u i‖ ^ 2) + a * ‖z‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, a]
  have hiz : ⟪∑ i, u i, z⟫_ℝ = a⁻¹ * ‖∑ i, u i‖ ^ 2 := by
    simp only [z, real_inner_smul_right, inner_self_eq]
  have hnz : ‖z‖ ^ 2 = (a⁻¹) ^ 2 * ‖∑ i, u i‖ ^ 2 := by
    exact square_smul a⁻¹ (∑ i, u i)
  rw [hiz, hnz] at hs
  have hbase :
      2 * a⁻¹ * ‖∑ i, u i‖ ^ 2 - a * ((a⁻¹) ^ 2 * ‖∑ i, u i‖ ^ 2) ≤
        ∑ i, w i * ‖u i‖ ^ 2 := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hbase (le_of_lt ha)
  have hcancel :
      a * (2 * a⁻¹ * ‖∑ i, u i‖ ^ 2 -
        a * ((a⁻¹) ^ 2 * ‖∑ i, u i‖ ^ 2)) = ‖∑ i, u i‖ ^ 2 := by
    field_simp [ne_of_gt ha]
    ring
  rw [hcancel] at hscaled
  exact hscaled

lemma weighted_cauchy_schwarz_mean {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (u : Fin n → E) :
    ‖(n : ℝ)⁻¹ • ∑ i, u i‖ ^ 2 ≤
      ((n : ℝ)⁻¹ * ∑ i, (w i)⁻¹) *
        ((n : ℝ)⁻¹ * ∑ i, w i * ‖u i‖ ^ 2) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have h := weighted_cauchy_schwarz w hw u
  rw [square_smul]
  have hs := mul_le_mul_of_nonneg_left h (sq_nonneg ((n : ℝ)⁻¹))
  calc
    (n : ℝ)⁻¹ ^ 2 * ‖∑ i, u i‖ ^ 2 ≤
        (n : ℝ)⁻¹ ^ 2 * ((∑ i, (w i)⁻¹) * ∑ i, w i * ‖u i‖ ^ 2) := hs
    _ = ((n : ℝ)⁻¹ * ∑ i, (w i)⁻¹) *
        ((n : ℝ)⁻¹ * ∑ i, w i * ‖u i‖ ^ 2) := by ring

lemma weight_properties {M l : ℝ} (hM : 0 < M) (hl : 0 ≤ l) :
    0 < M / (M + l) ∧ M / (M + l) ≤ 1 ∧
      M / (M + l) * l ≤ M ∧ (M / (M + l))⁻¹ = 1 + l / M := by
  have hden : 0 < M + l := by linarith
  refine ⟨div_pos hM hden, ?_, ?_, ?_⟩
  · exact (div_le_one hden).2 (by linarith)
  · apply (mul_le_mul_iff_of_pos_right hden).mp
    have heq : M / (M + l) * l * (M + l) = M * l := by
      field_simp [ne_of_gt hden]
    rw [heq]
    nlinarith [sq_nonneg M]
  · field_simp [ne_of_gt hM, ne_of_gt hden]

lemma inverse_weight_average {n : ℕ} (hn : 0 < n)
    {M : ℝ} (hM : 0 < M) (l : Fin n → ℝ)
    (hl : ∀ i, 0 ≤ l i)
    (hmean : (n : ℝ)⁻¹ * ∑ i, l i ≤ M) :
    (n : ℝ)⁻¹ * ∑ i, (M / (M + l i))⁻¹ ≤ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hid :
      (n : ℝ)⁻¹ * ∑ i, (M / (M + l i))⁻¹ =
        1 + ((n : ℝ)⁻¹ * ∑ i, l i) / M := by
    simp_rw [(weight_properties hM (hl _)).2.2.2]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, ← Finset.sum_div]
    field_simp [ne_of_gt hnR, ne_of_gt hM]
  rw [hid]
  have hq : ((n : ℝ)⁻¹ * ∑ i, l i) / M ≤ 1 :=
    (div_le_one hM).2 hmean
  linarith

lemma aggregate_error_bound {n : ℕ} (hn : 0 < n)
    {M : ℝ} (hM : 0 < M) (l : Fin n → ℝ)
    (hl : ∀ i, 0 ≤ l i)
    (hmean : (n : ℝ)⁻¹ * ∑ i, l i ≤ M) (u : Fin n → E) :
    ‖(n : ℝ)⁻¹ • ∑ i, u i‖ ^ 2 ≤
      2 * ((n : ℝ)⁻¹ * ∑ i, M / (M + l i) * ‖u i‖ ^ 2) := by
  have hw : ∀ i, 0 < M / (M + l i) := fun i => (weight_properties hM (hl i)).1
  have hcs := weighted_cauchy_schwarz_mean hn (fun i => M / (M + l i)) hw u
  have hinv := inverse_weight_average hn hM l hl hmean
  have hsum : 0 ≤ (n : ℝ)⁻¹ * ∑ i, M / (M + l i) * ‖u i‖ ^ 2 := by
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (hw i)) (sq_nonneg ‖u i‖)
  exact hcs.trans (mul_le_mul_of_nonneg_right hinv hsum)

lemma weighted_local_interpolation {n : ℕ} (hn : 0 < n)
    {M gap : ℝ} (hM : 0 < M)
    (l d q : Fin n → ℝ) (hl : ∀ i, 0 ≤ l i) (hd : ∀ i, 0 ≤ d i)
    (hlocal : ∀ i, q i ≤ 2 * l i * d i)
    (hgap : (n : ℝ)⁻¹ * ∑ i, d i ≤ gap) :
    (n : ℝ)⁻¹ * ∑ i, M / (M + l i) * q i ≤ 2 * M * gap := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoint : ∀ i, M / (M + l i) * q i ≤ 2 * M * d i := by
    intro i
    obtain ⟨hw, _, hwl, _⟩ := weight_properties hM (hl i)
    have h₁ := mul_le_mul_of_nonneg_left (hlocal i) (le_of_lt hw)
    have h₂ := mul_le_mul_of_nonneg_right hwl (hd i)
    nlinarith
  calc
    (n : ℝ)⁻¹ * ∑ i, M / (M + l i) * q i ≤
        (n : ℝ)⁻¹ * ∑ i, 2 * M * d i := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hnR))
      exact Finset.sum_le_sum (fun i hi => hpoint i)
    _ = 2 * M * ((n : ℝ)⁻¹ * ∑ i, d i) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * M * gap := mul_le_mul_of_nonneg_left hgap (by positivity)

lemma weighted_variance_bound {n : ℕ} {M variance : ℝ}
    (hM : 0 < M) (hvariance : 0 ≤ variance)
    (l noise : Fin n → ℝ) (hl : ∀ i, 0 ≤ l i)
    (hnoise : ∀ i, noise i ≤ variance) :
    (n : ℝ)⁻¹ * ∑ i, M / (M + l i) * noise i ≤ variance := by
  by_cases hn : n = 0
  · subst n
    simpa using hvariance
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpoint : ∀ i, M / (M + l i) * noise i ≤ variance := by
    intro i
    obtain ⟨hw, hw1, _, _⟩ := weight_properties hM (hl i)
    calc
      M / (M + l i) * noise i ≤ M / (M + l i) * variance :=
        mul_le_mul_of_nonneg_left (hnoise i) (le_of_lt hw)
      _ ≤ 1 * variance := mul_le_mul_of_nonneg_right hw1 hvariance
      _ = variance := one_mul _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (le_of_lt hnR))
  simpa [ne_of_gt hnR] using hm

lemma momentum_square_bound (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (m g gstar b : E) :
    ‖((1 - α) • m + α • (g + b)) - gstar‖ ^ 2 ≤
      (1 - α) * ‖m - gstar‖ ^ 2 + 2 * α * ‖g - gstar‖ ^ 2 +
        2 * α * ‖b‖ ^ 2 := by
  have hv : ((1 - α) • m + α • (g + b)) - gstar =
      (1 - α) • (m - gstar) + α • ((g - gstar) + b) := by
    simp only [smul_sub, smul_add, sub_smul, one_smul]
    abel
  rw [hv]
  have h₁ := square_convex_combination α hα hα1 (m - gstar) ((g - gstar) + b)
  have h₂ := mul_le_mul_of_nonneg_left (square_two (g - gstar) b) hα
  nlinarith [h₁, h₂]

lemma compressor_split (δ α : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (u z : E) :
    (1 - δ) * ‖u + α • z‖ ^ 2 ≤
      (1 - δ / 2) * ‖u‖ ^ 2 + 2 * α ^ 2 / δ * ‖z‖ ^ 2 := by
  have hy := twice_inner_young (δ / 2) (by positivity) u (α • z)
  rw [square_smul] at hy
  have hinv : (δ / 2)⁻¹ = 2 / δ := by
    field_simp [ne_of_gt hδ]
  rw [hinv] at hy
  have hbase : ‖u + α • z‖ ^ 2 ≤
      (1 + δ / 2) * ‖u‖ ^ 2 + (1 + 2 / δ) * α ^ 2 * ‖z‖ ^ 2 := by
    rw [square_add, square_smul]
    calc
      ‖u‖ ^ 2 + 2 * ⟪u, α • z⟫_ℝ + α ^ 2 * ‖z‖ ^ 2 ≤
          ‖u‖ ^ 2 + (δ / 2 * ‖u‖ ^ 2 + 2 / δ * (α ^ 2 * ‖z‖ ^ 2)) +
            α ^ 2 * ‖z‖ ^ 2 :=
        add_le_add (add_le_add le_rfl hy) le_rfl
      _ = (1 + δ / 2) * ‖u‖ ^ 2 + (1 + 2 / δ) * α ^ 2 * ‖z‖ ^ 2 := by
        ring
  have hc₁ : (1 - δ) * (1 + δ / 2) ≤ 1 - δ / 2 := by
    nlinarith only [sq_nonneg δ]
  have hc₂ : (1 - δ) * (1 + 2 / δ) ≤ 2 / δ := by
    have hid : (1 - δ) * (1 + 2 / δ) = 2 / δ - (1 + δ) := by
      field_simp [ne_of_gt hδ]
      ring
    rw [hid]
    linarith only [hδ]
  have ht₁ := mul_le_mul_of_nonneg_right hc₁ (sq_nonneg ‖u‖)
  have ht₂ := mul_le_mul_of_nonneg_right hc₂
    (mul_nonneg (sq_nonneg α) (sq_nonneg ‖z‖))
  calc
    (1 - δ) * ‖u + α • z‖ ^ 2 ≤
        (1 - δ) * ((1 + δ / 2) * ‖u‖ ^ 2 +
          (1 + 2 / δ) * α ^ 2 * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr hδ1)
    _ = ((1 - δ) * (1 + δ / 2)) * ‖u‖ ^ 2 +
        ((1 - δ) * (1 + 2 / δ)) * (α ^ 2 * ‖z‖ ^ 2) := by ring
    _ ≤ (1 - δ / 2) * ‖u‖ ^ 2 + (2 / δ) * (α ^ 2 * ‖z‖ ^ 2) :=
      add_le_add ht₁ ht₂
    _ = (1 - δ / 2) * ‖u‖ ^ 2 + 2 * α ^ 2 / δ * ‖z‖ ^ 2 := by ring

lemma compression_square_bound (δ α : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (m v g gstar b : E) :
    (1 - δ) * ‖m - v + α • (g - m + b)‖ ^ 2 ≤
      (1 - δ / 2) * ‖v - m‖ ^ 2 +
        6 * α ^ 2 / δ * (‖m - gstar‖ ^ 2 + ‖g - gstar‖ ^ 2 + ‖b‖ ^ 2) := by
  have hs := compressor_split δ α hδ hδ1 (m - v) (g - m + b)
  have hv : g - m + b = -(m - gstar) + (g - gstar) + b := by abel
  have ht : ‖g - m + b‖ ^ 2 ≤
      3 * (‖m - gstar‖ ^ 2 + ‖g - gstar‖ ^ 2 + ‖b‖ ^ 2) := by
    rw [hv]
    simpa only [norm_neg] using square_three (-(m - gstar)) (g - gstar) b
  rw [norm_sub_rev m v] at hs
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ 2 * α ^ 2 / δ by positivity)
  calc
    (1 - δ) * ‖m - v + α • (g - m + b)‖ ^ 2 ≤
        (1 - δ / 2) * ‖v - m‖ ^ 2 + 2 * α ^ 2 / δ * ‖g - m + b‖ ^ 2 := hs
    _ ≤ (1 - δ / 2) * ‖v - m‖ ^ 2 +
        2 * α ^ 2 / δ * (3 * (‖m - gstar‖ ^ 2 + ‖g - gstar‖ ^ 2 + ‖b‖ ^ 2)) :=
      add_le_add le_rfl hm
    _ = (1 - δ / 2) * ‖v - m‖ ^ 2 +
        6 * α ^ 2 / δ * (‖m - gstar‖ ^ 2 + ‖g - gstar‖ ^ 2 + ‖b‖ ^ 2) := by ring

end LongTails.Proofs.ProximalEf21WeightedErrors


end WeightedErrors


section ConvexAnalysis

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21ConvexAnalysis

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21WeightedErrors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma nonpositive_of_segment_bounds {a c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ 1 → a ≤ t * c) : a ≤ 0 := by
  by_contra hnot
  have ha : 0 < a := lt_of_not_ge hnot
  have hden : 0 < 2 * (c + a) := by positivity
  have ht : 0 < a / (2 * (c + a)) := div_pos ha hden
  have ht1 : a / (2 * (c + a)) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have h := hbound (a / (2 * (c + a))) ht ht1
  have hm := mul_le_mul_of_nonneg_right h (le_of_lt hden)
  have heq : a / (2 * (c + a)) * c * (2 * (c + a)) = a * c := by
    field_simp [ne_of_gt hden]
  rw [heq] at hm
  nlinarith [mul_nonneg hc (le_of_lt ha), sq_pos_of_pos ha]

lemma proximal_supporting_affine (D : Set E) (ψ : E → ℝ)
    (hψ : ConvexOn ℝ D ψ) {τ : ℝ} (hτ : 0 < τ) (u p : E)
    (hp : p ∈ D)
    (hmin : ∀ z ∈ D,
      ψ p + ‖p - u‖ ^ 2 / (2 * τ) ≤ ψ z + ‖z - u‖ ^ 2 / (2 * τ)) :
    ∀ z ∈ D, ψ p + ⟪τ⁻¹ • (u - p), z - p⟫_ℝ ≤ ψ z := by
  intro z hz
  have hmain : ψ p + ⟪τ⁻¹ • (u - p), z - p⟫_ℝ - ψ z ≤ 0 := by
    apply nonpositive_of_segment_bounds
      (c := ‖z - p‖ ^ 2 / (2 * τ)) (by positivity)
    intro t ht ht1
    have ht0 : 0 ≤ t := le_of_lt ht
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsum : (1 - t) + t = 1 := by ring
    have hmem := hψ.1 hp hz h1t ht0 hsum
    have hconv := hψ.2 hp hz h1t ht0 hsum
    simp only [smul_eq_mul] at hconv
    have hprox := hmin ((1 - t) • p + t • z) hmem
    have hv : (1 - t) • p + t • z - u = (p - u) + t • (z - p) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [hv, square_add_smul] at hprox
    have hnormterm :
        (‖p - u‖ ^ 2 + 2 * t * ⟪p - u, z - p⟫_ℝ +
          t ^ 2 * ‖z - p‖ ^ 2) / (2 * τ) =
        ‖p - u‖ ^ 2 / (2 * τ) +
          t / τ * ⟪p - u, z - p⟫_ℝ + t ^ 2 * ‖z - p‖ ^ 2 / (2 * τ) := by
      ring
    rw [hnormterm] at hprox
    have hip : ⟪τ⁻¹ • (u - p), z - p⟫_ℝ =
        -τ⁻¹ * ⟪p - u, z - p⟫_ℝ := by
      rw [real_inner_smul_left,
        show u - p = -(p - u) by abel, inner_neg_left]
      ring
    rw [hip]
    apply (mul_le_mul_iff_of_pos_left ht).mp
    apply sub_nonpos.mp
    calc
      t * (ψ p + -τ⁻¹ * ⟪p - u, z - p⟫_ℝ - ψ z) -
          t * (t * (‖z - p‖ ^ 2 / (2 * τ))) =
        (ψ p + ‖p - u‖ ^ 2 / (2 * τ)) -
          ((1 - t) * ψ p + t * ψ z +
            (‖p - u‖ ^ 2 / (2 * τ) +
              t / τ * ⟪p - u, z - p⟫_ℝ +
              t ^ 2 * ‖z - p‖ ^ 2 / (2 * τ))) := by
        simp only [div_eq_mul_inv]
        ring
      _ ≤ 0 := sub_nonpos.mpr (hprox.trans (add_le_add hconv le_rfl))
  linarith only [hmain]

lemma smooth_convex_interpolation (f : E → ℝ) (g : E → E)
    {L : ℝ} (hL : 0 < L)
    (hconvex : ∀ x y, f x + ⟪g x, y - x⟫_ℝ ≤ f y)
    (hsmooth : ∀ x y,
      f y ≤ f x + ⟪g x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (x y : E) :
    ‖g x - g y‖ ^ 2 ≤
      2 * L * (f x - f y - ⟪g y, x - y⟫_ℝ) := by
  let z := x - L⁻¹ • (g x - g y)
  have hlow := hconvex y z
  have hupp := hsmooth x z
  have hzx : z - x = -(L⁻¹) • (g x - g y) := by dsimp [z]; module
  have hzy : z - y = (x - y) - L⁻¹ • (g x - g y) := by dsimp [z]; abel
  rw [hzy, inner_sub_right, real_inner_smul_right] at hlow
  rw [hzx, real_inner_smul_right, square_smul] at hupp
  have hdiff : ⟪g x, g x - g y⟫_ℝ - ⟪g y, g x - g y⟫_ℝ =
      ‖g x - g y‖ ^ 2 := by rw [← inner_sub_left, inner_self_eq]
  have hcoef : L / 2 * (-(L⁻¹)) ^ 2 = L⁻¹ / 2 := by
    field_simp [ne_of_gt hL]
  have htw : 2 * L * L⁻¹ = 2 := by field_simp [ne_of_gt hL]
  have hlow' := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2 * L by positivity)
  have hupp' := mul_le_mul_of_nonneg_left hupp (show 0 ≤ 2 * L by positivity)
  have hclean :
      (2 * L) * (L / 2 * ((-(L⁻¹)) ^ 2 * ‖g x - g y‖ ^ 2)) =
        ‖g x - g y‖ ^ 2 := by
    field_simp [ne_of_gt hL]
  have hmul₁ : 2 * L * (L⁻¹ * ⟪g y, g x - g y⟫_ℝ) =
      2 * ⟪g y, g x - g y⟫_ℝ := by field_simp [ne_of_gt hL]
  have hmul₂ : 2 * L * (-(L⁻¹) * ⟪g x, g x - g y⟫_ℝ) =
      -2 * ⟪g x, g x - g y⟫_ℝ := by field_simp [ne_of_gt hL]
  nlinarith [hlow', hupp', hclean, hmul₁, hmul₂, hdiff]

lemma composite_gradient_interpolation (F ψ : E → ℝ) (g : E → E)
    {M : ℝ} (hM : 0 ≤ M) (x xstar : E)
    (hinterp : ‖g x - g xstar‖ ^ 2 ≤
      2 * M * (F x - F xstar - ⟪g xstar, x - xstar⟫_ℝ))
    (hstar : ψ xstar + ⟪-g xstar, x - xstar⟫_ℝ ≤ ψ x) :
    ‖g x - g xstar‖ ^ 2 ≤
      2 * M * (F x + ψ x - (F xstar + ψ xstar)) := by
  rw [inner_neg_left] at hstar
  have hgap : F x - F xstar - ⟪g xstar, x - xstar⟫_ℝ ≤
      F x + ψ x - (F xstar + ψ xstar) := by linarith
  exact hinterp.trans (mul_le_mul_of_nonneg_left hgap (by positivity))

lemma composite_strong_gap (F ψ : E → ℝ) (μ : ℝ) (x xstar gstar : E)
    (hstrong : F xstar + ⟪gstar, x - xstar⟫_ℝ +
      μ / 2 * ‖x - xstar‖ ^ 2 ≤ F x)
    (hstar : ψ xstar + ⟪-gstar, x - xstar⟫_ℝ ≤ ψ x) :
    μ / 2 * ‖x - xstar‖ ^ 2 ≤ F x + ψ x - (F xstar + ψ xstar) := by
  rw [inner_neg_left] at hstar
  linarith

lemma regularization_center_offset (μ : ℝ) (x x0 xstar g : E) :
    g + μ • (x - x0) = (g + μ • (x - xstar)) + μ • (xstar - x0) := by
  simp only [smul_sub]
  abel

lemma regularization_offset_norm {μ R : ℝ} (hμ : 0 ≤ μ)
    (x0 xstar : E) (hdistance : ‖x0 - xstar‖ ≤ R) :
    ‖μ • (xstar - x0)‖ ≤ μ * R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ, norm_sub_rev xstar x0]
  exact mul_le_mul_of_nonneg_left hdistance hμ

lemma weighted_initial_momentum_bound {n : ℕ} (hn : 0 < n)
    (w l : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hl : ∀ i, 0 ≤ l i) (m g0 gstar : Fin n → E)
    {L R : ℝ} (hR : 0 ≤ R)
    (hsmooth : ∀ i, ‖g0 i - gstar i‖ ≤ l i * R)
    (hrms : (n : ℝ)⁻¹ * ∑ i, l i ^ 2 ≤ L ^ 2) :
    (n : ℝ)⁻¹ * ∑ i, w i * ‖m i - gstar i‖ ^ 2 ≤
      2 * ((n : ℝ)⁻¹ * ∑ i, ‖m i - g0 i‖ ^ 2) + 2 * L ^ 2 * R ^ 2 := by
  have hpoint : ∀ i, w i * ‖m i - gstar i‖ ^ 2 ≤
      2 * ‖m i - g0 i‖ ^ 2 + 2 * l i ^ 2 * R ^ 2 := by
    intro i
    have hv : m i - gstar i = (m i - g0 i) + (g0 i - gstar i) := by abel
    have htwo := square_two (m i - g0 i) (g0 i - gstar i)
    rw [← hv] at htwo
    have hg : ‖g0 i - gstar i‖ ^ 2 ≤ l i ^ 2 * R ^ 2 := by
      have hnn : 0 ≤ l i * R := mul_nonneg (hl i) hR
      nlinarith [hsmooth i, norm_nonneg (g0 i - gstar i)]
    have hwbound := mul_le_mul_of_nonneg_right (hw1 i) (sq_nonneg ‖m i - gstar i‖)
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hmean := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hsumid :
      (n : ℝ)⁻¹ * ∑ i, (2 * ‖m i - g0 i‖ ^ 2 + 2 * l i ^ 2 * R ^ 2) =
        2 * ((n : ℝ)⁻¹ * ∑ i, ‖m i - g0 i‖ ^ 2) +
          2 * ((n : ℝ)⁻¹ * ∑ i, l i ^ 2) * R ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hsumid] at hmean
  have hscaled := mul_le_mul_of_nonneg_right hrms (sq_nonneg R)
  nlinarith

end LongTails.Proofs.ProximalEf21ConvexAnalysis


end ConvexAnalysis


section FunctionalCalculus

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21FunctionalCalculus

open LongTails.Proofs.ProximalEf21Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma signed_correction_change (ψ : E → ℝ) (x y xstar m mnext : E) :
    -(ψ y - ψ xstar + ⟪mnext, y - xstar⟫_ℝ) / 8 +
        (ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ) / 8 =
      -(ψ y - ψ x) / 8 - ⟪mnext - m, y - xstar⟫_ℝ / 8 +
        ⟪m, x - y⟫_ℝ / 8 := by
  have hv : x - xstar = (x - y) + (y - xstar) := by abel
  rw [hv]
  simp only [inner_add_right, inner_sub_left]
  ring

lemma functional_change_from_model (F ψ : E → ℝ) {μ τ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (xstar x y m mnext z znext g : E)
    (hsmooth : F y - F x ≤ -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2)
    (hsupport : ψ z + ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ ≤ ψ znext) :
    functionalEnergy F ψ μ τ xstar y mnext znext -
        functionalEnergy F ψ μ τ xstar x m z ≤
      -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2 +
        (7 / 8 + 1 / (μ * τ)) * (ψ y - ψ x) -
        ⟪mnext - m, y - xstar⟫_ℝ / 8 + ⟪m, x - y⟫_ℝ / 8 +
        (-⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          ⟪x - z, mnext - m⟫_ℝ + τ / 2 * ‖mnext - m‖ ^ 2) / (μ * τ) := by
  have hmodel := proximal_model_change ψ hτ x y m mnext z znext hsupport
  have hscaled := div_le_div_of_nonneg_right hmodel
    (show 0 ≤ μ * τ by positivity)
  have hsign := signed_correction_change ψ x y xstar m mnext
  calc
    functionalEnergy F ψ μ τ xstar y mnext znext -
        functionalEnergy F ψ μ τ xstar x m z =
      (F y - F x) + (ψ y - ψ x) +
        (-(ψ y - ψ xstar + ⟪mnext, y - xstar⟫_ℝ) / 8 +
          (ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ) / 8) +
        (modelDecrease ψ τ y mnext znext -
          modelDecrease ψ τ x m z) / (μ * τ) := by
      unfold functionalEnergy
      ring
    _ ≤ (-⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2) + (ψ y - ψ x) +
        (-(ψ y - ψ xstar + ⟪mnext, y - xstar⟫_ℝ) / 8 +
          (ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ) / 8) +
        (ψ y - ψ x - ⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          ⟪x - z, mnext - m⟫_ℝ + τ / 2 * ‖mnext - m‖ ^ 2) / (μ * τ) :=
      add_le_add (add_le_add (add_le_add hsmooth le_rfl) le_rfl) hscaled
    _ = -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2 +
        (7 / 8 + 1 / (μ * τ)) * (ψ y - ψ x) -
        ⟪mnext - m, y - xstar⟫_ℝ / 8 + ⟪m, x - y⟫_ℝ / 8 +
        (-⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          ⟪x - z, mnext - m⟫_ℝ + τ / 2 * ‖mnext - m‖ ^ 2) / (μ * τ) := by
      rw [hsign]
      simp only [div_eq_mul_inv]
      ring

noncomputable def componentBound (_F ψ : E → ℝ) (μ τ γ α : ℝ)
    (xstar x y m z g b : E) : ℝ :=
  -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2 +
    (7 / 8 + 1 / (μ * τ)) * (ψ y - ψ x) -
    (α / 8) * ⟪g - m + b, y - xstar⟫_ℝ + ⟪m, x - y⟫_ℝ / 8 -
    ⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ / (μ * τ) +
    γ / τ * ⟪x - z, g - m + b⟫_ℝ +
    μ * γ ^ 2 / 2 * ‖g - m + b‖ ^ 2

lemma functional_change_with_noise (F ψ : E → ℝ) {μ τ γ α : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hα : α = μ * γ)
    (xstar x y m mnext z znext g b ζ : E)
    (hupdate : mnext = m + α • (g - m + b + ζ))
    (hsmooth : F y - F x ≤ -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2)
    (hsupport : ψ z + ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ ≤ ψ znext) :
    functionalEnergy F ψ μ τ xstar y mnext znext -
        functionalEnergy F ψ μ τ xstar x m z ≤
      componentBound F ψ μ τ γ α xstar x y m z g b +
        γ / τ * ⟪x - z, ζ⟫_ℝ - α / 8 * ⟪y - xstar, ζ⟫_ℝ +
        μ * γ ^ 2 * ⟪g - m + b, ζ⟫_ℝ + μ * γ ^ 2 / 2 * ‖ζ‖ ^ 2 := by
  have hbase := functional_change_from_model F ψ hμ hτ
    xstar x y m mnext z znext g hsmooth hsupport
  have hinc : mnext - m = α • (g - m + b + ζ) := by rw [hupdate]; abel
  rw [hinc, real_inner_smul_left, real_inner_smul_right, square_smul, square_add] at hbase
  rw [inner_add_left, inner_add_right] at hbase
  have hid :
      -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2 +
        (7 / 8 + 1 / (μ * τ)) * (ψ y - ψ x) -
        (α * (⟪g - m + b, y - xstar⟫_ℝ + ⟪ζ, y - xstar⟫_ℝ)) / 8 +
        ⟪m, x - y⟫_ℝ / 8 +
        (-⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          α * (⟪x - z, g - m + b⟫_ℝ + ⟪x - z, ζ⟫_ℝ) +
          τ / 2 * (α ^ 2 * (‖g - m + b‖ ^ 2 +
            2 * ⟪g - m + b, ζ⟫_ℝ + ‖ζ‖ ^ 2))) / (μ * τ) =
      componentBound F ψ μ τ γ α xstar x y m z g b +
        γ / τ * ⟪x - z, ζ⟫_ℝ - α / 8 * ⟪y - xstar, ζ⟫_ℝ +
        μ * γ ^ 2 * ⟪g - m + b, ζ⟫_ℝ + μ * γ ^ 2 / 2 * ‖ζ‖ ^ 2 := by
    unfold componentBound
    rw [hα]
    rw [real_inner_comm ζ (y - xstar)]
    field_simp [ne_of_gt hμ, ne_of_gt hτ]
    <;> ring
  calc
    functionalEnergy F ψ μ τ xstar y mnext znext -
        functionalEnergy F ψ μ τ xstar x m z ≤ _ := hbase
    _ = _ := hid

lemma componentBound_assembled (F ψ : E → ℝ) {μ τ γ α : ℝ}
    (hμ : μ ≠ 0) (hγ : γ ≠ 0) (hτ : τ ≠ 0)
    (xstar x y m v z g b : E) :
    componentBound F ψ μ τ γ α xstar x y m z g b =
      -(7 / (8 * γ) + μ / 2) * ‖y - x‖ ^ 2 -
      (7 / 8 + 1 / (μ * τ)) *
        (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) -
      α / 8 * ⟪y - xstar, g - m + b⟫_ℝ +
      7 / 8 * ⟪v - m, x - y⟫_ℝ + ⟪b, x - y⟫_ℝ -
      γ * ⟪g - m + b, γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ -
      γ / (μ * τ) *
        ⟪γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m),
          γ⁻¹ • (x - y)⟫_ℝ +
      μ * γ ^ 2 / 2 * ‖g - m + b‖ ^ 2 := by
  unfold componentBound
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_neg_right, inner_neg_left, real_inner_comm]
  field_simp [hμ, hγ, hτ]
  <;> ring

end LongTails.Proofs.ProximalEf21FunctionalCalculus


end FunctionalCalculus


section FunctionalBounds

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21FunctionalBounds

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21FunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma remaining_young_bounds {μ γ α : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hα : α = μ * γ)
    (x y xstar c b : E) :
    α / 8 * ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ ≤
        α * μ / 32 * ‖y - xstar‖ ^ 2 + ‖y - x‖ ^ 2 / (8 * γ) ∧
    -α / 8 * ⟪y - xstar, c⟫_ℝ ≤
        α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖c‖ ^ 2 ∧
    -α / 8 * ⟪y - xstar, b⟫_ℝ ≤
        α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖b‖ ^ 2 ∧
    7 / 8 * ⟪c, x - y⟫_ℝ ≤ ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖c‖ ^ 2 ∧
    ⟪b, x - y⟫_ℝ ≤ ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖b‖ ^ 2 := by
  have hαpos : 0 < α := by rw [hα]; positivity
  have hnorm : ‖x - y‖ ^ 2 = ‖y - x‖ ^ 2 := by rw [norm_sub_rev]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := inner_young (μ / 2) (by positivity)
      (y - xstar) (γ⁻¹ • (x - y))
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ α / 8 by positivity)
    rw [square_smul, hnorm] at hh
    have hid : α / 8 * ((μ / 2) / 2 * ‖y - xstar‖ ^ 2 +
        1 / (2 * (μ / 2)) * (γ⁻¹ ^ 2 * ‖y - x‖ ^ 2)) =
        α * μ / 32 * ‖y - xstar‖ ^ 2 + ‖y - x‖ ^ 2 / (8 * γ) := by
      rw [hα]
      field_simp [ne_of_gt hμ, ne_of_gt hγ]
      <;> ring
    simpa only [hid] using hh
  · have h := neg_inner_young (μ / 8) (by positivity) (y - xstar) c
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ α / 8 by positivity)
    have hid : α / 8 * ((μ / 8) / 2 * ‖y - xstar‖ ^ 2 +
        1 / (2 * (μ / 8)) * ‖c‖ ^ 2) =
        α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖c‖ ^ 2 := by
      rw [hα]
      field_simp [ne_of_gt hμ]
      <;> ring
    rw [hid] at hh
    linarith
  · have h := neg_inner_young (μ / 8) (by positivity) (y - xstar) b
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ α / 8 by positivity)
    have hid : α / 8 * ((μ / 8) / 2 * ‖y - xstar‖ ^ 2 +
        1 / (2 * (μ / 8)) * ‖b‖ ^ 2) =
        α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖b‖ ^ 2 := by
      rw [hα]
      field_simp [ne_of_gt hμ]
      <;> ring
    rw [hid] at hh
    linarith
  · have h := inner_young (1 / (8 * γ)) (by positivity) (x - y) c
    rw [real_inner_comm c (x - y), hnorm] at h
    have hc₁ : (1 / (8 * γ) : ℝ) / 2 = 1 / (16 * γ) := by ring
    have hc₂ : (1 : ℝ) / (2 * (1 / (8 * γ))) = 4 * γ := by
      field_simp [ne_of_gt hγ]
      <;> ring
    rw [hc₁, hc₂] at h
    have hbound : ⟪c, x - y⟫_ℝ ≤
        ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖c‖ ^ 2 := by
      calc
        ⟪c, x - y⟫_ℝ ≤ 1 / (16 * γ) * ‖y - x‖ ^ 2 +
            4 * γ * ‖c‖ ^ 2 := h
        _ = ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖c‖ ^ 2 := by ring
    have hn : 0 ≤ ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖c‖ ^ 2 := by positivity
    calc
      7 / 8 * ⟪c, x - y⟫_ℝ ≤
          (7 / 8) * (‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ ≤ ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖c‖ ^ 2 := by
        linarith only [hn]
  · have h := inner_young (1 / (8 * γ)) (by positivity) (x - y) b
    rw [real_inner_comm b (x - y), hnorm] at h
    have hc₁ : (1 / (8 * γ) : ℝ) / 2 = 1 / (16 * γ) := by ring
    have hc₂ : (1 : ℝ) / (2 * (1 / (8 * γ))) = 4 * γ := by
      field_simp [ne_of_gt hγ]
      <;> ring
    rw [hc₁, hc₂] at h
    calc
      ⟪b, x - y⟫_ℝ ≤ 1 / (16 * γ) * ‖y - x‖ ^ 2 +
          4 * γ * ‖b‖ ^ 2 := h
      _ = ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖b‖ ^ 2 := by ring

lemma pointwise_functional_progress (F ψ : E → ℝ) {μ M τ γ α W V : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hτ : 0 < τ) (hγ : 0 < γ)
    (hγτ : γ ≤ τ / 2) (hμτ : μ * τ ≤ 1 / 4096)
    (hα : α = μ * γ) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (xstar x y m v z g gstar b : E)
    (hD : 0 ≤ ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ)
    (hstrong : F y + ⟪g, xstar - y⟫_ℝ + μ / 2 * ‖xstar - y‖ ^ 2 ≤ F xstar)
    (hmono : 0 ≤
      ⟪γ⁻¹ • (x - y) - v - (τ⁻¹ • (x - z) - m), y - z⟫_ℝ)
    (hgrad : ‖g - gstar‖ ^ 2 ≤ 2 * M * (F y + ψ y - (F xstar + ψ xstar)))
    (hmemory : ‖m - gstar‖ ^ 2 ≤ 2 * W)
    (hcompression : ‖v - m‖ ^ 2 ≤ 2 * V) :
    componentBound F ψ μ τ γ α xstar x y m z g b ≤
      -α * (1 / 8 - 15 * M * τ / 2) * (F y + ψ y - (F xstar + ψ xstar)) -
      5 / (8 * γ) * ‖y - x‖ ^ 2 -
      α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) -
      1 / (μ * τ) * (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) +
      15 * α * τ / 2 * W + 5 * γ / (μ * τ) * V + 5 * γ * ‖b‖ ^ 2 := by
  have hτγ : γ < τ := by linarith only [hγ, hγτ]
  have hden : 0 < τ - γ := sub_pos.mpr hτγ
  have hαpos : 0 < α := by rw [hα]; positivity
  have hmcomp := proximal_displacement_comparison hγ hτγ x y z m v hmono
  have hmix := mixed_proximal_products hγ hμ hτγ (g - m + b)
    (γ⁻¹ • (x - y)) (τ⁻¹ • (x - z)) (v - m) hmcomp
  have hcross := objective_cross_lower_bound F ψ μ γ x y xstar g m v b hstrong
  rw [inner_add_right (y - xstar) (v - m) b] at hcross
  have hcross' := neg_le_neg (mul_le_mul_of_nonneg_left hcross
    (show 0 ≤ α / 8 by positivity))
  obtain ⟨hy₁, hy₂, hy₃, hy₄, hy₅⟩ :=
    remaining_young_bounds hμ hγ hα x y xstar (v - m) b
  have hcrossBound :
      -α / 8 * ⟪y - xstar, g - m + b⟫_ℝ ≤
        -α / 8 * (F y + ψ y - (F xstar + ψ xstar)) -
        α * μ / 64 * ‖y - xstar‖ ^ 2 -
        α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) +
        ‖y - x‖ ^ 2 / (8 * γ) + γ / 2 * ‖v - m‖ ^ 2 +
        γ / 2 * ‖b‖ ^ 2 := by
    calc
      -α / 8 * ⟪y - xstar, g - m + b⟫_ℝ ≤
          -(α / 8 * (F y + ψ y - (F xstar + ψ xstar) +
            μ / 2 * ‖y - xstar‖ ^ 2 +
            (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) -
            ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ +
            (⟪y - xstar, v - m⟫_ℝ + ⟪y - xstar, b⟫_ℝ))) := by
        simpa only [neg_div, neg_mul] using hcross'
      _ = (-α / 8 * (F y + ψ y - (F xstar + ψ xstar)) -
            α * μ / 16 * ‖y - xstar‖ ^ 2 -
            α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar)) +
          (α / 8 * ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ) +
          (-α / 8 * ⟪y - xstar, v - m⟫_ℝ) +
          (-α / 8 * ⟪y - xstar, b⟫_ℝ) := by ring
      _ ≤ (-α / 8 * (F y + ψ y - (F xstar + ψ xstar)) -
            α * μ / 16 * ‖y - xstar‖ ^ 2 -
            α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar)) +
          (α * μ / 32 * ‖y - xstar‖ ^ 2 + ‖y - x‖ ^ 2 / (8 * γ)) +
          (α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖v - m‖ ^ 2) +
          (α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖b‖ ^ 2) :=
        add_le_add (add_le_add (add_le_add le_rfl hy₁) hy₂) hy₃
      _ = -α / 8 * (F y + ψ y - (F xstar + ψ xstar)) -
          α * μ / 64 * ‖y - xstar‖ ^ 2 -
          α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) +
          ‖y - x‖ ^ 2 / (8 * γ) + γ / 2 * ‖v - m‖ ^ 2 +
          γ / 2 * ‖b‖ ^ 2 := by ring
  have hq := square_three (g - gstar) (-(m - gstar)) b
  have hqvec : g - gstar + -(m - gstar) + b = g - m + b := by abel
  rw [hqvec, norm_neg] at hq
  have hqbound : ‖g - m + b‖ ^ 2 ≤
      3 * (2 * M * (F y + ψ y - (F xstar + ψ xstar)) + 2 * W + ‖b‖ ^ 2) := by
    exact hq.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hgrad hmemory) le_rfl) (by norm_num))
  have hqslack : 0 ≤ μ * γ ^ 2 / 2 + α * τ / 4 := by positivity
  have hqcoef : μ * γ ^ 2 / 2 + γ * μ * (τ - γ) ≤ 5 * α * τ / 4 := by
    calc
      μ * γ ^ 2 / 2 + γ * μ * (τ - γ) =
          5 * α * τ / 4 - (μ * γ ^ 2 / 2 + α * τ / 4) := by
        rw [hα]
        ring
      _ ≤ 5 * α * τ / 4 := sub_le_self _ hqslack
  have hqfinal :
      (μ * γ ^ 2 / 2 + γ * μ * (τ - γ)) * ‖g - m + b‖ ^ 2 ≤
      15 * α * τ / 4 *
        (2 * M * (F y + ψ y - (F xstar + ψ xstar)) + 2 * W + ‖b‖ ^ 2) := by
    calc
      (μ * γ ^ 2 / 2 + γ * μ * (τ - γ)) * ‖g - m + b‖ ^ 2 ≤
          (5 * α * τ / 4) * ‖g - m + b‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hqcoef (sq_nonneg ‖g - m + b‖)
      _ ≤ (5 * α * τ / 4) *
          (3 * (2 * M * (F y + ψ y - (F xstar + ψ xstar)) + 2 * W + ‖b‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hqbound (by positivity)
      _ = 15 * α * τ / 4 *
          (2 * M * (F y + ψ y - (F xstar + ψ xstar)) + 2 * W + ‖b‖ ^ 2) := by ring
  have hcden : γ / (μ * (τ - γ)) ≤ 2 * γ / (μ * τ) := by
    apply (div_le_div_iff₀ (mul_pos hμ hden) (mul_pos hμ hτ)).2
    have hsmall : 0 ≤ τ - 2 * γ := by linarith only [hγτ]
    calc
      γ * (μ * τ) ≤ γ * (μ * τ) + γ * μ * (τ - 2 * γ) :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg hγ.le hμ.le) hsmall)
      _ = (2 * γ) * (μ * (τ - γ)) := by ring
  have hcsmall : (2 * γ / (μ * τ) + 9 * γ / 2) * 2 ≤ 5 * γ / (μ * τ) := by
    apply (le_div_iff₀ (mul_pos hμ hτ)).2
    have hsmall : 9 * (μ * τ) ≤ 1 := by linarith only [hμτ]
    calc
      (2 * γ / (μ * τ) + 9 * γ / 2) * 2 * (μ * τ) =
          2 * ((2 * γ / (μ * τ)) * (μ * τ)) + 9 * γ * (μ * τ) := by ring
      _ = 4 * γ + γ * (9 * (μ * τ)) := by
        rw [div_mul_cancel₀ _ (ne_of_gt (mul_pos hμ hτ))]
        ring
      _ ≤ 4 * γ + γ * 1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall hγ.le)
      _ = 5 * γ := by ring
  have hcfinal : (γ / (μ * (τ - γ)) + 9 * γ / 2) * ‖v - m‖ ^ 2 ≤
      5 * γ / (μ * τ) * V := by
    calc
      (γ / (μ * (τ - γ)) + 9 * γ / 2) * ‖v - m‖ ^ 2 ≤
          (2 * γ / (μ * τ) + 9 * γ / 2) * ‖v - m‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (add_le_add hcden le_rfl) (sq_nonneg ‖v - m‖)
      _ ≤ (2 * γ / (μ * τ) + 9 * γ / 2) * (2 * V) :=
        mul_le_mul_of_nonneg_left hcompression (by positivity)
      _ = ((2 * γ / (μ * τ) + 9 * γ / 2) * 2) * V := by ring
      _ ≤ 5 * γ / (μ * τ) * V := mul_le_mul_of_nonneg_right hcsmall hV
  have hbcoef : 9 * γ / 2 + 15 * α * τ / 4 ≤ 5 * γ := by
    have hsmall : (9 / 2 : ℝ) + 15 * (μ * τ) / 4 ≤ 5 := by linarith only [hμτ]
    calc
      9 * γ / 2 + 15 * α * τ / 4 = γ * (9 / 2 + 15 * (μ * τ) / 4) := by
        rw [hα]
        ring
      _ ≤ γ * 5 := mul_le_mul_of_nonneg_left hsmall hγ.le
      _ = 5 * γ := by ring
  have hb := mul_le_mul_of_nonneg_right hbcoef (sq_nonneg ‖b‖)
  let retained : ℝ :=
    -α / 8 * (F y + ψ y - (F xstar + ψ xstar)) -
    5 / (8 * γ) * ‖y - x‖ ^ 2 -
    α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) -
    1 / (μ * τ) * (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ)
  let discarded : ℝ :=
    α * μ / 64 * ‖y - xstar‖ ^ 2 + μ / 2 * ‖y - x‖ ^ 2 +
    γ / (2 * μ * (τ - γ)) *
      ‖γ⁻¹ • (x - y) - τ⁻¹ • (x - z)‖ ^ 2 +
    7 / 8 * (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ)
  have hdiscarded : 0 ≤ discarded := by
    dsimp only [discarded]
    positivity
  let rest : ℝ :=
    -(7 / (8 * γ) + μ / 2) * ‖y - x‖ ^ 2 -
    (7 / 8 + 1 / (μ * τ)) *
      (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) +
    μ * γ ^ 2 / 2 * ‖g - m + b‖ ^ 2
  have hsum := add_le_add (add_le_add (add_le_add hcrossBound hy₄) hy₅) hmix
  have hraw : componentBound F ψ μ τ γ α xstar x y m z g b ≤
      retained + (μ * γ ^ 2 / 2 + γ * μ * (τ - γ)) * ‖g - m + b‖ ^ 2 +
        (γ / (μ * (τ - γ)) + 9 * γ / 2) * ‖v - m‖ ^ 2 +
        9 * γ / 2 * ‖b‖ ^ 2 - discarded := by
    calc
      componentBound F ψ μ τ γ α xstar x y m z g b =
          rest + ((-α / 8 * ⟪y - xstar, g - m + b⟫_ℝ +
            7 / 8 * ⟪v - m, x - y⟫_ℝ + ⟪b, x - y⟫_ℝ) +
            (-γ * ⟪g - m + b, γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ -
              γ / (μ * τ) *
                ⟪γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m),
                  γ⁻¹ • (x - y)⟫_ℝ)) := by
        rw [componentBound_assembled F ψ (ne_of_gt hμ) (ne_of_gt hγ)
          (ne_of_gt hτ) xstar x y m v z g b]
        dsimp only [rest]
        ring
      _ ≤ _ := add_le_add (le_refl rest) hsum
      _ = retained + (μ * γ ^ 2 / 2 + γ * μ * (τ - γ)) * ‖g - m + b‖ ^ 2 +
          (γ / (μ * (τ - γ)) + 9 * γ / 2) * ‖v - m‖ ^ 2 +
          9 * γ / 2 * ‖b‖ ^ 2 - discarded := by
        dsimp only [rest, retained, discarded]
        ring
  calc
    componentBound F ψ μ τ γ α xstar x y m z g b ≤
        retained + (μ * γ ^ 2 / 2 + γ * μ * (τ - γ)) * ‖g - m + b‖ ^ 2 +
          (γ / (μ * (τ - γ)) + 9 * γ / 2) * ‖v - m‖ ^ 2 +
          9 * γ / 2 * ‖b‖ ^ 2 :=
      hraw.trans (sub_le_self _ hdiscarded)
    _ ≤ retained + 15 * α * τ / 4 *
          (2 * M * (F y + ψ y - (F xstar + ψ xstar)) + 2 * W + ‖b‖ ^ 2) +
          5 * γ / (μ * τ) * V + 9 * γ / 2 * ‖b‖ ^ 2 :=
      add_le_add (add_le_add (add_le_add le_rfl hqfinal) hcfinal) le_rfl
    _ = (-α * (1 / 8 - 15 * M * τ / 2) * (F y + ψ y - (F xstar + ψ xstar)) -
          5 / (8 * γ) * ‖y - x‖ ^ 2 -
          α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) -
          1 / (μ * τ) * (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) +
          15 * α * τ / 2 * W + 5 * γ / (μ * τ) * V) +
          (9 * γ / 2 + 15 * α * τ / 4) * ‖b‖ ^ 2 := by
      dsimp only [retained]
      ring
    _ ≤ -α * (1 / 8 - 15 * M * τ / 2) * (F y + ψ y - (F xstar + ψ xstar)) -
          5 / (8 * γ) * ‖y - x‖ ^ 2 -
          α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) -
          1 / (μ * τ) * (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) +
          15 * α * τ / 2 * W + 5 * γ / (μ * τ) * V + 5 * γ * ‖b‖ ^ 2 :=
      add_le_add le_rfl hb

end LongTails.Proofs.ProximalEf21FunctionalBounds


end FunctionalBounds


section TrajectoryGeometry

open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21TrajectoryGeometry

open LongTails.Proofs.ProximalEf21Averages

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21WeightedErrors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure InnerGeometry (n : ℕ) (μ M : ℝ) where
  domain : Set E
  ψ : E → ℝ
  f : Fin n → E → ℝ
  grad : Fin n → E → E
  localL : Fin n → ℝ
  prox : ℝ → E → E
  xstar : E
  hn : 0 < n
  hμ : 0 < μ
  hμM : μ ≤ M
  localL_nonnegative : ∀ i, 0 ≤ localL i
  localL_average : (n : ℝ)⁻¹ * ∑ i, localL i ≤ M
  local_lower : ∀ i x y, f i x + ⟪grad i x, y - x⟫_ℝ ≤ f i y
  local_upper : ∀ i x y,
    f i y ≤ f i x + ⟪grad i x, y - x⟫_ℝ + localL i / 2 * ‖y - x‖ ^ 2
  average_strong : ∀ x y,
    (n : ℝ)⁻¹ * ∑ i, f i x +
      ⟪workerMean (fun i => grad i x), y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i, f i y
  regularizer_convex : ConvexOn ℝ domain ψ
  optimum_mem : xstar ∈ domain
  optimum_support : ∀ x ∈ domain,
    ψ xstar + ⟪-workerMean (fun i => grad i xstar), x - xstar⟫_ℝ ≤ ψ x
  prox_mem : ∀ τ, 0 < τ → ∀ u, prox τ u ∈ domain
  prox_min : ∀ τ, 0 < τ → ∀ u z, z ∈ domain →
    ψ (prox τ u) + ‖prox τ u - u‖ ^ 2 / (2 * τ) ≤
      ψ z + ‖z - u‖ ^ 2 / (2 * τ)

namespace InnerGeometry

variable {n : ℕ} {μ M : ℝ} (G : InnerGeometry (E := E) n μ M)

noncomputable def smoothValue (x : E) : ℝ := (n : ℝ)⁻¹ * ∑ i, G.f i x
noncomputable def smoothGradient (x : E) : E := workerMean (fun i => G.grad i x)
noncomputable def gap (x : E) : ℝ := G.smoothValue x + G.ψ x - (G.smoothValue G.xstar + G.ψ G.xstar)
noncomputable def weights (i : Fin n) : ℝ := M / (M + G.localL i)
noncomputable def W (m : Fin n → E) : ℝ := weightedSquare G.weights (fun i => m i - G.grad i G.xstar)
noncomputable def V (m v : Fin n → E) : ℝ := weightedSquare G.weights (fun i => v i - m i)
noncomputable def auxiliary (τ : ℝ) (x : E) (m : Fin n → E) : E :=
  G.prox τ (x - τ • workerMean m)
noncomputable def energy (τ : ℝ) (x : E) (m : Fin n → E) : ℝ :=
  functionalEnergy G.smoothValue G.ψ μ τ G.xstar x (workerMean m) (G.auxiliary τ x m)
noncomputable def potential (τ : ℝ) (x : E) (m v : Fin n → E) : ℝ :=
  G.energy τ x m + G.V m v / μ + G.W m / (64 * M)

include G in
lemma M_pos : 0 < M := lt_of_lt_of_le G.hμ G.hμM

lemma weights_positive (i : Fin n) : 0 < G.weights i :=
  (weight_properties G.M_pos (G.localL_nonnegative i)).1

lemma weights_le_one (i : Fin n) : G.weights i ≤ 1 :=
  (weight_properties G.M_pos (G.localL_nonnegative i)).2.1

lemma W_nonnegative (m : Fin n → E) : 0 ≤ G.W m :=
  weightedSquare_nonnegative _ (fun i => (G.weights_positive i).le) _

lemma V_nonnegative (m v : Fin n → E) : 0 ≤ G.V m v :=
  weightedSquare_nonnegative _ (fun i => (G.weights_positive i).le) _

lemma average_inner (x u : E) :
    (n : ℝ)⁻¹ * ∑ i, ⟪G.grad i x, u⟫_ℝ = ⟪G.smoothGradient x, u⟫_ℝ := by
  simp only [smoothGradient, workerMean, real_inner_smul_left, sum_inner]

lemma smooth_upper (x y : E) :
    G.smoothValue y ≤ G.smoothValue x + ⟪G.smoothGradient x, y - x⟫_ℝ +
      M / 2 * ‖y - x‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => G.local_upper i x y))
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hid : (n : ℝ)⁻¹ * ∑ i,
      (G.f i x + ⟪G.grad i x, y - x⟫_ℝ + G.localL i / 2 * ‖y - x‖ ^ 2) =
      G.smoothValue x + ⟪G.smoothGradient x, y - x⟫_ℝ +
      ((n : ℝ)⁻¹ * ∑ i, G.localL i) / 2 * ‖y - x‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div,
      mul_add, G.average_inner, smoothValue]
    ring
  rw [hid] at h
  have hM := mul_le_mul_of_nonneg_right G.localL_average (sq_nonneg ‖y - x‖)
  exact h.trans (by nlinarith only [hM])

lemma smooth_lower (x y : E) :
    G.smoothValue x + ⟪G.smoothGradient x, y - x⟫_ℝ ≤ G.smoothValue y := by
  have h := G.average_strong x y
  change G.smoothValue x + ⟪G.smoothGradient x, y - x⟫_ℝ +
    μ / 2 * ‖y - x‖ ^ 2 ≤ G.smoothValue y at h
  have hn : 0 ≤ μ / 2 * ‖y - x‖ ^ 2 :=
    mul_nonneg (div_nonneg G.hμ.le (by norm_num)) (sq_nonneg _)
  linarith

lemma strong_gap (x : E) (hx : x ∈ G.domain) : μ / 2 * ‖x - G.xstar‖ ^ 2 ≤ G.gap x := by
  apply composite_strong_gap G.smoothValue G.ψ μ x G.xstar (G.smoothGradient G.xstar)
  · exact G.average_strong G.xstar x
  · exact G.optimum_support x hx

lemma gap_nonnegative (x : E) (hx : x ∈ G.domain) : 0 ≤ G.gap x := by
  exact (mul_nonneg (div_nonneg G.hμ.le (by norm_num))
    (sq_nonneg ‖x - G.xstar‖)).trans (G.strong_gap x hx)

lemma global_gradient_interpolation (x : E) (hx : x ∈ G.domain) :
    ‖G.smoothGradient x - G.smoothGradient G.xstar‖ ^ 2 ≤ 2 * M * G.gap x := by
  apply composite_gradient_interpolation G.smoothValue G.ψ G.smoothGradient
    G.M_pos.le x G.xstar
  · exact smooth_convex_interpolation G.smoothValue G.smoothGradient G.M_pos
      G.smooth_lower G.smooth_upper x G.xstar
  · exact G.optimum_support x hx

lemma weighted_gradient_interpolation (x : E) (hx : x ∈ G.domain) :
    weightedSquare G.weights (fun i => G.grad i x - G.grad i G.xstar) ≤ 2 * M * G.gap x := by
  have hp (i : Fin n) :
      G.weights i * ‖G.grad i x - G.grad i G.xstar‖ ^ 2 ≤
        2 * M * (G.f i x - G.f i G.xstar - ⟪G.grad i G.xstar, x - G.xstar⟫_ℝ) := by
    have hlocalPos : 0 < M + G.localL i := add_pos_of_pos_of_nonneg G.M_pos (G.localL_nonnegative i)
    have hu : ∀ y z,
        G.f i z ≤ G.f i y + ⟪G.grad i y, z - y⟫_ℝ +
          (M + G.localL i) / 2 * ‖z - y‖ ^ 2 := by
      intro y z
      have hs := G.local_upper i y z
      have hh : 0 ≤ M * ‖z - y‖ ^ 2 := mul_nonneg G.M_pos.le (sq_nonneg _)
      linarith
    have h := smooth_convex_interpolation (G.f i) (G.grad i) hlocalPos
      (G.local_lower i) hu x G.xstar
    have hscaled := mul_le_mul_of_nonneg_left h (G.weights_positive i).le
    have hid (a : ℝ) : G.weights i * (2 * (M + G.localL i) * a) = 2 * M * a := by
      unfold weights
      field_simp [ne_of_gt hlocalPos]
    simpa only [hid] using hscaled
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i))
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hid : (n : ℝ)⁻¹ * ∑ i,
      2 * M * (G.f i x - G.f i G.xstar - ⟪G.grad i G.xstar, x - G.xstar⟫_ℝ) =
      2 * M * (G.smoothValue x - G.smoothValue G.xstar -
        ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ) := by
    rw [← Finset.mul_sum]
    simp only [Finset.sum_sub_distrib]
    rw [← G.average_inner G.xstar (x - G.xstar)]
    unfold smoothValue
    ring
  rw [hid] at hs
  have hstar := G.optimum_support x hx
  change G.ψ G.xstar + ⟪-G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ≤ G.ψ x at hstar
  rw [inner_neg_left] at hstar
  have hgap : G.smoothValue x - G.smoothValue G.xstar -
      ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ≤ G.gap x := by
    unfold gap
    linarith
  exact hs.trans (mul_le_mul_of_nonneg_left hgap (mul_nonneg (by norm_num) G.M_pos.le))

lemma average_momentum_control (m : Fin n → E) :
    ‖workerMean m - G.smoothGradient G.xstar‖ ^ 2 ≤ 2 * G.W m := by
  have h := aggregate_error_bound G.hn G.M_pos G.localL G.localL_nonnegative
    G.localL_average (fun i => m i - G.grad i G.xstar)
  change ‖workerMean (fun i => m i - G.grad i G.xstar)‖ ^ 2 ≤ 2 * G.W m at h
  rw [workerMean_sub] at h
  exact h

lemma average_compression_control (m v : Fin n → E) :
    ‖workerMean v - workerMean m‖ ^ 2 ≤ 2 * G.V m v := by
  have h := aggregate_error_bound G.hn G.M_pos G.localL G.localL_nonnegative
    G.localL_average (fun i => v i - m i)
  change ‖workerMean (fun i => v i - m i)‖ ^ 2 ≤ 2 * G.V m v at h
  rw [workerMean_sub] at h
  exact h

lemma prox_support {a : ℝ} (ha : 0 < a) (u z : E) (hz : z ∈ G.domain) :
    G.ψ (G.prox a u) + ⟪a⁻¹ • (u - G.prox a u), z - G.prox a u⟫_ℝ ≤ G.ψ z :=
  proximal_supporting_affine G.domain G.ψ G.regularizer_convex ha u
    (G.prox a u) (G.prox_mem a ha u) (G.prox_min a ha u) z hz

lemma prox_support_step {a : ℝ} (ha : 0 < a) (x v z : E) (hz : z ∈ G.domain) :
    G.ψ (G.prox a (x - a • v)) +
      ⟪a⁻¹ • (x - G.prox a (x - a • v)) - v,
        z - G.prox a (x - a • v)⟫_ℝ ≤ G.ψ z := by
  have h := G.prox_support ha (x - a • v) z hz
  have hv : a⁻¹ • ((x - a • v) - G.prox a (x - a • v)) =
      a⁻¹ • (x - G.prox a (x - a • v)) - v := by
    have he : (x - a • v) - G.prox a (x - a • v) =
        (x - G.prox a (x - a • v)) - a • v := by abel
    rw [he, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  simpa only [hv] using h

lemma model_nonnegative {τ : ℝ} (hτ : 0 < τ) (x : E) (hx : x ∈ G.domain)
    (m : Fin n → E) : 0 ≤ modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) := by
  apply modelDecrease_nonnegative
  have hmin := G.prox_min τ hτ (x - τ • workerMean m) x hx
  have hz := complete_model_square G.ψ (ne_of_gt hτ) x (workerMean m) (G.auxiliary τ x m)
  have hxid := complete_model_square G.ψ (ne_of_gt hτ) x (workerMean m) x
  norm_num only [sub_self, inner_zero_right, norm_zero, zero_div, add_zero] at hxid
  change G.ψ (G.auxiliary τ x m) +
    ‖G.auxiliary τ x m - (x - τ • workerMean m)‖ ^ 2 / (2 * τ) ≤
      G.ψ x + ‖x - (x - τ • workerMean m)‖ ^ 2 / (2 * τ) at hmin
  linarith only [hz, hxid, hmin]

lemma model_lower {τ : ℝ} (hτ : 0 < τ) (hμτ : μ * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m : Fin n → E) :
    G.ψ x - G.ψ G.xstar + ⟪workerMean m, x - G.xstar⟫_ℝ -
      μ / 2 * ‖x - G.xstar‖ ^ 2 ≤
      modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ) := by
  have ht : 0 ≤ μ * τ := mul_nonneg G.hμ.le hτ.le
  have hconv := G.regularizer_convex.2 hx G.optimum_mem
    (sub_nonneg.mpr hμτ) ht (by ring)
  have hmem := G.regularizer_convex.1 hx G.optimum_mem
    (sub_nonneg.mpr hμτ) ht (by ring)
  apply model_lower_from_segment G.ψ G.hμ hτ x G.xstar (workerMean m)
    (G.auxiliary τ x m)
  · simpa only [smul_eq_mul] using hconv
  · have hmin := G.prox_min τ hτ (x - τ • workerMean m)
      ((1 - μ * τ) • x + (μ * τ) • G.xstar) hmem
    have h1 := complete_model_square G.ψ (ne_of_gt hτ) x (workerMean m)
      (G.auxiliary τ x m)
    have h2 := complete_model_square G.ψ (ne_of_gt hτ) x (workerMean m)
      ((1 - μ * τ) • x + (μ * τ) • G.xstar)
    change G.ψ (G.auxiliary τ x m) +
      ‖G.auxiliary τ x m - (x - τ • workerMean m)‖ ^ 2 / (2 * τ) ≤ _ at hmin
    linarith

lemma energy_lower {τ : ℝ} (hτ : 0 < τ) (hμτ : μ * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m : Fin n → E) :
    (7 / 8 : ℝ) * (G.gap x +
      modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ)) ≤
      G.energy τ x m := by
  exact (functionalEnergy_nonnegative G.smoothValue G.ψ G.hμ hτ G.xstar x
    (workerMean m) (G.auxiliary τ x m) (G.gap_nonnegative x hx)
    (G.strong_gap x hx) (G.model_nonnegative hτ x hx m)
    (G.model_lower hτ hμτ x hx m)).1

lemma potential_lower {τ : ℝ} (hτ : 0 < τ) (hμτ : μ * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m v : Fin n → E) :
    (7 / 8 : ℝ) * G.gap x +
      (7 / 8 : ℝ) * modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ) +
      G.V m v / μ + G.W m / (64 * M) ≤ G.potential τ x m v := by
  have h := G.energy_lower hτ hμτ x hx m
  calc
    (7 / 8 : ℝ) * G.gap x +
        (7 / 8 : ℝ) * modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ) +
        G.V m v / μ + G.W m / (64 * M) =
        (7 / 8 : ℝ) * (G.gap x +
          modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ)) +
          G.V m v / μ + G.W m / (64 * M) := by ring
    _ ≤ G.energy τ x m + G.V m v / μ + G.W m / (64 * M) :=
      add_le_add (add_le_add h (le_refl (G.V m v / μ)))
        (le_refl (G.W m / (64 * M)))
    _ = G.potential τ x m v := rfl

lemma potential_nonnegative {τ : ℝ} (hτ : 0 < τ) (hμτ : μ * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m v : Fin n → E) : 0 ≤ G.potential τ x m v := by
  have h := G.potential_lower hτ hμτ x hx m v
  have hg := G.gap_nonnegative x hx
  have ha := G.model_nonnegative hτ x hx m
  have hv := G.V_nonnegative m v
  have hw := G.W_nonnegative m
  have hμpos : 0 < μ := G.hμ
  have hMpos : 0 < M := G.M_pos
  have hnon : 0 ≤ (7 / 8 : ℝ) * G.gap x +
      (7 / 8 : ℝ) * modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ) +
      G.V m v / μ + G.W m / (64 * M) := by positivity
  exact hnon.trans h

end InnerGeometry

end LongTails.Proofs.ProximalEf21TrajectoryGeometry

end

end TrajectoryGeometry


section Regularization

open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21Regularization

open LongTails.Proofs.ProximalEf21Averages

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21TrajectoryGeometry
open LongTails.Proofs.ProximalEf21ScalarCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ConvexCompositeGeometry (n : ℕ) (L : ℝ) where
  domain : Set E
  ψ : E → ℝ
  f : Fin n → E → ℝ
  grad : Fin n → E → E
  localL : Fin n → ℝ
  prox : ℝ → E → E
  xstar : E
  hn : 0 < n
  hL : 0 < L
  localL_nonnegative : ∀ i, 0 ≤ localL i
  rms_bound : (n : ℝ)⁻¹ * ∑ i, (localL i) ^ 2 ≤ L ^ 2
  local_lower : ∀ i x y, f i x + ⟪grad i x, y - x⟫_ℝ ≤ f i y
  local_upper : ∀ i x y,
    f i y ≤ f i x + ⟪grad i x, y - x⟫_ℝ + localL i / 2 * ‖y - x‖ ^ 2
  local_lipschitz : ∀ i x y, ‖grad i x - grad i y‖ ≤ localL i * ‖x - y‖
  regularizer_convex : ConvexOn ℝ domain ψ
  optimum_mem : xstar ∈ domain
  optimum_support : ∀ x ∈ domain,
    ψ xstar + ⟪-workerMean (fun i => grad i xstar), x - xstar⟫_ℝ ≤ ψ x
  prox_mem : ∀ τ, 0 < τ → ∀ u, prox τ u ∈ domain
  prox_min : ∀ τ, 0 < τ → ∀ u z, z ∈ domain →
    ψ (prox τ u) + ‖prox τ u - u‖ ^ 2 / (2 * τ) ≤
      ψ z + ‖z - u‖ ^ 2 / (2 * τ)

namespace ConvexCompositeGeometry

variable {n : ℕ} {L : ℝ} (G : ConvexCompositeGeometry (E := E) n L)

noncomputable def smoothValue (x : E) : ℝ := (n : ℝ)⁻¹ * ∑ i, G.f i x
noncomputable def smoothGradient (x : E) : E := workerMean (fun i => G.grad i x)
noncomputable def gap (x : E) : ℝ := G.smoothValue x + G.ψ x - (G.smoothValue G.xstar + G.ψ G.xstar)

lemma mean_localL : (n : ℝ)⁻¹ * ∑ i, G.localL i ≤ L := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast G.hn
  let a : ℝ := (n : ℝ)⁻¹ * ∑ i, G.localL i
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsum : 0 ≤ ∑ i, (G.localL i - a) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hid : (n : ℝ)⁻¹ * ∑ i, (G.localL i - a) ^ 2 =
      (n : ℝ)⁻¹ * ∑ i, (G.localL i) ^ 2 - a ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [a]
    field_simp [hnz]
    <;> ring
  have h := mul_nonneg (inv_nonneg.mpr hnR.le) hsum
  rw [hid] at h
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (inv_nonneg.mpr hnR.le)
      (Finset.sum_nonneg (fun i _ => G.localL_nonnegative i))
  change a ≤ L
  nlinarith [G.rms_bound, G.hL]

lemma quadratic_expansion (x y : E) :
    ‖y - G.xstar‖ ^ 2 = ‖x - G.xstar‖ ^ 2 +
      2 * ⟪x - G.xstar, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
  rw [show y - G.xstar = (x - G.xstar) + (y - x) by abel, square_add]

noncomputable def regularized (μ : ℝ) (hμ : 0 < μ) (hμL : μ ≤ 2 * L) :
    InnerGeometry (E := E) n μ (3 * L) where
  domain := G.domain
  ψ := G.ψ
  f i x := G.f i x + μ / 2 * ‖x - G.xstar‖ ^ 2
  grad i x := G.grad i x + μ • (x - G.xstar)
  localL i := G.localL i + 2 * L
  prox := G.prox
  xstar := G.xstar
  hn := G.hn
  hμ := hμ
  hμM := by linarith [G.hL]
  localL_nonnegative i := by linarith [G.localL_nonnegative i, G.hL]
  localL_average := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt G.hn
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_add]
    have hc : (n : ℝ)⁻¹ * ((n : ℝ) * (2 * L)) = 2 * L := by
      field_simp [hnR]
    rw [hc]
    linarith [G.mean_localL]
  local_lower i x y := by
    have h := G.local_lower i x y
    rw [G.quadratic_expansion x y]
    simp only [inner_add_left, real_inner_smul_left]
    have hsq : 0 ≤ μ * ‖y - x‖ ^ 2 := by positivity
    nlinarith
  local_upper i x y := by
    have h := G.local_upper i x y
    rw [G.quadratic_expansion x y]
    simp only [inner_add_left, real_inner_smul_left]
    have hh := mul_le_mul_of_nonneg_right hμL (sq_nonneg ‖y - x‖)
    nlinarith
  average_strong x y := by
    have hs := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => G.local_lower i x y))
      (inv_nonneg.mpr (Nat.cast_nonneg n))
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt G.hn
    have hf (z : E) : (n : ℝ)⁻¹ * ∑ i,
        (G.f i z + μ / 2 * ‖z - G.xstar‖ ^ 2) =
        G.smoothValue z + μ / 2 * ‖z - G.xstar‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_add, smoothValue]
      field_simp [hnR]
    rw [hf, hf, workerMean_add, workerMean_const G.hn,
      inner_add_left, real_inner_smul_left, G.quadratic_expansion x y]
    have hi : (n : ℝ)⁻¹ * ∑ i, (G.f i x + ⟪G.grad i x, y - x⟫_ℝ) =
        G.smoothValue x + ⟪workerMean (fun i => G.grad i x), y - x⟫_ℝ := by
      simp only [Finset.sum_add_distrib, mul_add, workerMean,
        real_inner_smul_left, sum_inner, smoothValue]
    rw [hi] at hs
    change _ ≤ G.smoothValue y at hs
    linarith
  regularizer_convex := G.regularizer_convex
  optimum_mem := G.optimum_mem
  optimum_support x hx := by
    simpa only [sub_self, smul_zero, add_zero] using G.optimum_support x hx
  prox_mem := G.prox_mem
  prox_min := G.prox_min

lemma regularized_gradient {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * L) (x : E) :
    (G.regularized μ hμ hμL).smoothGradient x =
      G.smoothGradient x + μ • (x - G.xstar) := by
  exact (workerMean_add _ _).trans (by rw [workerMean_const G.hn]; rfl)

lemma regularized_value {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * L) (x : E) :
    (G.regularized μ hμ hμL).smoothValue x = G.smoothValue x + μ / 2 * ‖x - G.xstar‖ ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt G.hn
  simp only [InnerGeometry.smoothValue, regularized, smoothValue,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_add]
  field_simp [hnR]

lemma regularized_gap {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * L) (x : E) :
    (G.regularized μ hμ hμL).gap x = G.gap x + μ / 2 * ‖x - G.xstar‖ ^ 2 := by
  have hstar : (G.regularized μ hμ hμL).smoothValue G.xstar =
      G.smoothValue G.xstar := by
    rw [G.regularized_value hμ hμL G.xstar]
    simp only [sub_self, norm_zero, pow_two, mul_zero, add_zero]
  change (G.regularized μ hμ hμL).smoothValue x + G.ψ x -
      ((G.regularized μ hμ hμL).smoothValue G.xstar + G.ψ G.xstar) =
        G.gap x + μ / 2 * ‖x - G.xstar‖ ^ 2
  rw [G.regularized_value hμ hμL x, hstar]
  unfold gap
  ring

lemma base_gap_nonnegative (x : E) (hx : x ∈ G.domain) : 0 ≤ G.gap x := by
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => G.local_lower i G.xstar x))
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hi : (n : ℝ)⁻¹ * ∑ i, (G.f i G.xstar + ⟪G.grad i G.xstar, x - G.xstar⟫_ℝ) =
      G.smoothValue G.xstar + ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ := by
    simp only [smoothValue, smoothGradient, workerMean, Finset.sum_add_distrib,
      mul_add, real_inner_smul_left, sum_inner]
  rw [hi] at hs
  have hp := G.optimum_support x hx
  change G.ψ G.xstar + ⟪-G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ≤ G.ψ x at hp
  rw [inner_neg_left] at hp
  unfold gap
  change _ ≤ G.smoothValue x at hs
  linarith

lemma regularized_potential_transfer {μ τ : ℝ}
    (hμ : 0 < μ) (h2μ : 2 * μ ≤ 2 * L)
    (hτ : 0 < τ) (hscale : (2 * μ) * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m v : Fin n → E) :
    (G.regularized μ hμ (by linarith)).potential τ x m v ≤
      (15 / 7 : ℝ) * (G.regularized (2 * μ) (by positivity) h2μ).potential τ x m v := by
  let oldG := G.regularized (2 * μ) (by positivity) h2μ
  let newG := G.regularized μ hμ (by linarith)
  have hV : newG.V m v = oldG.V m v := rfl
  have hW : newG.W m = oldG.W m := by
    unfold InnerGeometry.W InnerGeometry.weights newG oldG regularized
    simp only [sub_self, smul_zero, add_zero]
  have hz : newG.auxiliary τ x m = oldG.auxiliary τ x m := rfl
  have hgapnew : newG.gap x = G.gap x + μ / 2 * ‖x - G.xstar‖ ^ 2 :=
    G.regularized_gap hμ (show μ ≤ 2 * L by linarith) x
  have hgapold : oldG.gap x = G.gap x + (2 * μ) / 2 * ‖x - G.xstar‖ ^ 2 :=
    G.regularized_gap (show 0 < 2 * μ by positivity) h2μ x
  have hidentity : newG.potential τ x m v = oldG.potential τ x m v -
      μ / 2 * ‖x - G.xstar‖ ^ 2 +
      modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) / ((2 * μ) * τ) +
      oldG.V m v / (2 * μ) := by
    have hmodel_scale (a : ℝ) : a / (μ * τ) = 2 * (a / ((2 * μ) * τ)) := by
      field_simp [ne_of_gt hμ, ne_of_gt hτ]
    have herror_scale (a : ℝ) : a / μ = 2 * (a / (2 * μ)) := by
      field_simp [ne_of_gt hμ]
    change newG.gap x -
        (G.ψ x - G.ψ G.xstar + ⟪workerMean m, x - G.xstar⟫_ℝ) / 8 +
        modelDecrease G.ψ τ x (workerMean m) (newG.auxiliary τ x m) / (μ * τ) +
        newG.V m v / μ + newG.W m / (64 * (3 * L)) =
      oldG.gap x -
        (G.ψ x - G.ψ G.xstar + ⟪workerMean m, x - G.xstar⟫_ℝ) / 8 +
        modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) / ((2 * μ) * τ) +
        oldG.V m v / (2 * μ) + oldG.W m / (64 * (3 * L)) -
        μ / 2 * ‖x - G.xstar‖ ^ 2 +
        modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) / ((2 * μ) * τ) +
        oldG.V m v / (2 * μ)
    rw [hV, hW, hz, hgapnew, hgapold, hmodel_scale, herror_scale]
    ring
  have hlo := oldG.potential_lower hτ hscale x hx m v
  change (7 / 8 : ℝ) * oldG.gap x +
      (7 / 8 : ℝ) * modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) /
        ((2 * μ) * τ) + oldG.V m v / (2 * μ) + oldG.W m / (64 * (3 * L)) ≤
      oldG.potential τ x m v at hlo
  have hgap := oldG.gap_nonnegative x hx
  have hwn := oldG.W_nonnegative m
  have hvn := oldG.V_nonnegative m v
  have hgap_part : 0 ≤ (7 / 8 : ℝ) * oldG.gap x :=
    mul_nonneg (by norm_num) hgap
  have hWt : 0 ≤ oldG.W m / (64 * (3 * L)) :=
    div_nonneg hwn (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) G.hL.le))
  have hcontrol : (7 / 8 : ℝ) *
      (modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) / ((2 * μ) * τ)) +
      oldG.V m v / (2 * μ) ≤ oldG.potential τ x m v := by
    calc
      (7 / 8 : ℝ) *
          (modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) / ((2 * μ) * τ)) +
          oldG.V m v / (2 * μ) =
          (7 / 8 : ℝ) * modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) /
            ((2 * μ) * τ) + oldG.V m v / (2 * μ) := by ring
      _ ≤ (7 / 8 : ℝ) * oldG.gap x +
          (7 / 8 : ℝ) * modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) /
            ((2 * μ) * τ) + oldG.V m v / (2 * μ) + oldG.W m / (64 * (3 * L)) := by
        linarith only [hgap_part, hWt]
      _ ≤ oldG.potential τ x m v := hlo
  exact stage_transfer_from_model_control
    (mul_nonneg (div_nonneg hμ.le (by norm_num)) (sq_nonneg ‖x - G.xstar‖))
    (div_nonneg hvn (mul_nonneg (by norm_num) hμ.le)) hcontrol hidentity

end ConvexCompositeGeometry

end LongTails.Proofs.ProximalEf21Regularization

end

end Regularization


section SetupGeometry

open MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21SetupGeometry

open LongTails.Proofs.ProximalEf21Averages

open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21Regularization

variable {p : Params} {I : Instance p}

lemma line_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (hg : ∀ x, HasGradientAt f (g x) x)
    (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) ⟪g (x + t • d), d⟫_ℝ t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hc := (hg (x + t • d)).hasFDerivAt.comp_hasDerivAt t hp
  rw [hasDerivAt_iff_isLittleO] at hc ⊢
  simpa [Function.comp_def, smul_eq_mul] using hc

lemma convex_gradient_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (x y : E) : f x + ⟪g x, y - x⟫_ℝ ≤ f y := by
  have hc' : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • (y - x))) := by
    refine ⟨convex_univ, ?_⟩
    intro a ha b hb u v hu hv huv
    have h := hc.2 (Set.mem_univ (x + a • (y - x)))
      (Set.mem_univ (x + b • (y - x))) hu hv huv
    have hid : u • (x + a • (y - x)) + v • (x + b • (y - x)) =
        x + (u * a + v * b) • (y - x) := by
      rw [smul_add, smul_add, smul_smul, smul_smul]
      calc
        u • x + (u * a) • (y - x) + (v • x + (v * b) • (y - x)) =
            (u + v) • x + (u * a + v * b) • (y - x) := by module
        _ = _ := by rw [huv, one_smul]
    change f (x + (u * a + v * b) • (y - x)) ≤
      u * f (x + a • (y - x)) + v * f (x + b • (y - x))
    change f (u • (x + a • (y - x)) + v • (x + b • (y - x))) ≤
      u * f (x + a • (y - x)) + v * f (x + b • (y - x)) at h
    rw [hid] at h
    exact h
  have hd := line_gradient f g hg x (y - x) 0
  simp only [zero_smul, add_zero] at hd
  have h := hc'.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by norm_num) hd
  have hy : x + (y - x) = y := by abel
  have hbound : ⟪g x, y - x⟫_ℝ ≤ f y - f x := by
    simpa [slope, hy] using h
  linarith only [hbound]

lemma smooth_gradient_upper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  have hf : Continuous (fun t : ℝ => f (x + t • d)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (line_gradient f g hg x d t).continuousAt
  have hB (t : ℝ) : HasDerivAt
      (fun s : ℝ => f x + s * ⟪g x, d⟫_ℝ + L / 2 * s ^ 2 * ‖d‖ ^ 2)
      (⟪g x, d⟫_ℝ + L * t * ‖d‖ ^ 2) t := by
    convert (((hasDerivAt_id t).mul_const ⟪g x, d⟫_ℝ).const_add (f x)).add
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖d‖ ^ 2)) using 1 <;>
      first
      | rfl
      | (funext s; simp only [Pi.add_apply, Pi.pow_apply, id_eq] <;> ring)
      | (simp only [id_eq] <;> ring)
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ⟪g (x + t • d), d⟫_ℝ ≤ ⟪g x, d⟫_ℝ + L * t * ‖d‖ ^ 2 := by
    intro t ht
    have hi := real_inner_le_norm (g (x + t • d) - g x) d
    have hn := hl (x + t • d) x
    have hd : x + t • d - x = t • d := by abel
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hn
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg d)
    rw [inner_sub_left] at hi
    nlinarith only [hi, hm]
  have h := image_le_of_deriv_right_le_deriv_boundary
    (a := (0 : ℝ)) (b := 1) hf.continuousOn
    (fun t ht => (line_gradient f g hg x d t).hasDerivWithinAt)
    (by simp)
    (by fun_prop)
    (fun t ht => (hB t).hasDerivWithinAt) hbound
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa [d] using h

noncomputable def domain (I : Instance p) : Set (Point p) := {x | I.ψ x ≠ ⊤}
noncomputable def psiValue (I : Instance p) (x : Point p) : ℝ := (I.ψ x).toReal

lemma finite_psi_coe (h : ProblemAssumptions p I) (x : Point p)
    (hx : x ∈ domain I) : (psiValue I x : EReal) = I.ψ x :=
  EReal.coe_toReal hx (h.regularizerNoBottom x)

lemma finite_psi_convex (h : ProblemAssumptions p I) :
    ConvexOn ℝ (domain I) (psiValue I) := by
  have hpair (x : Point p) (hx : x ∈ domain I) :
      (x, psiValue I x) ∈ {z : Point p × ℝ | I.ψ z.1 ≤ (z.2 : EReal)} := by
    change I.ψ x ≤ (psiValue I x : EReal)
    rw [finite_psi_coe h x hx]
  have hm (x : Point p) (hx : x ∈ domain I) (y : Point p) (hy : y ∈ domain I)
      (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      I.ψ (a • x + b • y) ≤ ((a * psiValue I x + b * psiValue I y : ℝ) : EReal) := by
    have hc := h.regularizerConvex (hpair x hx) (hpair y hy) ha hb hab
    simpa only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul, Set.mem_ofPred_eq] using hc
  have hdom : Convex ℝ (domain I) := by
    intro x hx y hy a b ha hb hab
    have hc := hm x hx y hy a b ha hb hab
    exact ne_top_of_le_ne_top
      (EReal.coe_ne_top (a * psiValue I x + b * psiValue I y)) hc
  refine ⟨hdom, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := hm x hx y hy a b ha hb hab
  have hr := EReal.toReal_le_toReal hc (h.regularizerNoBottom _)
    (EReal.coe_ne_top (a * psiValue I x + b * psiValue I y))
  simpa only [EReal.toReal_coe, smul_eq_mul, psiValue] using hr

lemma finite_prox_min (h : ProblemAssumptions p I) {τ : ℝ} (hτ : 0 < τ)
    (u z : Point p) (hz : z ∈ domain I) :
    psiValue I (I.prox τ u) + ‖I.prox τ u - u‖ ^ 2 / (2 * τ) ≤
      psiValue I z + ‖z - u‖ ^ 2 / (2 * τ) := by
  have hmin := h.proximalMinimizer τ hτ u z
  rw [← finite_psi_coe h (I.prox τ u) (h.proximalFinite τ hτ u),
    ← finite_psi_coe h z hz, ← EReal.coe_add, ← EReal.coe_add] at hmin
  exact EReal.coe_le_coe_iff.mp hmin

lemma finite_optimum (h : ProblemAssumptions p I) (x : Point p)
    (hx : x ∈ domain I) : finiteObjective I I.xstar ≤ finiteObjective I x := by
  have ho := h.optimum x
  unfold objective at ho
  rw [← finite_psi_coe h I.xstar h.optimumFinite,
    ← finite_psi_coe h x hx, ← EReal.coe_add, ← EReal.coe_add] at ho
  exact EReal.coe_le_coe_iff.mp ho

lemma average_upper (h : ProblemAssumptions p I) (hn : 0 < p.workers)
    (x y : Point p) :
    smoothObjective I y ≤ smoothObjective I x +
      ⟪workerMean (fun i => gradient (I.f i) x), y - x⟫_ℝ +
      ((p.workers : ℝ)⁻¹ * ∑ i, I.localL i) / 2 * ‖y - x‖ ^ 2 := by
  have hi (i : Fin p.workers) := smooth_gradient_upper (I.f i)
    (gradient (I.f i)) (I.localL i) (h.localNonnegative i)
    (h.localGradient i) (h.localSmooth i) x y
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i))
    (inv_nonneg.mpr (Nat.cast_nonneg p.workers))
  simpa only [Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.sum_mul, mul_add, smoothObjective, workerMean,
    real_inner_smul_left, sum_inner, mul_div_assoc, mul_assoc] using hs

lemma composite_optimum_support (h : ProblemAssumptions p I)
    (hn : 0 < p.workers) (x : Point p) (hx : x ∈ domain I) :
    psiValue I I.xstar +
      ⟪-workerMean (fun i => gradient (I.f i) I.xstar), x - I.xstar⟫_ℝ ≤
      psiValue I x := by
  let A : ℝ := (p.workers : ℝ)⁻¹ * ∑ i, I.localL i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun i _ => h.localNonnegative i))
  have hψ := finite_psi_convex h
  have hnonpos : psiValue I I.xstar - psiValue I x -
      ⟪workerMean (fun i => gradient (I.f i) I.xstar), x - I.xstar⟫_ℝ ≤ 0 := by
    apply nonpositive_of_segment_bounds (c := A / 2 * ‖x - I.xstar‖ ^ 2)
      (by positivity)
    intro t ht ht1
    have hmem := hψ.1 h.optimumFinite hx (sub_nonneg.mpr ht1) ht.le (by ring)
    have hc := hψ.2 h.optimumFinite hx (sub_nonneg.mpr ht1) ht.le (by ring)
    have hmin := finite_optimum h _ hmem
    have hs := average_upper h hn I.xstar ((1 - t) • I.xstar + t • x)
    have he : (1 - t) • I.xstar + t • x - I.xstar = t • (x - I.xstar) := by module
    rw [he, real_inner_smul_right, square_smul] at hs
    simp only [smul_eq_mul] at hc
    unfold finiteObjective at hmin
    change _ + psiValue I I.xstar ≤ _ + psiValue I _ at hmin
    change _ ≤ _ + _ + A / 2 * (t ^ 2 * _) at hs
    apply (mul_le_mul_iff_of_pos_left ht).mp
    nlinarith only [hmin, hc, hs]
  rw [inner_neg_left]
  linarith

noncomputable def geometry (hp : spec.valid p) (h : ProblemAssumptions p I) :
    ConvexCompositeGeometry (E := Point p) p.workers p.L where
  domain := domain I
  ψ := psiValue I
  f := I.f
  grad i := gradient (I.f i)
  localL := I.localL
  prox := I.prox
  xstar := I.xstar
  hn := hp.1
  hL := hp.2.1
  localL_nonnegative := h.localNonnegative
  rms_bound := by
    have hnonneg : 0 ≤ (p.workers : ℝ)⁻¹ * ∑ i, I.localL i ^ 2 := by positivity
    rw [h.rmsSmoothness, Real.sq_sqrt hnonneg]
  local_lower i := convex_gradient_lower (I.f i) (gradient (I.f i))
    (h.localConvex i) (h.localGradient i)
  local_upper i := smooth_gradient_upper (I.f i) (gradient (I.f i))
    (I.localL i) (h.localNonnegative i) (h.localGradient i) (h.localSmooth i)
  local_lipschitz := h.localSmooth
  regularizer_convex := finite_psi_convex h
  optimum_mem := h.optimumFinite
  optimum_support := composite_optimum_support h hp.1
  prox_mem := h.proximalFinite
  prox_min τ hτ u z hz := finite_prox_min h hτ u z hz

lemma geometry_gap (hp : spec.valid p) (h : ProblemAssumptions p I) (x : Point p) :
    (geometry hp h).gap x = finiteObjective I x - finiteObjective I I.xstar := rfl

lemma prox_nonexpansive (hp : spec.valid p) (h : ProblemAssumptions p I)
    {τ : ℝ} (hτ : 0 < τ) (u v : Point p) :
    ‖I.prox τ u - I.prox τ v‖ ≤ ‖u - v‖ := by
  let G := (geometry hp h).regularized (2 * p.L) (by linarith [hp.2.1]) (by rfl)
  have h₁ := G.prox_support hτ u (I.prox τ v) (h.proximalFinite τ hτ v)
  have h₂ := G.prox_support hτ v (I.prox τ u) (h.proximalFinite τ hτ u)
  change psiValue I (I.prox τ u) +
    ⟪τ⁻¹ • (u - I.prox τ u), I.prox τ v - I.prox τ u⟫_ℝ ≤ psiValue I (I.prox τ v) at h₁
  change psiValue I (I.prox τ v) +
    ⟪τ⁻¹ • (v - I.prox τ v), I.prox τ u - I.prox τ v⟫_ℝ ≤ psiValue I (I.prox τ u) at h₂
  have he : ⟪u - I.prox τ u, I.prox τ v - I.prox τ u⟫_ℝ +
      ⟪v - I.prox τ v, I.prox τ u - I.prox τ v⟫_ℝ =
      ‖I.prox τ u - I.prox τ v‖ ^ 2 -
        ⟪u - v, I.prox τ u - I.prox τ v⟫_ℝ := by
    rw [← inner_self_eq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  simp only [real_inner_smul_left] at h₁ h₂
  have hsum : τ⁻¹ * (‖I.prox τ u - I.prox τ v‖ ^ 2 -
      ⟪u - v, I.prox τ u - I.prox τ v⟫_ℝ) ≤ 0 := by
    rw [← he, mul_add]
    linarith only [h₁, h₂]
  have hfirm : ‖I.prox τ u - I.prox τ v‖ ^ 2 ≤
      ⟪u - v, I.prox τ u - I.prox τ v⟫_ℝ := by
    apply sub_nonpos.mp
    apply (mul_le_mul_iff_of_pos_left (inv_pos.mpr hτ)).mp
    simpa only [mul_zero] using hsum
  have hc := real_inner_le_norm (u - v) (I.prox τ u - I.prox τ v)
  by_cases hz : ‖I.prox τ u - I.prox τ v‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hz' : 0 < ‖I.prox τ u - I.prox τ v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_of_pos_right hz').mp
    simpa only [pow_two] using hfirm.trans hc

end LongTails.Proofs.ProximalEf21SetupGeometry

end

end SetupGeometry
