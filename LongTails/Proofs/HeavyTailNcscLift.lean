import LongTails.Proofs.GdConvex
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped RealInnerProductSpace
open InnerProductSpace

namespace LongTails.Proofs.HeavyTailNcscLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def lift (H : E → ℝ) (α β ν γ : ℝ) (x y : E) : ℝ :=
  α * H (β • y) - ν / 2 * ‖y - γ • x‖ ^ 2

noncomputable def liftGx (ν γ : ℝ) (z : E × E) : E := (ν * γ) • (z.2 - γ • z.1)

noncomputable def liftGy (gH : E → E) (q β ν γ : ℝ) (z : E × E) : E :=
  q • gH (β • z.2) - ν • (z.2 - γ • z.1)

lemma lift_hasGradient_x (H : E → ℝ) (α β ν γ : ℝ) (x y : E) :
    HasGradientAt (fun x' => lift H α β ν γ x' y) (liftGx ν γ (x, y)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (HasFDerivAt.norm_sq ((hasFDerivAt_const y x).sub
    ((hasFDerivAt_id x).const_smul γ))).const_mul (ν / 2)
  refine ((hasFDerivAt_const (α * H (β • y)) x).sub h).congr_fderiv ?_
  ext v
  simp only [liftGx, toDual_apply_apply]
  simp [inner_sub_left, inner_smul_left]
  ring

lemma lift_hasGradient_y {H : E → ℝ} {gH : E → E} (hH : ∀ u, HasGradientAt H (gH u) u)
    {α β ν γ q : ℝ} (hq : α * β = q) (x y : E) :
    HasGradientAt (fun y' => lift H α β ν γ x y') (liftGy gH q β ν γ (x, y)) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := ((hH (β • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul β)).const_mul α
  have h2 := (HasFDerivAt.norm_sq ((hasFDerivAt_id y).sub_const (γ • x))).const_mul (ν / 2)
  refine (h1.sub h2).congr_fderiv ?_
  ext v
  simp only [liftGy, toDual_apply_apply]
  simp [inner_sub_left, inner_smul_left]
  rw [← hq]
  ring

lemma inner_bound_sq (a b : ℝ) (t1 t2 : ℝ) :
    (a * t1 + b * t2) ^ 2 ≤ (a ^ 2 + b ^ 2) * (t1 ^ 2 + t2 ^ 2) := by
  nlinarith [sq_nonneg (a * t2 - b * t1)]

omit [CompleteSpace E] in
lemma lift_smooth {gH : E → E} {ℓ : ℝ} (hlip : ∀ u v, ‖gH u - gH v‖ ≤ ℓ * ‖u - v‖)
    {q β ν γ : ℝ} (hq : 0 ≤ q) (hβ : 0 ≤ β) (hν : 0 ≤ ν) (hγ : 0 ≤ γ) (z z' : E × E) :
    ‖liftGx ν γ z - liftGx ν γ z'‖ ^ 2 + ‖liftGy gH q β ν γ z - liftGy gH q β ν γ z'‖ ^ 2 ≤
      ((ν * γ ^ 2) ^ 2 + 2 * (ν * γ) ^ 2 + (q * β * ℓ + ν) ^ 2) *
        (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := by
  set dx := z.1 - z'.1
  set dy := z.2 - z'.2
  have hx : liftGx ν γ z - liftGx ν γ z' = (ν * γ) • (dy - γ • dx) := by
    simp only [liftGx, dx, dy, smul_sub]
    abel_nf
  have hy : liftGy gH q β ν γ z - liftGy gH q β ν γ z' =
      q • (gH (β • z.2) - gH (β • z'.2)) - ν • (dy - γ • dx) := by
    simp only [liftGy, dx, dy, smul_sub]
    abel_nf
  have hdd : ‖dy - γ • dx‖ ≤ ‖dy‖ + γ * ‖dx‖ := by
    calc ‖dy - γ • dx‖ ≤ ‖dy‖ + ‖γ • dx‖ := norm_sub_le _ _
      _ = ‖dy‖ + γ * ‖dx‖ := by rw [norm_smul, Real.norm_of_nonneg hγ]
  have hg : ‖gH (β • z.2) - gH (β • z'.2)‖ ≤ β * ℓ * ‖dy‖ := by
    have h := hlip (β • z.2) (β • z'.2)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hβ] at h
    linarith
  have hnx : ‖liftGx ν γ z - liftGx ν γ z'‖ ≤ ν * γ ^ 2 * ‖dx‖ + ν * γ * ‖dy‖ := by
    rw [hx, norm_smul, Real.norm_of_nonneg (mul_nonneg hν hγ)]
    nlinarith [mul_le_mul_of_nonneg_left hdd (mul_nonneg hν hγ)]
  have hny : ‖liftGy gH q β ν γ z - liftGy gH q β ν γ z'‖ ≤
      ν * γ * ‖dx‖ + (q * β * ℓ + ν) * ‖dy‖ := by
    rw [hy]
    calc _ ≤ ‖q • (gH (β • z.2) - gH (β • z'.2))‖ + ‖ν • (dy - γ • dx)‖ := norm_sub_le _ _
      _ = q * ‖gH (β • z.2) - gH (β • z'.2)‖ + ν * ‖dy - γ • dx‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hq, Real.norm_of_nonneg hν]
      _ ≤ q * (β * ℓ * ‖dy‖) + ν * (‖dy‖ + γ * ‖dx‖) := by
          gcongr
      _ = ν * γ * ‖dx‖ + (q * β * ℓ + ν) * ‖dy‖ := by ring
  have h1 := pow_le_pow_left₀ (norm_nonneg _) hnx 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hny 2
  have h3 := inner_bound_sq (ν * γ ^ 2) (ν * γ) ‖dx‖ ‖dy‖
  have h4 := inner_bound_sq (ν * γ) (q * β * ℓ + ν) ‖dx‖ ‖dy‖
  nlinarith

lemma lift_concave {H : E → ℝ} {gH : E → E} (hH : ∀ u, HasGradientAt H (gH u) u) {ℓ : ℝ}
    (hlip : ∀ u v, ‖gH u - gH v‖ ≤ ℓ * ‖u - v‖) {α β ν γ q h : ℝ} (hα : 0 ≤ α)
    (hq : α * β = q) (hh : α * β ^ 2 = h) (x y y' : E) :
    lift H α β ν γ x y' ≤ lift H α β ν γ x y + ⟪liftGy gH q β ν γ (x, y), y' - y⟫ -
      (ν - h * ℓ) / 2 * ‖y' - y‖ ^ 2 := by
  have hup := OracleTemplate.Gradient.smooth_upper_bound hH hlip (β • y) (β • y')
  have hd : β • y' - β • y = β • (y' - y) := (smul_sub β y' y).symm
  rw [hd, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hup
  have hsq : ‖y' - γ • x‖ ^ 2 = ‖y - γ • x‖ ^ 2 + 2 * ⟪y - γ • x, y' - y⟫ + ‖y' - y‖ ^ 2 := by
    have he : y' - γ • x = (y - γ • x) + (y' - y) := by abel
    rw [he, norm_add_sq_real]
  have hm := mul_le_mul_of_nonneg_left hup hα
  simp only [lift, liftGy]
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hsq]
  have : α * (β * ⟪gH (β • y), y' - y⟫) = q * ⟪gH (β • y), y' - y⟫ := by rw [← hq]; ring
  have : α * (ℓ / 2 * (β ^ 2 * ‖y' - y‖ ^ 2)) = h * ℓ / 2 * ‖y' - y‖ ^ 2 := by rw [← hh]; ring
  nlinarith

lemma lift_gap {H : E → ℝ} {gH : E → E} (hH : ∀ u, HasGradientAt H (gH u) u) {ℓ : ℝ}
    (hlip : ∀ u v, ‖gH u - gH v‖ ≤ ℓ * ‖u - v‖) {α β ν γ q h fstar : ℝ} (hα : 0 ≤ α)
    (hq : α * β = q) (hh : α * β ^ 2 = h) (hm : 0 < ν - h * ℓ) (hlow : ∀ u, fstar ≤ H u)
    (x y : E) :
    lift H α β ν γ 0 y - lift H α β ν γ x (γ • x) ≤
      α * (H 0 - fstar) + q ^ 2 * ‖gH 0‖ ^ 2 / (2 * (ν - h * ℓ)) := by
  have hup := OracleTemplate.Gradient.smooth_upper_bound hH hlip 0 (β • y)
  rw [sub_zero, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hup
  have hm' := mul_le_mul_of_nonneg_left hup hα
  have hlo := mul_le_mul_of_nonneg_left (hlow (β • (γ • x))) hα
  have hci : q * ⟪gH 0, y⟫ ≤ q ^ 2 * ‖gH 0‖ ^ 2 / (2 * (ν - h * ℓ)) +
      (ν - h * ℓ) / 2 * ‖y‖ ^ 2 := by
    have h1 : q * ⟪gH 0, y⟫ ≤ |q| * ‖gH 0‖ * ‖y‖ := by
      have := real_inner_le_norm (gH 0) y
      have habs := abs_real_inner_le_norm (gH 0) y
      calc q * ⟪gH 0, y⟫ ≤ |q * ⟪gH 0, y⟫| := le_abs_self _
        _ = |q| * |⟪gH 0, y⟫| := abs_mul _ _
        _ ≤ |q| * (‖gH 0‖ * ‖y‖) := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
        _ = |q| * ‖gH 0‖ * ‖y‖ := by ring
    have h2 : |q| * ‖gH 0‖ * ‖y‖ ≤ q ^ 2 * ‖gH 0‖ ^ 2 / (2 * (ν - h * ℓ)) +
        (ν - h * ℓ) / 2 * ‖y‖ ^ 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      have hq2 : |q| ^ 2 = q ^ 2 := sq_abs q
      nlinarith [sq_nonneg (|q| * ‖gH 0‖ - (ν - h * ℓ) * ‖y‖)]
    linarith
  simp only [lift, smul_zero, sub_zero, sub_self, norm_zero]
  have : α * (β * ⟪gH 0, y⟫) = q * ⟪gH 0, y⟫ := by rw [← hq]; ring
  have : α * (ℓ / 2 * (β ^ 2 * ‖y‖ ^ 2)) = h * ℓ / 2 * ‖y‖ ^ 2 := by rw [← hh]; ring
  nlinarith

omit [CompleteSpace E] in
lemma lift_transfer {gH : E → E} {ℓ : ℝ} (hlip : ∀ u v, ‖gH u - gH v‖ ≤ ℓ * ‖u - v‖)
    {q β ν γ : ℝ} (hq : 0 < q) (hβ : 0 ≤ β) (hν : 0 < ν) (hγ : 0 < γ) (x ys : E)
    (h0 : liftGy gH q β ν γ (x, ys) = 0) :
    ‖gH ((β * γ) • x)‖ ≤ (ν + q * β * ℓ) / (ν * γ * q) * ‖liftGx ν γ (x, ys)‖ := by
  have hrel : q • gH (β • ys) = ν • (ys - γ • x) := by
    simp only [liftGy] at h0
    exact sub_eq_zero.mp h0
  have hgn : ‖gH (β • ys)‖ = ν / q * ‖ys - γ • x‖ := by
    have h := congrArg norm hrel
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hq.le, Real.norm_of_nonneg hν.le] at h
    rw [div_mul_eq_mul_div, eq_div_iff hq.ne']
    linarith
  have hgx : ‖liftGx ν γ (x, ys)‖ = ν * γ * ‖ys - γ • x‖ := by
    simp only [liftGx]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hl := hlip ((β * γ) • x) (β • ys)
  have hd : (β * γ) • x - β • ys = -(β • (ys - γ • x)) := by
    rw [smul_sub, mul_smul]; abel
  rw [hd, norm_neg, norm_smul, Real.norm_of_nonneg hβ] at hl
  have htri : ‖gH ((β * γ) • x)‖ ≤ ‖gH (β • ys)‖ + ‖gH ((β * γ) • x) - gH (β • ys)‖ := by
    have := norm_sub_norm_le (gH ((β * γ) • x)) (gH (β • ys))
    linarith
  rw [hgx, hgn] at *
  rw [hgn] at htri
  have hfin : (ν + q * β * ℓ) / (ν * γ * q) * (ν * γ * ‖ys - γ • x‖) =
      ν / q * ‖ys - γ • x‖ + ℓ * (β * ‖ys - γ • x‖) := by
    field_simp
  rw [hfin]
  linarith

end LongTails.Proofs.HeavyTailNcscLift
