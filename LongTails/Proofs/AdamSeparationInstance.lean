import LongTails.Proofs.AdamMatrixGeometry
import LongTails.Proofs.SeparationInstance

namespace LongTails.Proofs.AdamSeparationInstance

open LongTails.Algorithms.MatrixPolar
open LongTails.Proofs.AdamMatrixGeometry LongTails.Proofs.SeparationInstance

noncomputable def stiffCoord {r : ℕ} (x0 X : Space r r) : ℝ :=
  inner ℝ (denseProjection r) (X - x0)

noncomputable def quietCoord {r : ℕ} (x0 X : Space r r) : ℝ :=
  inner ℝ (quietProjection r) (X - x0) / ((r : ℝ) - 1)

noncomputable def objective {r : ℕ} (ℓ c w D : ℝ) (x0 X : Space r r) : ℝ :=
  ℓ / 2 * stiffCoord x0 X ^ 2 +
    c * ((r : ℝ) - 1) * (valley w D (quietCoord x0 X) - w)

lemma dense_eq_mixed (r : ℕ) : denseProjection r = mixedProjection r 1 0 := by
  simp [mixedProjection]

lemma quiet_eq_mixed (r : ℕ) : quietProjection r = mixedProjection r 0 1 := by
  simp [mixedProjection]

lemma stiffCoord_mixed {r : ℕ} (hr : 0 < r) (x0 : Space r r) (a b : ℝ) :
    stiffCoord x0 (x0 + mixedProjection r a b) = a := by
  simp only [stiffCoord, add_sub_cancel_left, dense_eq_mixed, inner_mixedProjection hr]
  ring

lemma quietCoord_mixed {r : ℕ} (hr : 1 < r) (x0 : Space r r) (a b : ℝ) :
    quietCoord x0 (x0 + mixedProjection r a b) = b := by
  have hr' : (r : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (r : ℤ) - 1 ≠ 0 by omega)
  simp only [quietCoord, add_sub_cancel_left, quiet_eq_mixed,
    inner_mixedProjection (show 0 < r by omega)]
  field_simp
  ring

lemma hasFDerivAt_stiffCoord {r : ℕ} (x0 X : Space r r) :
    HasFDerivAt (stiffCoord x0) (innerSL ℝ (denseProjection r)) X := by
  have h := ((innerSL ℝ (denseProjection r)).hasFDerivAt (x := X)).sub_const
    (inner ℝ (denseProjection r) x0)
  convert h using 1
  funext Y
  simp [stiffCoord, inner_sub_right]

lemma hasFDerivAt_quietCoord {r : ℕ} (x0 X : Space r r) :
    HasFDerivAt (quietCoord x0) (((r : ℝ) - 1)⁻¹ • innerSL ℝ (quietProjection r)) X := by
  have h := (((innerSL ℝ (quietProjection r)).hasFDerivAt (x := X)).sub_const
    (inner ℝ (quietProjection r) x0)).const_smul (((r : ℝ) - 1)⁻¹)
  convert h using 1
  funext Y
  simp [quietCoord, inner_sub_right, div_eq_mul_inv, mul_comm]

lemma hasGradientAt_objective {r : ℕ} (hr : 1 < r) (ℓ c D : ℝ) {w : ℝ}
    (hw : 0 < w) (x0 X : Space r r) :
    HasGradientAt (objective ℓ c w D x0)
      (mixedProjection r (ℓ * stiffCoord x0 X) (c * valleySlope w D (quietCoord x0 X))) X := by
  have hr' : (r : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (r : ℤ) - 1 ≠ 0 by omega)
  have hs : HasDerivAt (fun a : ℝ => ℓ / 2 * a ^ 2)
      (ℓ * stiffCoord x0 X) (stiffCoord x0 X) := by
    convert ((hasDerivAt_id (stiffCoord x0 X)).pow 2).const_mul (ℓ / 2) using 1
    · simp
    · simp
      ring
  have hq := ((hasDerivAt_valley hw D (quietCoord x0 X)).sub_const w).const_mul
    (c * ((r : ℝ) - 1))
  have h := (hs.comp_hasFDerivAt X (hasFDerivAt_stiffCoord x0 X)).add
    (hq.comp_hasFDerivAt X (hasFDerivAt_quietCoord x0 X))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · rfl
  · ext Y
    simp only [InnerProductSpace.toDual_apply_apply, mixedProjection, inner_add_left,
      real_inner_smul_left, add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
    field_simp

lemma gradient_objective {r : ℕ} (hr : 1 < r) (ℓ c D : ℝ) {w : ℝ}
    (hw : 0 < w) (x0 X : Space r r) :
    gradient (objective ℓ c w D x0) X =
      mixedProjection r (ℓ * stiffCoord x0 X) (c * valleySlope w D (quietCoord x0 X)) :=
  (hasGradientAt_objective hr ℓ c D hw x0 X).gradient

lemma nuclear_gradient_mixed {r : ℕ} (hr : 1 < r) (ℓ c D : ℝ) {w : ℝ}
    (hw : 0 < w) (x0 : Space r r) (a b : ℝ) :
    nuclearNorm (gradient (objective ℓ c w D x0) (x0 + mixedProjection r a b)) =
      |ℓ * a| + ((r : ℝ) - 1) * |c * valleySlope w D b| := by
  rw [gradient_objective hr ℓ c D hw, stiffCoord_mixed (by omega), quietCoord_mixed hr,
    nuclearNorm_mixedProjection (by omega)]

lemma stiffCoord_difference {r : ℕ} (hr : 0 < r) (x0 X Y : Space r r) :
    |stiffCoord x0 X - stiffCoord x0 Y| ≤ spectralNorm (X - Y) := by
  have h := inner_le_nuclear_mul_spectral (denseProjection r) (X - Y)
  rw [dense_eq_mixed, nuclearNorm_mixedProjection hr] at h
  simpa [stiffCoord, inner_sub_right, sub_sub_sub_cancel_right, mixedProjection] using h

lemma quietCoord_difference {r : ℕ} (hr : 1 < r) (x0 X Y : Space r r) :
    |quietCoord x0 X - quietCoord x0 Y| ≤ spectralNorm (X - Y) := by
  have hr' : 0 < (r : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < r - 1 by omega)
  have h := inner_le_nuclear_mul_spectral (quietProjection r) (X - Y)
  rw [quiet_eq_mixed, nuclearNorm_mixedProjection (by omega)] at h
  simp only [abs_zero, abs_one, zero_add, mul_one] at h
  unfold quietCoord
  rw [← sub_div, abs_div, abs_of_pos hr', div_le_iff₀ hr']
  have heq : inner ℝ (quietProjection r) (X - x0) - inner ℝ (quietProjection r) (Y - x0) =
      inner ℝ (quietProjection r) (X - Y) := by simp [inner_sub_right]
  rw [heq]
  simpa [mixedProjection, mul_comm] using h

lemma mixedProjection_sub (r : ℕ) (a b c d : ℝ) :
    mixedProjection r a b - mixedProjection r c d = mixedProjection r (a - c) (b - d) := by
  unfold mixedProjection
  module

lemma lipschitz_objective {r : ℕ} (hr : 1 < r) {ℓ c w : ℝ}
    (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (hw : 0 < w) (D : ℝ) (x0 X Y : Space r r) :
    nuclearNorm (gradient (objective ℓ c w D x0) X - gradient (objective ℓ c w D x0) Y) ≤
      (ℓ + ((r : ℝ) - 1) * c / w) * spectralNorm (X - Y) := by
  have hr' : 0 ≤ (r : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) ≤ r - 1 by omega)
  rw [gradient_objective hr ℓ c D hw, gradient_objective hr ℓ c D hw,
    mixedProjection_sub, nuclearNorm_mixedProjection (by omega)]
  rw [← mul_sub ℓ, ← mul_sub c, abs_mul, abs_mul, abs_of_nonneg hℓ, abs_of_nonneg hc]
  have ha := mul_le_mul_of_nonneg_left (stiffCoord_difference (by omega) x0 X Y) hℓ
  have hb := valleySlope_lipschitz hw D (quietCoord x0 X) (quietCoord x0 Y)
  have hb' := quietCoord_difference hr x0 X Y
  have hq : |valleySlope w D (quietCoord x0 X) - valleySlope w D (quietCoord x0 Y)| ≤
      spectralNorm (X - Y) / w := hb.trans (div_le_div_of_nonneg_right hb' hw.le)
  have hmul := mul_le_mul_of_nonneg_left hq (mul_nonneg hr' hc)
  calc
    _ ≤ ℓ * spectralNorm (X - Y) + ((r : ℝ) - 1) * c * (spectralNorm (X - Y) / w) := by
      nlinarith
    _ = _ := by ring

lemma objective_nonneg {r : ℕ} (hr : 1 < r) {ℓ c w : ℝ}
    (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (hw : 0 ≤ w) (D : ℝ) (x0 X : Space r r) :
    0 ≤ objective ℓ c w D x0 X := by
  have hr' : 0 ≤ (r : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) ≤ r - 1 by omega)
  have hv : w ≤ valley w D (quietCoord x0 X) := by
    unfold valley
    rw [Real.le_sqrt hw (by positivity)]
    nlinarith [sq_nonneg (quietCoord x0 X - D)]
  unfold objective
  positivity

lemma objective_start_le {r : ℕ} (hr : 1 < r) (ℓ : ℝ) {c w D : ℝ}
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hD : 0 ≤ D) (x0 : Space r r) :
    objective ℓ c w D x0 x0 ≤ c * ((r : ℝ) - 1) * D := by
  have hr' : 0 ≤ (r : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) ≤ r - 1 by omega)
  have hv : valley w D 0 - w ≤ D := by
    unfold valley
    have hs : Real.sqrt (w ^ 2 + (0 - D) ^ 2) ≤ w + D := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [mul_nonneg hw hD]
    linarith
  simpa [objective, stiffCoord, quietCoord] using
    mul_le_mul_of_nonneg_left hv (mul_nonneg hc hr')

lemma quiet_cost_barrier {R c w D ε b V : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c)
    (hw : 0 < w) (hD : 0 < D) (hε : 0 ≤ ε) (hRc : R * c = 4 * ε)
    (hDw : 2 * w ≤ D) (hb : |b| ≤ V) :
    2 * ε * D ≤ D * (R * |c * valleySlope w D b|) + 4 * ε * V := by
  have hquiet : 0 ≤ R * |c * valleySlope w D b| := by positivity
  have hV : 0 ≤ V := (abs_nonneg _).trans hb
  by_cases hsmall : V ≤ D / 2
  · have hs := valleySlope_far hw (D := D) (u := b) (by linarith [le_abs_self b])
    have habs : (1 / 2 : ℝ) ≤ |valleySlope w D b| := by
      have := neg_le_abs (valleySlope w D b)
      linarith
    have hq : 2 * ε ≤ R * |c * valleySlope w D b| := by
      rw [abs_mul, abs_of_nonneg hc, ← mul_assoc, hRc]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hq hD.le
    have hnonneg := mul_nonneg hε hV
    nlinarith
  · have hlarge : D / 2 < V := lt_of_not_ge hsmall
    have hmul := mul_le_mul_of_nonneg_left hlarge.le (show 0 ≤ 4 * ε by positivity)
    nlinarith [mul_nonneg hD.le hquiet]

end LongTails.Proofs.AdamSeparationInstance
