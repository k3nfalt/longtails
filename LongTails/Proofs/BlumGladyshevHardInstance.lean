import LongTails.Proofs.BlumGladyshevRidge
import LongTails.Setups.InterpolatedDistanceGrowingSubgradient
import LongTails.Proofs.BlumGladyshevMask

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace ContDiff
open LongTails.Setups.TerminalClippingConvex
open LongTails.Proofs.BlumGladyshevValley

namespace LongTails.Proofs.BlumGladyshevHardInstance

noncomputable def axis (p : Public) (e : Vector p.d) := p.R⁻¹ • e

noncomputable def common (p : Public) (e : Vector p.d) :=
  ridge (512 * p.ε) (1 / 2) (axis p e) p.x0

noncomputable def tilt (p : Public) (e w : Vector p.d) :=
  ridge (512 * p.ε) 0 (axis p (e + w)) p.x0

noncomputable def objective (p : Public) (e w x : Vector p.d) :=
  common p e x + tilt p e w x

noncomputable def baseField (p : Public) (e : Vector p.d) :=
  ridgeGradient (512 * p.ε) (1 / 2) (axis p e) p.x0

noncomputable def tiltField (p : Public) (e w : Vector p.d) :=
  ridgeGradient (512 * p.ε) 0 (axis p (e + w)) p.x0

noncomputable def loss (p : Public) (e w : Vector p.d) (q : ℝ) (z : Bool) (x : Vector p.d) :=
  common p e x + (if z then q⁻¹ else 0) * tilt p e w x

noncomputable def field (p : Public) (e w : Vector p.d) (q : ℝ) (x : Vector p.d) (z : Bool) :=
  baseField p e x + (if z then q⁻¹ else 0) • tiltField p e w x

noncomputable def point (p : Public) (e w : Vector p.d) := p.x0 + (p.R / 2) • (e - w)

lemma field_gradient (p : Public) (e w x : Vector p.d) (q : ℝ) (z : Bool) :
    HasGradientAt (loss p e w q z) (field p e w q x z) x := by
  have ha := (ridge_gradient (512 * p.ε) (1/2) (axis p e) p.x0 x).hasFDerivAt
  have hb := (ridge_gradient (512 * p.ε) 0 (axis p (e+w)) p.x0 x).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ha.add (hb.const_mul (if z then q⁻¹ else 0)) using 1
  · rfl
  · ext v
    cases z <;> simp [field, baseField, tiltField, InnerProductSpace.toDual_apply_apply]


lemma loss_smooth (p : Public) (e w : Vector p.d) (q : ℝ) (z : Bool) :
    ContDiff ℝ ∞ (loss p e w q z) :=
  (ridge_smooth _ _ _ _).add (contDiff_const.mul (ridge_smooth _ _ _ _))

lemma loss_convex (p : Public) (hε : 0 ≤ p.ε) (e w : Vector p.d) {q : ℝ}
    (hq : 0 < q) (z : Bool) : ConvexOn ℝ Set.univ (loss p e w q z) := by
  have hz : (0 : ℝ) ≤ (if z then q⁻¹ else 0) := by split <;> positivity
  exact (ridge_convex (a := 512 * p.ε) (by positivity) _ _ _).add
    ((ridge_convex (a := 512 * p.ε) (by positivity) _ _ _).smul hz)

lemma anchor_field (p : Public) (e w : Vector p.d) (q : ℝ) (z : Bool) :
    field p e w q p.x0 z = baseField p e p.x0 := by
  simp [field, tiltField, ridgeGradient]

lemma point_radius (p : Public) (hR : 0 ≤ p.R) {e w : Vector p.d} (he : ‖e‖ = 1)
    (hw : ‖w‖ = 1) : ‖p.x0 - point p e w‖ ≤ p.R := by
  simp only [point, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ p.R / 2 by positivity)]
  have h := norm_sub_le e w
  rw [he, hw] at h
  nlinarith [mul_le_mul_of_nonneg_left h hR]

lemma point_zero (p : Public) (hR : 0 < p.R) {e w : Vector p.d}
    (he : ‖e‖ = 1) (hw : ‖w‖ = 1) (hew : ⟪e,w⟫ = 0) :
    common p e (point p e w) = 0 ∧ tilt p e w (point p e w) = 0 := by
  have hwe : ⟪w,e⟫ = 0 := (real_inner_comm _ _).trans hew
  have hc : p.R / 2 * p.R⁻¹ = 2⁻¹ := by field_simp
  simp [common, tilt, ridge, axis, point, inner_add_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, he, hw, hew, hwe, hc]

lemma loss_minimum (p : Public) (hε : 0 ≤ p.ε) (hR : 0 < p.R) {e w : Vector p.d}
    (he : ‖e‖ = 1) (hw : ‖w‖ = 1) (hew : ⟪e,w⟫ = 0) {q : ℝ} (hq : 0 < q) (z : Bool) :
    IsMinOn (loss p e w q z) Set.univ (point p e w) := by
  intro x _
  have hv := point_zero p hR he hw hew
  change common p e _ + _ * tilt p e w _ ≤ common p e x + _ * tilt p e w x
  rw [hv.1, hv.2, mul_zero, add_zero]
  have hc : 0 ≤ common p e x := mul_nonneg (by positivity) (valley_nonneg _)
  have ht : 0 ≤ tilt p e w x := mul_nonneg (by positivity) (valley_nonneg _)
  exact add_nonneg hc (mul_nonneg (by split <;> positivity) ht)

lemma objective_separation (p : Public) (hε : 0 < p.ε) (e w x : Vector p.d) :
    p.ε < objective p e w x ∨ p.ε < objective p e (-w) x := by
  let t := ⟪axis p e, x - p.x0⟫
  let s := ⟪axis p w, x - p.x0⟫
  have h := separated t s
  have hp : ⟪axis p (e + w), x - p.x0⟫ = t + s := by simp [axis, t, s, smul_add, inner_add_left]
  have hm : ⟪axis p (e + -w), x - p.x0⟫ = t - s := by
    simp [axis, t, s, smul_add, inner_add_left, sub_eq_add_neg]
  unfold objective common tilt ridge
  rw [hp, hm]
  simp only [sub_zero]
  rcases h with h | h
  · left; linarith only [mul_lt_mul_of_pos_left h hε]
  · right; linarith only [mul_lt_mul_of_pos_left h hε]

end LongTails.Proofs.BlumGladyshevHardInstance
