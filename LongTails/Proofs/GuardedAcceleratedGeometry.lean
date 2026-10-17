import LongTails.Algorithms.GuardedMetricAcceleration
import LongTails.Proofs.GuardedAcceleratedEnergy

namespace LongTails.Proofs.GuardedAcceleratedGeometry

open scoped RealInnerProductSpace
open LongTails.Algorithms.GuardedMetricAcceleration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma estimate_quadratic_identity {a μ φ Fy : ℝ} (hμ : μ ≠ 0) (u y z g : E) :
    (1 - a) * (φ + μ / 2 * ‖u - z‖ ^ 2) +
      a * (Fy + ⟪g, u - y⟫ + μ / 2 * ‖u - y‖ ^ 2) =
    (1 - a) * φ + a * Fy + μ * a * (1 - a) / 2 * ‖z - y‖ ^ 2 +
      a * (1 - a) * ⟪g, z - y⟫ - a ^ 2 / (2 * μ) * ‖g‖ ^ 2 +
      μ / 2 * ‖u - centerStep a μ y z g‖ ^ 2 := by
  simp only [centerStep, norm_sub_sq_real, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm g z, real_inner_comm g y, real_inner_comm g u]
  field_simp
  ring

lemma extrapolate_cancellation {a : ℝ} (ha : 1 + a ≠ 0) (x z g : E) :
    ⟪g, x - extrapolate a x z⟫ + a * ⟪g, z - extrapolate a x z⟫ = 0 := by
  simp only [extrapolate, inner_sub_right, inner_add_right, real_inner_smul_right]
  field_simp
  ring

lemma primal_center_relation {a μ L : ℝ} (ha : 1 + a ≠ 0) (hμ : μ ≠ 0) (hL : L ≠ 0)
    (htune : a ^ 2 * L = μ) (x z g : E) :
    gradientStep L (extrapolate a x z) g =
      (1 - a) • x + a • centerStep a μ (extrapolate a x z) z g := by
  have hcoef : a * (a / μ) = L⁻¹ := by
    field_simp
    nlinarith only [htune]
  unfold gradientStep centerStep extrapolate
  module_nf
  have hc₁ : (1 - a + a ^ 2 * (1 + a)⁻¹) = (1 + a)⁻¹ := by
    field_simp
    ring
  have hc₂ : a - a ^ 2 + a ^ 3 * (1 + a)⁻¹ = a * (1 + a)⁻¹ := by
    field_simp
    ring
  have hc₃ : a ^ 2 * μ⁻¹ = L⁻¹ := by
    convert hcoef using 1
    ring
  rw [hc₁, hc₂, hc₃]

noncomputable def minimumUpdate (a μ φ Fy : ℝ) (y z g : E) : ℝ :=
  (1 - a) * φ + a * Fy + μ * a * (1 - a) / 2 * ‖z - y‖ ^ 2 +
    a * (1 - a) * ⟪g, z - y⟫ - a ^ 2 / (2 * μ) * ‖g‖ ^ 2

lemma minimum_step {a μ L φ Fx Fy Fnext : ℝ} {x z g : E}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) (hμ : 0 < μ) (hL : 0 < L)
    (htune : a ^ 2 * L = μ) (hφ : Fx ≤ φ)
    (hsupport : Fy + ⟪g, x - extrapolate a x z⟫ + μ * ‖x - extrapolate a x z‖ ^ 2 / 2 ≤ Fx)
    (hdescent : Fnext ≤ Fy - ‖g‖ ^ 2 / (2 * L)) :
    Fnext ≤ minimumUpdate a μ φ Fy (extrapolate a x z) z g := by
  have hcoef : a ^ 2 / (2 * μ) * ‖g‖ ^ 2 = ‖g‖ ^ 2 / (2 * L) := by
    field_simp
    nlinarith only [htune]
  have hh := GuardedAcceleratedEnergy.estimate_minimum_step (f₂ := Fnext) (G := ‖g‖ ^ 2) ha ha₁ hμ.le
    (sq_nonneg ‖x - extrapolate a x z‖) (sq_nonneg ‖z - extrapolate a x z‖)
    hφ hsupport (extrapolate_cancellation (by positivity) x z g) (by simpa only [hcoef] using hdescent)
  simpa only [minimumUpdate, div_mul_eq_mul_div] using hh

lemma center_step {a μ φ Fy Fc : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (hμ : μ ≠ 0) (c y z g : E)
    (hcenter : φ + μ / 2 * ‖c - z‖ ^ 2 ≤ Fc)
    (hsupport : Fy + ⟪g, c - y⟫ + μ / 2 * ‖c - y‖ ^ 2 ≤ Fc) :
    minimumUpdate a μ φ Fy y z g + μ / 2 * ‖c - centerStep a μ y z g‖ ^ 2 ≤ Fc := by
  rw [← show (1 - a) * (φ + μ / 2 * ‖c - z‖ ^ 2) +
      a * (Fy + ⟪g, c - y⟫ + μ / 2 * ‖c - y‖ ^ 2) =
      minimumUpdate a μ φ Fy y z g + μ / 2 * ‖c - centerStep a μ y z g‖ ^ 2 from
      estimate_quadratic_identity hμ c y z g]
  exact GuardedAcceleratedEnergy.estimate_center_step ha ha₁ hcenter hsupport

lemma estimate_contraction {a F q₀ : ℝ} {q : ℕ → ℝ}
    (ha₁ : a ≤ 1) (hzero : q 0 ≤ q₀)
    (hstep : ∀ k, q (k + 1) ≤ (1 - a) * q k + a * F) (n : ℕ) :
    q n ≤ (1 - a) ^ n * q₀ + (1 - (1 - a) ^ n) * F := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    have hh := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ha₁)
    have hs := hstep n
    rw [pow_succ]
    nlinarith

lemma certificate_gradient {L decay Fc Fw Fx φw μ r G : ℝ} (hL : 0 < L)
    (hdescent : Fw ≤ Fx - G / (2 * L)) (hminimum : Fx ≤ φw)
    (hestimate : φw ≤ decay * (Fc + μ * r / 2) + (1 - decay) * Fw) :
    G ≤ 2 * L * decay * (Fc - Fw + μ * r / 2) := by
  have hh : G / (2 * L) ≤ decay * (Fc - Fw + μ * r / 2) := by nlinarith
  have hp := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hh
  nlinarith only [hp]

lemma convex_radius {a A : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) (c x z : E)
    (hx : ‖x - c‖ ≤ A) (hz : ‖z - c‖ ≤ A) :
    ‖(1 - a) • x + a • z - c‖ ≤ A := by
  have he : (1 - a) • x + a • z - c = (1 - a) • (x - c) + a • (z - c) := by module
  rw [he]
  calc
    _ ≤ ‖(1 - a) • (x - c)‖ + ‖a • (z - c)‖ := norm_add_le _ _
    _ = (1 - a) * ‖x - c‖ + a * ‖z - c‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ha₁), abs_of_nonneg ha]
    _ ≤ (1 - a) * A + a * A := add_le_add
      (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ha₁)) (mul_le_mul_of_nonneg_left hz ha)
    _ = A := by ring

lemma extrapolate_radius {a A : ℝ} (ha : 0 ≤ a) (c x z : E)
    (hx : ‖x - c‖ ≤ A) (hz : ‖z - c‖ ≤ A) : ‖extrapolate a x z - c‖ ≤ A := by
  have hpos : 0 < 1 + a := by positivity
  have hcoef : 1 - a / (1 + a) = (1 + a)⁻¹ := by field_simp; ring
  have hh := convex_radius (by positivity : 0 ≤ a / (1 + a))
    ((div_le_one hpos).mpr (by linarith)) c x z hx hz
  rw [hcoef] at hh
  have he : extrapolate a x z = (1 + a)⁻¹ • x + (a / (1 + a)) • z := by
    unfold extrapolate
    module
  simpa only [he] using hh

lemma momentum_relation {a : ℝ} (ha : 1 + a ≠ 0) (previous x z : E)
    (hx : x = (1 - a) • previous + a • z) :
    extrapolate a x z = x + ((1 - a) / (1 + a)) • (x - previous) := by
  have he : x + a • z = (2 : ℝ) • x - (1 - a) • previous := by rw [hx]; module
  unfold extrapolate
  rw [he]
  module_nf
  have hc : (1 + a)⁻¹ * 2 = 1 - a * (1 + a)⁻¹ + (1 + a)⁻¹ := by
    field_simp
    ring
  rw [hc]

end LongTails.Proofs.GuardedAcceleratedGeometry
