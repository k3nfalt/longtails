import LongTails.Proofs.GradientOnlyTests

namespace LongTails.Proofs.GradientOnlyGeometry

open scoped RealInnerProductSpace
open LongTails.Algorithms.GradientOnlyGuarded LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.GuardedAcceleratedGeometry LongTails.Proofs.GradientOnlyAgd
open LongTails.Proofs.GradientOnlyTests

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Valid (t : Tuning) : Prop where
  α_pos : 0 < t.α
  L_pos : 0 < t.L
  μ_eq : t.μ = t.α / 2
  a_nonneg : 0 ≤ t.a
  a_le : t.a ≤ 1
  tune : t.a ^ 2 * t.L = t.μ
  R_nonneg : 0 ≤ t.R

lemma xs_zero (t : Tuning) (g : E → E) (c : E) : xs t g c 0 = c := (agd_zero t g c).1

lemma ys_zero (t : Tuning) (hv : Valid t) (g : E → E) (c : E) : ys t g c 0 = c := by
  have hpos : (1 : ℝ) + t.a ≠ 0 := (show (0 : ℝ) < 1 + t.a by linarith [hv.a_nonneg]).ne'
  have h : zs t g c 0 = c := (agd_zero t g c).2
  unfold ys extrapolate
  rw [xs_zero, h, show c + t.a • c = (1 + t.a) • c by module, smul_smul, inv_mul_cancel₀ hpos,
    one_smul]

lemma xs_primal (t : Tuning) (hv : Valid t) (g : E → E) (c : E) (k : ℕ) (hk : k < t.N) :
    xs t g c (k + 1) = (1 - t.a) • xs t g c k + t.a • zs t g c (k + 1) := by
  rw [xs_succ t g c k hk, zs_succ t g c k hk]
  exact primal_center_relation (show (0 : ℝ) < 1 + t.a by linarith [hv.a_nonneg]).ne'
    (show (0 : ℝ) < t.μ by rw [hv.μ_eq]; linarith [hv.α_pos]).ne'
    hv.L_pos.ne' hv.tune _ _ _

lemma ys_momentum (t : Tuning) (hv : Valid t) (g : E → E) (c : E) (k : ℕ) (hk : k < t.N) :
    ys t g c (k + 1) = xs t g c (k + 1) +
      ((1 - t.a) / (1 + t.a)) • (xs t g c (k + 1) - xs t g c k) :=
  momentum_relation (show (0 : ℝ) < 1 + t.a by linarith [hv.a_nonneg]).ne' _ _ _ (xs_primal t hv g c k hk)

lemma ys_close (t : Tuning) (hv : Valid t) (g : E → E) (c : E) {A : ℝ} (k : ℕ) (hkN : k < t.N)
    (hk : ‖xs t g c (k + 1) - c‖ ≤ A) (hk' : ‖xs t g c k - c‖ ≤ A) :
    ‖ys t g c (k + 1) - c‖ ≤ 3 * A := by
  rw [ys_momentum t hv g c k hkN]
  set θ := (1 - t.a) / (1 + t.a)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hv.a_le]) (by linarith [hv.a_nonneg])
  have hθ1 : θ ≤ 1 := (div_le_one (by linarith [hv.a_nonneg])).mpr (by linarith [hv.a_nonneg])
  have he : xs t g c (k + 1) + θ • (xs t g c (k + 1) - xs t g c k) - c =
      (1 + θ) • (xs t g c (k + 1) - c) - θ • (xs t g c k - c) := by module
  rw [he]
  calc
    _ ≤ ‖(1 + θ) • (xs t g c (k + 1) - c)‖ + ‖θ • (xs t g c k - c)‖ := norm_sub_le _ _
    _ = (1 + θ) * ‖xs t g c (k + 1) - c‖ + θ * ‖xs t g c k - c‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
        abs_of_nonneg hθ0]
    _ ≤ (1 + θ) * A + θ * A := by gcongr
    _ ≤ 3 * A := by
      have hA : 0 ≤ A := (norm_nonneg _).trans hk
      nlinarith

end LongTails.Proofs.GradientOnlyGeometry
