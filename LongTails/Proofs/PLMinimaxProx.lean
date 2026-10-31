import LongTails.Proofs.PLMinimaxValue
import LongTails.Proofs.WeaklyConvexMoreau
import LongTails.Proofs.ComponentEnvelopeProx

open Set InnerProductSpace
open scoped RealInnerProductSpace
open LongTails.Setups.WeaklyConvexHeavyTailed

namespace OracleTemplate.PLMinimax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weak_prox_exists [ProperSpace E] {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : Continuous φ)
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g) (z : E) :
    ∃ x, IsMinOn (proxObj φ L z) univ x := by
  have hgrowth : ∀ x, 2 * ‖g z‖ / L + 1 + 2 * 0 / L < ‖x - z‖ →
      proxObj φ L z z ≤ proxObj φ L z x := by
    intro x hx
    have hg := TwoSidedPL.growth_radius hL le_rfl (norm_nonneg (g z)) hx
    have hl := hw z (mem_univ _) x (mem_univ _)
    have hi : -(‖g z‖ * ‖x - z‖) ≤ ⟪g z, x - z⟫ :=
      (abs_le.mp (abs_real_inner_le_norm (g z) (x - z))).1
    simp only [proxObj, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero]
    nlinarith
  obtain ⟨x, hx⟩ := TwoSidedPL.exists_min_of_growth (proxObj φ L z)
    (hc.add (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))).lowerSemicontinuous
    z (2 * ‖g z‖ / L + 1 + 2 * 0 / L) hgrowth
  exact ⟨x, fun u _ => hx u⟩

noncomputable def weakProx (φ : E → ℝ) (L : ℝ) (z : E) : E :=
  Classical.epsilon (fun x => IsMinOn (proxObj φ L z) univ x)

lemma weakProx_min [ProperSpace E] {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : Continuous φ)
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g) (z : E) :
    IsMinOn (proxObj φ L z) univ (weakProx φ L z) :=
  Classical.epsilon_spec (weak_prox_exists hL hc hw z)

lemma weakProx_lipschitz [ProperSpace E] {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : Continuous φ)
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g) (z z' : E) :
    ‖weakProx φ L z - weakProx φ L z'‖ ≤ 2 * ‖z - z'‖ :=
  WeaklyConvexHeavyTailed.prox_lipschitz (convex_univ) hw hL
    (mem_univ _) (weakProx_min hL hc hw z) (mem_univ _) (weakProx_min hL hc hw z')

lemma weakProx_growth [ProperSpace E] {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : Continuous φ)
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g) (z x : E) :
    proxObj φ L z (weakProx φ L z) + L / 2 * ‖x - weakProx φ L z‖ ^ 2 ≤ proxObj φ L z x :=
  WeaklyConvexHeavyTailed.growth_of_isMinOn (convex_univ) hw hL
    (mem_univ _) (weakProx_min hL hc hw z) (mem_univ _)

lemma weakProx_stationary [CompleteSpace E] [ProperSpace E] {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt φ (g x) x)
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g) (z : E) :
    g (weakProx φ L z) + (2 * L) • (weakProx φ L z - z) = 0 := by
  have hc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  apply ComponentEnvelope.regularized_minimum_stationary hg (2 * L) z (weakProx φ L z)
  intro x
  simpa [LongTails.Proofs.RecursiveEnvelopeGeometry.regularized, proxObj] using
    weakProx_min hL hc hw z (mem_univ x)

noncomputable def weakEnvelope (φ : E → ℝ) (L : ℝ) (z : E) : ℝ :=
  proxObj φ L z (weakProx φ L z)

lemma proxObj_center_shift (φ : E → ℝ) (L : ℝ) (z h u : E) :
    proxObj φ L (z + h) u = proxObj φ L z u + 2 * L * ⟪z - u, h⟫ + L * ‖h‖ ^ 2 := by
  have he : u - (z + h) = (u - z) - h := by abel
  unfold proxObj
  rw [he, norm_sub_sq_real]
  have hi : ⟪u - z, h⟫ = -⟪z - u, h⟫ := by rw [← inner_neg_left, neg_sub]
  rw [hi]
  ring

lemma weakEnvelope_remainder [ProperSpace E] {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : Continuous φ)
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g) (z h : E) :
    |weakEnvelope φ L (z + h) - weakEnvelope φ L z -
      ⟪(2 * L) • (z - weakProx φ L z), h⟫| ≤ 3 * L * ‖h‖ ^ 2 := by
  have hu := weakProx_min hL hc hw (z + h) (mem_univ (weakProx φ L z))
  have hl := weakProx_min hL hc hw z (mem_univ (weakProx φ L (z + h)))
  change proxObj φ L (z + h) (weakProx φ L (z + h)) ≤ proxObj φ L (z + h) (weakProx φ L z) at hu
  change proxObj φ L z (weakProx φ L z) ≤ proxObj φ L z (weakProx φ L (z + h)) at hl
  have he := proxObj_center_shift φ L z h (weakProx φ L z)
  have he' := proxObj_center_shift φ L z h (weakProx φ L (z + h))
  have hd := weakProx_lipschitz hL hc hw z (z + h)
  simp only [sub_add_cancel_left, norm_neg] at hd
  have hi := abs_real_inner_le_norm (weakProx φ L z - weakProx φ L (z + h)) h
  have hdiff : ⟪z - weakProx φ L (z + h), h⟫ = ⟪z - weakProx φ L z, h⟫ +
      ⟪weakProx φ L z - weakProx φ L (z + h), h⟫ := by
    simp only [inner_sub_left]
    ring
  have hb : -2 * ‖h‖ ^ 2 ≤ ⟪weakProx φ L z - weakProx φ L (z + h), h⟫ := by
    have hh := (abs_le.mp hi).1
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg h)]
  rw [hdiff] at he'
  unfold weakEnvelope
  rw [real_inner_smul_left, abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * L by positivity),
    mul_nonneg hL.le (sq_nonneg ‖h‖)]

lemma weakEnvelope_hasGradient [CompleteSpace E] [ProperSpace E] {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : Continuous φ)
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g) (z : E) :
    HasGradientAt (weakEnvelope φ L) ((2 * L) • (z - weakProx φ L z)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  apply hasFDerivAt_of_quadratic_remainder (C := 3 * L)
  intro h
  simpa [Real.norm_eq_abs, real_inner_smul_left, inner_sub_left] using weakEnvelope_remainder hL hc hw z h

lemma proxObj_lower {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g) (z x x' : E) :
    proxObj φ L z x + ⟪g x + (2 * L) • (x - z), x' - x⟫ + L / 2 * ‖x' - x‖ ^ 2 ≤
      proxObj φ L z x' := by
  have hh := hw x (mem_univ _) x' (mem_univ _)
  have he := TwoSidedPL.norm_sq_expand x x' z
  simp only [proxObj, inner_add_left, real_inner_smul_left]
  rw [he]
  nlinarith

lemma proxObj_min_of_stationary {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 ≤ L) (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g)
    {z x : E} (hx : g x + (2 * L) • (x - z) = 0) :
    IsMinOn (proxObj φ L z) univ x := by
  intro x' _
  change proxObj φ L z x ≤ proxObj φ L z x'
  have hh := proxObj_lower hw z x x'
  rw [hx, inner_zero_left, add_zero] at hh
  nlinarith [mul_nonneg hL (sq_nonneg ‖x' - x‖)]

lemma proxObj_residual_distance {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g)
    {z p : E} (hp : g p + (2 * L) • (p - z) = 0) (x : E) :
    L * ‖x - p‖ ≤ ‖g x + (2 * L) • (x - z)‖ := by
  have h₁ := proxObj_lower hw z p x
  have h₂ := proxObj_lower hw z x p
  rw [hp, inner_zero_left, add_zero] at h₁
  have hi : ⟪g x + (2 * L) • (x - z), p - x⟫ =
      -⟪g x + (2 * L) • (x - z), x - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [hi, norm_sub_rev p x] at h₂
  have hb := real_inner_le_norm (g x + (2 * L) • (x - z)) (x - p)
  have hn := norm_nonneg (x - p)
  by_cases hz : ‖x - p‖ = 0
  · simp [hz]
  · have hn' : 0 < ‖x - p‖ := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

lemma proxObj_gap_bound {φ : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hw : WeaklyConvexHeavyTailed.WeakSubgradientOn univ L φ g)
    (z x p : E) :
    proxObj φ L z x - proxObj φ L z p ≤ ‖g x + (2 * L) • (x - z)‖ ^ 2 / (2 * L) := by
  have hh := proxObj_lower hw z x p
  have hi := (abs_le.mp (abs_real_inner_le_norm (g x + (2 * L) • (x - z)) (p - x))).1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (L * ‖p - x‖ - ‖g x + (2 * L) • (x - z)‖)]

end OracleTemplate.PLMinimax
