import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveAnalysis

lemma hasFDerivAt_of_model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {L : E →L[ℝ] ℝ} {z : E} {C : ℝ} (h : ∀ w, |f w - f z - L (w - z)| ≤ C * ‖w - z‖ ^ 2) :
    HasFDerivAt f L z := by
  apply HasFDerivAt.of_isLittleO
  have hb : (fun w => f w - f z - L (w - z)) =O[𝓝 z] (fun w => ‖w - z‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound |C|
    filter_upwards [] with w
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖w - z‖)]
    exact (h w).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _))
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub z (by norm_num))

lemma pair_lipschitz {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : E → F → ℝ) (gx : E → F → E) (gy : E → F → F)
    (S : Set (E × F)) (K : ℝ) (hK : 0 ≤ K)
    (hmod : ∀ z ∈ S, ∀ x' y', |f x' y' - f z.1 z.2 - ⟪gx z.1 z.2, x' - z.1⟫ - ⟪gy z.1 z.2, y' - z.2⟫| ≤
      K * (‖x' - z.1‖ ^ 2 + ‖y' - z.2‖ ^ 2))
    (z z' : E × F) (hz : z ∈ S) (hz' : z' ∈ S) :
    ‖gx z.1 z.2 - gx z'.1 z'.2‖ ^ 2 + ‖gy z.1 z.2 - gy z'.1 z'.2‖ ^ 2 ≤
      (6 * K) ^ 2 * (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := by
  set hx := gx z'.1 z'.2 - gx z.1 z.2
  set hy := gy z'.1 z'.2 - gy z.1 z.2
  set H := ‖hx‖ ^ 2 + ‖hy‖ ^ 2
  set D2 := ‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2
  have hH0 : 0 ≤ H := by positivity
  have hD0 : 0 ≤ D2 := by positivity
  have e1 : ‖gx z.1 z.2 - gx z'.1 z'.2‖ = ‖hx‖ := norm_sub_rev _ _
  have e2 : ‖gy z.1 z.2 - gy z'.1 z'.2‖ = ‖hy‖ := norm_sub_rev _ _
  rw [e1, e2]
  rcases eq_or_lt_of_le hH0 with hH | hH
  · have h0 : ‖hx‖ ^ 2 + ‖hy‖ ^ 2 = 0 := hH.symm
    rw [h0]; positivity
  set D := Real.sqrt D2
  set R := Real.sqrt H
  have hR : 0 < R := Real.sqrt_pos.mpr hH
  have hR2 : R ^ 2 = H := Real.sq_sqrt hH0
  have hD2 : D ^ 2 = D2 := Real.sq_sqrt hD0
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  set t := D / R
  set vx := t • hx
  set vy := t • hy
  have ht0 : 0 ≤ t := by positivity
  have htH : t ^ 2 * H = D2 := by
    have : t ^ 2 = D2 / H := by simp only [t, div_pow, hR2, hD2]
    rw [this, div_mul_cancel₀ _ hH.ne']
  have htR : t * H = D * R := by
    simp only [t]; rw [← hR2]; field_simp
  have hv : ‖vx‖ ^ 2 + ‖vy‖ ^ 2 = D2 := by
    simp only [vx, vy, norm_smul, mul_pow, Real.norm_of_nonneg ht0]
    rw [← mul_add]; exact htH
  have hinner : ⟪hx, vx⟫ + ⟪hy, vy⟫ = D * R := by
    simp only [vx, vy, inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← mul_add]; exact htR
  have m1 := hmod z hz (z'.1 + vx) (z'.2 + vy)
  have m2 := hmod z' hz' (z'.1 + vx) (z'.2 + vy)
  have m3 := hmod z hz z'.1 z'.2
  simp only [add_sub_cancel_left] at m2
  have hsq1 : ‖z'.1 + vx - z.1‖ ^ 2 ≤ 2 * ‖z'.1 - z.1‖ ^ 2 + 2 * ‖vx‖ ^ 2 := by
    have := norm_add_le (z'.1 - z.1) vx
    have e : z'.1 + vx - z.1 = z'.1 - z.1 + vx := by abel
    rw [e]
    nlinarith [norm_nonneg (z'.1 - z.1 + vx), norm_nonneg (z'.1 - z.1), norm_nonneg vx,
      sq_nonneg (‖z'.1 - z.1‖ - ‖vx‖)]
  have hsq2 : ‖z'.2 + vy - z.2‖ ^ 2 ≤ 2 * ‖z'.2 - z.2‖ ^ 2 + 2 * ‖vy‖ ^ 2 := by
    have := norm_add_le (z'.2 - z.2) vy
    have e : z'.2 + vy - z.2 = z'.2 - z.2 + vy := by abel
    rw [e]
    nlinarith [norm_nonneg (z'.2 - z.2 + vy), norm_nonneg (z'.2 - z.2), norm_nonneg vy,
      sq_nonneg (‖z'.2 - z.2‖ - ‖vy‖)]
  have n1 : ‖z'.1 - z.1‖ = ‖z.1 - z'.1‖ := norm_sub_rev _ _
  have n2 : ‖z'.2 - z.2‖ = ‖z.2 - z'.2‖ := norm_sub_rev _ _
  have lin1 : ⟪gx z.1 z.2, z'.1 + vx - z.1⟫ = ⟪gx z.1 z.2, z'.1 - z.1⟫ + ⟪gx z.1 z.2, vx⟫ := by
    rw [show z'.1 + vx - z.1 = z'.1 - z.1 + vx by abel, inner_add_right]
  have lin2 : ⟪gy z.1 z.2, z'.2 + vy - z.2⟫ = ⟪gy z.1 z.2, z'.2 - z.2⟫ + ⟪gy z.1 z.2, vy⟫ := by
    rw [show z'.2 + vy - z.2 = z'.2 - z.2 + vy by abel, inner_add_right]
  have dx : ⟪hx, vx⟫ = ⟪gx z'.1 z'.2, vx⟫ - ⟪gx z.1 z.2, vx⟫ := by simp only [hx, inner_sub_left]
  have dy : ⟪hy, vy⟫ = ⟪gy z'.1 z'.2, vy⟫ - ⟪gy z.1 z.2, vy⟫ := by simp only [hy, inner_sub_left]
  rw [lin1, lin2] at m1
  have a1 := abs_le.mp m1
  have a2 := abs_le.mp m2
  have a3 := abs_le.mp m3
  rw [n1] at hsq1
  rw [n2] at hsq2
  have hk1 : K * (‖z'.1 + vx - z.1‖ ^ 2 + ‖z'.2 + vy - z.2‖ ^ 2) ≤ K * (4 * D2) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  have hk2 : K * (‖vx‖ ^ 2 + ‖vy‖ ^ 2) = K * D2 := by rw [hv]
  have hk3 : K * (‖z'.1 - z.1‖ ^ 2 + ‖z'.2 - z.2‖ ^ 2) = K * D2 := by rw [n1, n2]
  rw [hk2] at a2
  rw [hk3] at a3
  have key : D * R ≤ 6 * K * D2 := by linarith
  have hDR : R ≤ 6 * K * D := by
    rcases eq_or_lt_of_le hD with h0 | h0
    · exfalso
      have hD20 : D2 = 0 := by rw [← hD2, ← h0]; ring
      have e1 : ‖z.1 - z'.1‖ ^ 2 = 0 := by
        have := sq_nonneg ‖z.2 - z'.2‖; have := sq_nonneg ‖z.1 - z'.1‖; linarith
      have e2 : ‖z.2 - z'.2‖ ^ 2 = 0 := by
        have := sq_nonneg ‖z.2 - z'.2‖; have := sq_nonneg ‖z.1 - z'.1‖; linarith
      have z1 : z.1 = z'.1 := sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1))
      have z2 : z.2 = z'.2 := sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2))
      have : hx = 0 := by simp only [hx, z1, z2, sub_self]
      have : hy = 0 := by simp only [hy, z1, z2, sub_self]
      have : H = 0 := by simp [H, *]
      linarith
    · have : D * R ≤ D * (6 * K * D) := by
        rw [show D * (6 * K * D) = 6 * K * D ^ 2 by ring, hD2]; exact key
      exact le_of_mul_le_mul_left this h0
  have hR6 : R ^ 2 ≤ (6 * K * D) ^ 2 := pow_le_pow_left₀ hR.le hDR 2
  rw [hR2] at hR6
  calc H ≤ (6 * K * D) ^ 2 := hR6
    _ = (6 * K) ^ 2 * D2 := by rw [mul_pow, hD2]

lemma sum_comp_le {α β : Type*} [Fintype α] [Fintype β] (φ : α → β) (hφ : Function.Injective φ)
    (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) : ∑ a, g (φ a) ≤ ∑ b, g b := by
  classical
  rw [← Finset.sum_image (fun a _ b _ h => hφ h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hg b

end LongTails.Proofs.NcConcaveAnalysis
