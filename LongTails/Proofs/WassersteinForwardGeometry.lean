import LongTails.Proofs.WassersteinAccelerationEnergy
import Mathlib.Topology.MetricSpace.Contracting

open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.WassersteinForwardGeometry

lemma forward_norm_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (h L : ℝ) (hh : 0 ≤ h)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    (1 - h * L) * ‖x - y‖ ≤ ‖(x - h • g x) - (y - h • g y)‖ := by
  have hn : ‖h • (g x - g y)‖ ≤ h * L * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    nlinarith [hg x y]
  have he : (x - h • g x) - (y - h • g y) = (x - y) - h • (g x - g y) := by
    module
  rw [he]
  have hd := norm_sub_norm_le (x - y) (h • (g x - g y))
  nlinarith

lemma forward_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (h L : ℝ) (hh : 0 ≤ h) (hsmall : h * L < 1)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) :
    Function.Injective (fun x => x - h • g x) := by
  intro x y he
  have hn := forward_norm_lower g h L hh hg x y
  change x - h • g x = y - h • g y at he
  rw [he, sub_self, norm_zero] at hn
  have hz : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma forward_surjective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (g : E → E) (h L : ℝ) (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : h * L < 1) (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) :
    Function.Surjective (fun x => x - h • g x) := by
  intro y
  let K : ℝ≥0 := ⟨h * L, mul_nonneg hh hL⟩
  have hc : ContractingWith K (fun x => y + h • g x) := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul ?_⟩
    intro x z
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hh]
    change h * ‖g x - g z‖ ≤ h * L * ‖x - z‖
    nlinarith [hg x z]
  refine ⟨hc.fixedPoint (fun x => y + h • g x), ?_⟩
  have hf := hc.fixedPoint_isFixedPt
  change y + h • g (hc.fixedPoint _) = hc.fixedPoint _ at hf
  exact sub_eq_iff_eq_add.mpr hf.symm

lemma forward_inverse {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (g : E → E) (h L : ℝ) (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : h * L < 1) (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) :
    ∃ B : E → E,
      Function.LeftInverse B (fun x => x - h • g x) ∧
      Function.RightInverse B (fun x => x - h • g x) ∧
      ∀ x y, ‖B x - B y‖ ≤ ‖x - y‖ / (1 - h * L) := by
  let e := Equiv.ofBijective (fun x => x - h • g x)
    ⟨forward_injective g h L hh hsmall hg,
      forward_surjective g h L hh hL hsmall hg⟩
  refine ⟨e.symm, e.symm_apply_apply, e.apply_symm_apply, ?_⟩
  intro x y
  have hn := forward_norm_lower g h L hh hg (e.symm x) (e.symm y)
  change (1 - h * L) * ‖e.symm x - e.symm y‖ ≤ ‖e (e.symm x) - e (e.symm y)‖ at hn
  rw [e.apply_symm_apply, e.apply_symm_apply] at hn
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).mpr
  nlinarith

lemma forward_continuous_inverse {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (g : E → E) (h L : ℝ)
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hsmall : h * L < 1)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) :
    ∃ B : E → E, Continuous B ∧
      Function.LeftInverse B (fun x => x - h • g x) ∧
      Function.RightInverse B (fun x => x - h • g x) := by
  obtain ⟨B, hleft, hright, hbound⟩ := forward_inverse g h L hh hL hsmall hg
  refine ⟨B, ?_, hleft, hright⟩
  let K : ℝ≥0 := ⟨(1 - h * L)⁻¹, inv_nonneg.mpr (le_of_lt (sub_pos.mpr hsmall))⟩
  have hb : LipschitzWith K B := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm]
    change ‖B x - B y‖ ≤ (1 - h * L)⁻¹ * ‖x - y‖
    simpa only [div_eq_mul_inv, mul_comm] using hbound x y
  exact hb.continuous

lemma forward_squared_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x z g : E) (h : ℝ) :
    ‖x - h • g - z‖ ^ 2 = ‖x - z‖ ^ 2 - 2 * h * ⟪g, x - z⟫ +
      h ^ 2 * ‖g‖ ^ 2 := by
  have he : x - h • g - z = (x - z) - h • g := by module
  rw [he]
  simp only [norm_sub_sq_real, inner_smul_right, real_inner_comm (x - z) g,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma forward_convex_cost {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : E → ℝ) (x v g : E) (h : ℝ) (hh : 0 ≤ h)
    (hconv : V x + ⟪g, v - x⟫ ≤ V v) :
    ‖x - h • g - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 - 2 * h * (V x - V v) +
      h ^ 2 * ‖g‖ ^ 2 := by
  rw [forward_squared_norm]
  have hi : ⟪g, v - x⟫ = -⟪g, x - v⟫ := by
    rw [← neg_sub x v, inner_neg_right]
  rw [hi] at hconv
  nlinarith

lemma forward_smooth_cost {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : E → ℝ) (x u g : E) (h L : ℝ) (hh : 0 ≤ h)
    (hsmooth : V u ≤ V x + ⟪g, u - x⟫ + L / 2 * ‖u - x‖ ^ 2) :
    2 * h * (V u - V x) ≤ ‖x - h • g - u‖ ^ 2 -
      (1 - h * L) * ‖x - u‖ ^ 2 - h ^ 2 * ‖g‖ ^ 2 := by
  rw [forward_squared_norm]
  have hi : ⟪g, u - x⟫ = -⟪g, x - u⟫ := by
    rw [← neg_sub x u, inner_neg_right]
  rw [hi, norm_sub_rev u x] at hsmooth
  nlinarith

end LongTails.Proofs.WassersteinForwardGeometry
