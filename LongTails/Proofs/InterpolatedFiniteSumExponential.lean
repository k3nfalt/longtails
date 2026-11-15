import LongTails.Proofs.InterpolatedFiniteSumCentering
import LongTails.Proofs.InterpolatedFiniteSumChains
import LongTails.Proofs.HiddenDecompositionEnergy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.InterpolatedFiniteSumExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def value (m : E → ℝ) (v : E) (C : ℝ) (x : E) : ℝ :=
  C * (Real.exp (m x + ⟪v, x⟫) - 1)

noncomputable def field (m : E → ℝ) (g : E → E) (v : E) (C : ℝ) (x : E) : E :=
  (C * Real.exp (m x + ⟪v, x⟫)) • (g x + v)

lemma exponent_gradient (m : E → ℝ) (g : E → E) (v x : E)
    (hm : HasGradientAt m (g x) x) :
    HasGradientAt (fun y => m y + ⟪v, y⟫) (g x + v) x := by
  rw [hasGradientAt_iff_hasFDerivAt, map_add]
  exact hm.hasFDerivAt.add (InnerProductSpace.toDual ℝ E v).hasFDerivAt

lemma value_gradient (m : E → ℝ) (g : E → E) (v : E) (C : ℝ) (x : E)
    (hm : HasGradientAt m (g x) x) : HasGradientAt (value m v C) (field m g v C x) x := by
  have hd := (((exponent_gradient m g v x hm).hasFDerivAt.exp).sub_const 1).const_mul C
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext y
    simp only [field, InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, smul_eq_mul]
    ring

lemma field_hasFDerivAt (m : E → ℝ) (g : E → E) (v : E) (C : ℝ) (x : E)
    (A : E →L[ℝ] E) (hm : HasGradientAt m (g x) x) (hg : HasFDerivAt g A x) :
    HasFDerivAt (field m g v C)
      ((C * Real.exp (m x + ⟪v, x⟫)) • A +
        ((C * Real.exp (m x + ⟪v, x⟫)) • (InnerProductSpace.toDual ℝ E (g x + v))).smulRight
          (g x + v)) x := by
  have hd := (((exponent_gradient m g v x hm).hasFDerivAt.exp).const_mul C).smul (hg.add_const v)
  convert hd using 1
  · rfl
  · simp only [smul_smul]

lemma field_curvature (m : E → ℝ) (g : E → E) (v : E) (C : ℝ) (hC : 0 ≤ C)
    (x : E) (A : E →L[ℝ] E) (hm : HasGradientAt m (g x) x) (hg : HasFDerivAt g A x) :
    ‖fderiv ℝ (field m g v C) x‖ ≤
      C * Real.exp (m x + ⟪v, x⟫) * (‖A‖ + ‖g x + v‖ ^ 2) := by
  have hs : 0 ≤ C * Real.exp (m x + ⟪v, x⟫) := mul_nonneg hC (Real.exp_pos _).le
  rw [(field_hasFDerivAt m g v C x A hm hg).fderiv]
  have hb := norm_add_le ((C * Real.exp (m x + ⟪v, x⟫)) • A)
    (((C * Real.exp (m x + ⟪v, x⟫)) • (InnerProductSpace.toDual ℝ E (g x + v))).smulRight (g x + v))
  rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_smul,
    Real.norm_of_nonneg hs, (InnerProductSpace.toDual ℝ E).norm_map] at hb
  nlinarith

omit [CompleteSpace E] in
lemma value_convex (m : E → ℝ) (v : E) (C : ℝ) (hC : 0 ≤ C)
    (hm : ConvexOn ℝ Set.univ m) : ConvexOn ℝ Set.univ (value m v C) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h₁ := hm.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have h₂ := convexOn_exp.2 (Set.mem_univ (m x + ⟪v, x⟫))
    (Set.mem_univ (m y + ⟪v, y⟫)) ha hb hab
  have h₃ : Real.exp (m (a • x + b • y) + ⟪v, a • x + b • y⟫) ≤
      Real.exp (a * (m x + ⟪v, x⟫) + b * (m y + ⟪v, y⟫)) := by
    apply Real.exp_le_exp.mpr
    simp only [inner_add_right, inner_smul_right, smul_eq_mul] at *
    nlinarith
  have h₄ := mul_le_mul_of_nonneg_left (h₃.trans h₂) hC
  simp only [smul_eq_mul] at h₄
  simp only [value, smul_eq_mul]
  nlinarith

lemma field_relative_curvature (m : E → ℝ) (g : E → E) (v : E) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (x : E)
    (hm : HasGradientAt m (g x) x) (hg : DifferentiableAt ℝ g x)
    (hgn : ‖g x‖ ≤ L / 7) (hv : ‖v‖ = 2 * L / 7)
    (hgc : ‖fderiv ℝ g x‖ ≤ 4 * L ^ 2 / 49) :
    ‖fderiv ℝ (field m g v C) x‖ ≤ L * ‖field m g v C x‖ := by
  have hu : ‖g x + v‖ ≤ 3 * L / 7 := by
    have h := norm_add_le (g x) v
    rw [hv] at h
    linarith
  have hl : L / 7 ≤ ‖g x + v‖ := by
    have h := norm_sub_le (g x + v) (g x)
    have he : g x + v - g x = v := by abel
    rw [he, hv] at h
    linarith
  have hh : ‖fderiv ℝ g x‖ + ‖g x + v‖ ^ 2 ≤ L * ‖g x + v‖ := by
    have h₁ := mul_le_mul_of_nonneg_left hl (show 0 ≤ 4 * L / 7 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hu (norm_nonneg (g x + v))
    nlinarith
  have hs : 0 ≤ C * Real.exp (m x + ⟪v, x⟫) := mul_nonneg hC (Real.exp_pos _).le
  have hb := field_curvature m g v C hC x (fderiv ℝ g x) hm hg.hasFDerivAt
  have hbound := mul_le_mul_of_nonneg_left hh hs
  simp only [field, norm_smul, Real.norm_of_nonneg hs]
  nlinarith

noncomputable def centeredValue (m : E → ℝ) (v : E) (C : ℝ) : E → ℝ :=
  InterpolatedFiniteSumCentering.centered (value m v C) (C • v)

noncomputable def centeredField (m : E → ℝ) (g : E → E) (v : E) (C : ℝ) (x : E) : E :=
  field m g v C x - C • v

lemma centeredValue_gradient (m : E → ℝ) (g : E → E) (v : E) (C : ℝ) (x : E)
    (hm : HasGradientAt m (g x) x) :
    HasGradientAt (centeredValue m v C) (centeredField m g v C x) x :=
  InterpolatedFiniteSumCentering.centered_gradient (value m v C) (field m g v C) (C • v) x
    (value_gradient m g v C x hm)

lemma centeredField_curvature (m : E → ℝ) (g : E → E) (v : E) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (x : E)
    (hm : HasGradientAt m (g x) x) (hg : DifferentiableAt ℝ g x)
    (hgn : ‖g x‖ ≤ L / 7) (hv : ‖v‖ = 2 * L / 7)
    (hgc : ‖fderiv ℝ g x‖ ≤ 4 * L ^ 2 / 49) :
    ‖fderiv ℝ (centeredField m g v C) x‖ ≤
      2 * C * L ^ 2 / 7 + L * ‖centeredField m g v C x‖ := by
  have hb := InterpolatedFiniteSumCentering.centered_curvature (field m g v C) (C • v) x 0 L hL
    (by simpa only [zero_add] using field_relative_curvature m g v C L hC hL x hm hg hgn hv hgc)
  rw [norm_smul, Real.norm_of_nonneg hC, hv] at hb
  change ‖fderiv ℝ (fun y => field m g v C y - C • v) x‖ ≤
    2 * C * L ^ 2 / 7 + L * ‖field m g v C x - C • v‖
  nlinarith

omit [CompleteSpace E] in
lemma centeredValue_at_minimizer (m : E → ℝ) (v : E) (C : ℝ) (z : E)
    (hm : m z = 0) (hv : ⟪v, z⟫ = 0) : centeredValue m v C z = 0 := by
  simp [centeredValue, InterpolatedFiniteSumCentering.centered, value, hm, hv,
    real_inner_smul_left]

omit [CompleteSpace E] in
lemma centeredValue_nonnegative (m : E → ℝ) (v : E) (C : ℝ) (hC : 0 ≤ C)
    (x : E) (hm : 0 ≤ m x) : 0 ≤ centeredValue m v C x := by
  have h := Real.add_one_le_exp (m x + ⟪v, x⟫)
  have hh := mul_le_mul_of_nonneg_left h hC
  have hp := mul_nonneg hC hm
  simp only [centeredValue, InterpolatedFiniteSumCentering.centered, value, real_inner_smul_left]
  nlinarith

omit [CompleteSpace E] in
lemma centeredValue_minimizer (m : E → ℝ) (v : E) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ x, 0 ≤ m x) (z : E) (hz : m z = 0) (hvz : ⟪v, z⟫ = 0) :
    IsMinOn (centeredValue m v C) Set.univ z := by
  intro x _
  change centeredValue m v C z ≤ centeredValue m v C x
  rw [centeredValue_at_minimizer m v C z hz hvz]
  exact centeredValue_nonnegative m v C hC x (hm x)

omit [CompleteSpace E] in
lemma centered_pair_lower (m : E → ℝ) (v : E) (C : ℝ) (hC : 0 ≤ C) (x : E) :
    2 * C * (Real.exp (m x) - 1) ≤ centeredValue m v C x + centeredValue m (-v) C x := by
  have hp := Real.add_one_le_exp ⟪v, x⟫
  have hn := Real.add_one_le_exp (-⟪v, x⟫)
  have hsum : 2 ≤ Real.exp ⟪v, x⟫ + Real.exp (-⟪v, x⟫) := by linarith
  have hh := mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (Real.exp_pos (m x)).le)
  simp only [centeredValue, InterpolatedFiniteSumCentering.centered, value, inner_neg_left,
    real_inner_smul_left, Real.exp_add]
  nlinarith

omit [CompleteSpace E] in
lemma centered_pair_zero_carrier (m : E → ℝ) (v : E) (C : ℝ) (x : E) (hx : ⟪v, x⟫ = 0) :
    centeredValue m v C x + centeredValue m (-v) C x = 2 * C * (Real.exp (m x) - 1) := by
  simp only [centeredValue, InterpolatedFiniteSumCentering.centered, value, inner_neg_left,
    real_inner_smul_left, hx, neg_zero, mul_zero, add_zero, sub_zero]
  ring

lemma exponential_conjugate_bound (t z : ℝ) (ht : 0 ≤ t) (hz : 0 ≤ z) :
    t * z - (Real.exp z - 1) ≤ t * max 0 (Real.log t) := by
  by_cases ht1 : t ≤ 1
  · have he := Real.add_one_le_exp z
    have hm := mul_le_mul_of_nonneg_right ht1 hz
    have hp := mul_nonneg ht (le_max_left 0 (Real.log t))
    nlinarith
  · have ht0 : 0 < t := by linarith
    have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (z - Real.log t)) ht
    have hexp : t * Real.exp (z - Real.log t) = Real.exp z := by
      rw [Real.exp_sub, Real.exp_log ht0]
      field_simp
    rw [hexp] at he
    have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    rw [max_eq_right hlog]
    nlinarith

noncomputable def linkPotential (L u : ℝ) : ℝ :=
  InterpolatedFiniteSumProfiles.profile (L * u / 2) / 128

lemma linkPotential_nonnegative (L u : ℝ) : 0 ≤ linkPotential L u :=
  div_nonneg (InterpolatedFiniteSumProfiles.profile_nonnegative _) (by norm_num)

lemma linkPotential_support (L u : ℝ) : (L * u - 1) / 256 ≤ linkPotential L u := by
  have h := InterpolatedFiniteSumChains.profile_support_one (L * u / 2)
  dsimp [linkPotential]
  linarith

lemma link_conjugate_bound (s L u : ℝ) (hs : 0 ≤ s) (hL : 0 < L) :
    s * u - (Real.exp (linkPotential L u) - 1) ≤
      256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L)))) := by
  let t := 256 * (s / L)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hlog : 0 ≤ max 0 (Real.log t) := le_max_left _ _
  have he : 1 ≤ Real.exp (linkPotential L u) := Real.one_le_exp (linkPotential_nonnegative L u)
  by_cases hu : u ≤ 1 / L
  · have hm := mul_le_mul_of_nonneg_left hu hs
    have hμ : s / L ≤ t := by dsimp [t]; have := div_nonneg hs hL.le; linarith
    change s * u - (Real.exp (linkPotential L u) - 1) ≤ t * (1 + max 0 (Real.log t))
    have hp := mul_nonneg ht hlog
    simp only [div_eq_mul_inv] at hm hμ
    nlinarith only [hm, hμ, hp, he]
  · let z := (L * u - 1) / 256
    have hz : 0 ≤ z := by
      have hh : 1 < L * u := by
        have := (div_lt_iff₀ hL).mp (lt_of_not_ge hu)
        nlinarith only [this]
      dsimp [z]
      positivity
    have hzφ : z ≤ linkPotential L u := linkPotential_support L u
    have hez : Real.exp z ≤ Real.exp (linkPotential L u) := Real.exp_le_exp.mpr hzφ
    have hc := exponential_conjugate_bound t z ht hz
    have hsu : s * u = t * z + s / L := by
      dsimp [t, z]
      field_simp
      ring
    have hμ : s / L ≤ t := by dsimp [t]; have := div_nonneg hs hL.le; linarith
    change s * u - (Real.exp (linkPotential L u) - 1) ≤ t * (1 + max 0 (Real.log t))
    rw [hsu]
    nlinarith only [hc, hez, hμ]

lemma centeredField_differentiable (m : E → ℝ) (g : E → E) (v : E) (C : ℝ)
    (hm : ∀ x, HasGradientAt m (g x) x) (hg : Differentiable ℝ g) :
    Differentiable ℝ (centeredField m g v C) := by
  intro x
  exact ((field_hasFDerivAt m g v C x (fderiv ℝ g x) (hm x)
    (hg x).hasFDerivAt).differentiableAt).sub_const (C • v)

omit [CompleteSpace E] in
lemma centeredValue_convex (m : E → ℝ) (v : E) (C : ℝ) (hC : 0 ≤ C)
    (hm : ConvexOn ℝ Set.univ m) : ConvexOn ℝ Set.univ (centeredValue m v C) :=
  InterpolatedFiniteSumCentering.centered_convex _ _ (value_convex m v C hC hm)

omit [CompleteSpace E] in
lemma centeredValue_zero (m : E → ℝ) (v : E) (C : ℝ) :
    centeredValue m v C 0 = C * (Real.exp (m 0) - 1) := by
  simp [centeredValue, InterpolatedFiniteSumCentering.centered, value]

end LongTails.Proofs.InterpolatedFiniteSumExponential
