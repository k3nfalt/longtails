import LongTails.Proofs.StochasticEqualityGeometry
import LongTails.Proofs.StochasticEqualityMerit
import LongTails.Proofs.HeavyTailedPLStep

namespace LongTails.Proofs.StochasticEqualityDescent

open LongTails.Algorithms.StochasticEqualityDirection
open LongTails.Proofs.StochasticEqualityMerit
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def merit (f : E → ℝ) (c : E → F) (J : E → F →L[ℝ] E)
    (g : E → E) (β : ℝ) (x : E) : ℝ :=
  f x + ⟪multiplier (J x) (g x), c x⟫ + β * ‖c x‖ ^ 2 / 2

lemma constraint_model {c : E → F} {J : E → F →L[ℝ] E} {Lc LJ : ℝ}
    (hLJ : 0 ≤ LJ) (hc : ∀ x, HasFDerivAt c (J x).adjoint x)
    (hJn : ∀ x, ‖J x‖ ≤ Lc)
    (hJL : ∀ x y, ‖J y - J x‖ ≤ LJ * ‖y - x‖) (x y : E) :
    ‖c y - c x‖ ≤ Lc * ‖y - x‖ ∧
      ‖c y - c x - (J x).adjoint (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2 := by
  have hcL : ‖c y - c x‖ ≤ Lc * ‖y - x‖ := by
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hc z).hasFDerivWithinAt)
      (fun z _ => by simpa only [ContinuousLinearMap.adjoint.norm_map] using hJn z)
      (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ y)
  have hDL : ∀ x y, ‖(J y).adjoint - (J x).adjoint‖ ≤ LJ * ‖y - x‖ := by
    intro x y
    rw [← map_sub ContinuousLinearMap.adjoint, ContinuousLinearMap.adjoint.norm_map]
    exact hJL x y
  have hr := quadratic_remainder hLJ hc hDL x y
  exact ⟨hcL, hr⟩

lemma field_increment {f : E → ℝ} {c : E → F} {J : E → F →L[ℝ] E} {g : E → E}
    {Lf Lc LJ B K β : ℝ} (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hLJ : 0 ≤ LJ) (hB : 0 ≤ B) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hf : ∀ x, HasGradientAt f (g x) x)
    (hc : ∀ x, HasFDerivAt c (J x).adjoint x)
    (hgL : ∀ x y, ‖g y - g x‖ ≤ Lf * ‖y - x‖)
    (hJn : ∀ x, ‖J x‖ ≤ Lc)
    (hJL : ∀ x y, ‖J y - J x‖ ≤ LJ * ‖y - x‖)
    (x y : E) (hmultNorm : ‖multiplier (J x) (g x)‖ ≤ B)
    (hmultLip : ‖multiplier (J y) (g y) - multiplier (J x) (g x)‖ ≤ K * ‖y - x‖) :
    merit f c J g β y - merit f c J g β x ≤
      ⟪tangent (J x) (g x) + β • J x (c x), y - x⟫ + K * ‖y - x‖ * ‖c x‖ +
      (Lf + B * LJ + K * Lc + β * (‖c x‖ * LJ + Lc ^ 2 / 2)) * ‖y - x‖ ^ 2 := by
  obtain ⟨hcL, hr⟩ := constraint_model hLJ hc hJn hJL x y
  have h := combined_merit_increment hB hK hLc (norm_nonneg (y - x)) hβ
    (objective_upper hLf hf hgL x y) hmultNorm hmultLip hcL hr
  have he : ⟪g x, y - x⟫ + ⟪multiplier (J x) (g x), (J x).adjoint (y - x)⟫ +
      β * ⟪c x, (J x).adjoint (y - x)⟫ =
      ⟪tangent (J x) (g x) + β • J x (c x), y - x⟫ := by
    simp only [ContinuousLinearMap.adjoint_inner_right, tangent, inner_add_left,
      real_inner_smul_left]
  change _ ≤ _ at h
  simpa only [merit, he] using h

lemma field_descent [FiniteDimensional ℝ F]
    {f : E → ℝ} {c : E → F} {J : E → F →L[ℝ] E} {g : E → E}
    {Lf Lc LJ B K β ν M η : ℝ} (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hLJ : 0 ≤ LJ) (hB : 0 ≤ B) (hK : 0 ≤ K) (hν : 0 < ν) (hη : 0 ≤ η)
    (hβ : 8 * ((K / ν) ^ 2 + K / ν + 1) ≤ β)
    (hf : ∀ x, HasGradientAt f (g x) x)
    (hc : ∀ x, HasFDerivAt c (J x).adjoint x)
    (hgL : ∀ x y, ‖g y - g x‖ ≤ Lf * ‖y - x‖)
    (hJn : ∀ x, ‖J x‖ ≤ Lc)
    (hJL : ∀ x y, ‖J y - J x‖ ≤ LJ * ‖y - x‖)
    {x y e : E} (hmultNorm : ‖multiplier (J x) (g x)‖ ≤ B)
    (hmultLip : ‖multiplier (J y) (g y) - multiplier (J x) (g x)‖ ≤ K * ‖y - x‖)
    (hJx : regular ν (J x)) (hM : ‖c x‖ ≤ M)
    (hy : y - x = η • (-tangent (J x) (g x) - J x (c x) + e))
    (hηD : (Lf + B * LJ + K * Lc + β * (M * LJ + Lc ^ 2 / 2)) * η ≤ 1 / 16) :
    merit f c J g β y ≤ merit f c J g β x - η * ‖tangent (J x) (g x)‖ ^ 2 / 2 -
      η * β * ‖J x (c x)‖ ^ 2 / 4 + η * (β + 3) * ‖e‖ ^ 2 := by
  have hk : 0 ≤ K / ν := div_nonneg hK hν.le
  have hβ0 : 0 ≤ β := by nlinarith [sq_nonneg (K / ν)]
  have hi := field_increment hLf hLc hLJ hB hK hβ0 hf hc hgL hJn hJL x y hmultNorm hmultLip
  have hcn : ‖c x‖ ≤ ‖J x (c x)‖ / ν := by
    apply (le_div_iff₀ hν).mpr
    simpa only [mul_comm] using hJx (c x)
  have hcross : K * ‖y - x‖ * ‖c x‖ ≤ (K / ν) * ‖y - x‖ * ‖J x (c x)‖ := by
    have h := mul_le_mul_of_nonneg_left hcn (show 0 ≤ K * ‖y - x‖ by positivity)
    convert h using 1; ring
  have hcurve : (Lf + B * LJ + K * Lc + β * (‖c x‖ * LJ + Lc ^ 2 / 2)) * ‖y - x‖ ^ 2 ≤
      (Lf + B * LJ + K * Lc + β * (M * LJ + Lc ^ 2 / 2)) * ‖y - x‖ ^ 2 := by
    gcongr
  have hstep : merit f c J g β y - merit f c J g β x ≤
      ⟪tangent (J x) (g x) + β • J x (c x), y - x⟫ +
      (K / ν) * ‖y - x‖ * ‖J x (c x)‖ +
      (Lf + B * LJ + K * Lc + β * (M * LJ + Lc ^ 2 / 2)) * ‖y - x‖ ^ 2 := by
    linarith only [hi, hcross, hcurve]
  rw [hy] at hstep
  exact inexact_merit_step
    (LongTails.Proofs.StochasticEqualityGeometry.tangent_orthogonal hν hJx (g x) (c x))
    hk hη hβ hηD hstep

lemma field_lower_bound {f : E → ℝ} {c : E → F} {J : E → F →L[ℝ] E}
    {g : E → E} {β B fLower : ℝ} {x : E} (hβ : 0 < β) (hf : fLower ≤ f x)
    (hmult : ‖multiplier (J x) (g x)‖ ≤ B) :
    fLower + β * ‖c x‖ ^ 2 / 4 - B ^ 2 / β ≤ merit f c J g β x := by
  have hab : |⟪multiplier (J x) (g x), c x⟫| ≤ B * ‖c x‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hmult (norm_nonneg _))
  have hc : -B * ‖c x‖ ≤ ⟪multiplier (J x) (g x), c x⟫ := by
    simpa only [neg_mul] using neg_le_of_abs_le hab
  exact merit_lower_bound hf hβ hc

lemma field_initial_bound {f : E → ℝ} {c : E → F} {J : E → F →L[ℝ] E}
    {g : E → E} {β B fLower Δ C0 : ℝ} {x : E} (hβ : 0 ≤ β)
    (hf : f x - fLower ≤ Δ) (hmult : ‖multiplier (J x) (g x)‖ ≤ B)
    (hc : ‖c x‖ ≤ C0) :
    merit f c J g β x - fLower ≤ Δ + B * C0 + β * C0 ^ 2 / 2 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hmult
  have hC : 0 ≤ C0 := (norm_nonneg _).trans hc
  have hi : ⟪multiplier (J x) (g x), c x⟫ ≤ B * C0 := by
    apply (real_inner_le_norm _ _).trans
    gcongr
  have hs := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hC).mpr hc) hβ
  unfold merit
  linarith only [hf, hi, hs]

lemma field_coercive [FiniteDimensional ℝ F]
    {f : E → ℝ} {c : E → F} {J : E → F →L[ℝ] E} {g : E → E}
    {Lf β ν fLower : ℝ} (hLf : 0 < Lf) (hβ : 0 < β) (hν : 0 < ν)
    (hf : ∀ x, HasGradientAt f (g x) x)
    (hgL : ∀ x y, ‖g y - g x‖ ≤ Lf * ‖y - x‖)
    (hlow : ∀ x, fLower ≤ f x) (hβL : 4 * Lf ≤ β * ν ^ 2)
    (x : E) (hJx : regular ν (J x)) :
    fLower + (f x - fLower) / 2 + β * ‖c x‖ ^ 2 / 4 ≤ merit f c J g β x := by
  have hgeq : gradient f = g := gradient_eq hf
  have hgrad : ∀ x, HasGradientAt f (gradient f x) x := by simpa only [hgeq] using hf
  have hglip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖ := by
    simpa only [hgeq] using fun x y => hgL y x
  have hself := OracleTemplate.HeavyTailedPL.gradient_sq_le hLf hgrad hglip hlow x
  rw [hgeq] at hself
  have hmult := LongTails.Proofs.StochasticEqualityGeometry.norm_multiplier_le hν hJx (g x)
  have huG : ν * ‖multiplier (J x) (g x)‖ ≤ ‖g x‖ := by
    have h := (le_div_iff₀ hν).mp hmult
    simpa only [mul_comm] using h
  have hcross : -‖multiplier (J x) (g x)‖ * ‖c x‖ ≤ ⟪multiplier (J x) (g x), c x⟫ := by
    simpa only [neg_mul] using neg_le_of_abs_le (abs_real_inner_le_norm (multiplier (J x) (g x)) (c x))
  have h := relative_merit_lower (sub_nonneg.mpr (hlow x)) hβ hν
    (norm_nonneg _) (norm_nonneg _) huG hself hβL hcross
  unfold merit
  linarith only [h]

lemma feasibility_descent {c : E → F} {J : E → F →L[ℝ] E} {Lc LJ M ν η : ℝ}
    (hLc : 0 ≤ Lc) (hLJ : 0 ≤ LJ) (hν : 0 < ν) (hη : 0 ≤ η)
    (hc : ∀ x, HasFDerivAt c (J x).adjoint x)
    (hJn : ∀ x, ‖J x‖ ≤ Lc)
    (hJL : ∀ x y, ‖J y - J x‖ ≤ LJ * ‖y - x‖)
    {x y e : E} (hJx : regular ν (J x)) (hM : ‖c x‖ ≤ M)
    (hy : y - x = η • (-J x (c x) + e))
    (hηD : (M * LJ + Lc ^ 2 / 2) * η ≤ 1 / 16) :
    ‖c y‖ ^ 2 ≤ (1 - η * ν ^ 2) * ‖c x‖ ^ 2 + 4 * η * ‖e‖ ^ 2 := by
  obtain ⟨hcL, hr⟩ := constraint_model hLJ hc hJn hJL x y
  have hi := constraint_square_increment hLc (norm_nonneg (y - x)) hcL hr
  rw [ContinuousLinearMap.adjoint_inner_right] at hi
  have hco : (2 * ‖c x‖ * LJ + Lc ^ 2) * ‖y - x‖ ^ 2 ≤
      (2 * M * LJ + Lc ^ 2) * ‖y - x‖ ^ 2 := by gcongr
  have hinc : ‖c y‖ ^ 2 - ‖c x‖ ^ 2 ≤ 2 * ⟪J x (c x), y - x⟫ +
      2 * (M * LJ + Lc ^ 2 / 2) * ‖y - x‖ ^ 2 := by nlinarith only [hi, hco]
  rw [hy] at hinc
  simp only [inner_smul_right, inner_add_right, inner_neg_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, mul_pow] at hinc
  have hn := (orthogonal_direction_norm (a := (0 : E)) (b := J x (c x)) (e := e)
    (by simp)).2
  simp only [neg_zero, zero_sub, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add] at hn
  have hcurv : 2 * (M * LJ + Lc ^ 2 / 2) * η ^ 2 * ‖-J x (c x) + e‖ ^ 2 ≤
      η / 4 * (‖J x (c x)‖ ^ 2 + ‖e‖ ^ 2) := by
    have h₁ := mul_le_mul_of_nonneg_right hηD (sq_nonneg ‖-J x (c x) + e‖)
    have h₂ : (M * LJ + Lc ^ 2 / 2) * η * ‖-J x (c x) + e‖ ^ 2 ≤
        (‖J x (c x)‖ ^ 2 + ‖e‖ ^ 2) / 8 := by nlinarith only [h₁, hn]
    have h₃ := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 2 * η by positivity)
    nlinarith only [h₃]
  have hiYoung : ⟪J x (c x), e⟫ ≤ ‖J x (c x)‖ ^ 2 / 4 + ‖e‖ ^ 2 := by
    have h := real_inner_le_norm (J x (c x)) e
    nlinarith only [h, sq_nonneg (‖J x (c x)‖ - 2 * ‖e‖)]
  have hyYoung := mul_le_mul_of_nonneg_left hiYoung (show 0 ≤ 2 * η by positivity)
  have hrank : (ν * ‖c x‖) ^ 2 ≤ ‖J x (c x)‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (hJx (c x))
  have hrank' := mul_le_mul_of_nonneg_left hrank hη
  have he0 := mul_nonneg hη (sq_nonneg ‖e‖)
  have hb0 := mul_nonneg hη (sq_nonneg ‖J x (c x)‖)
  nlinarith only [hinc, hcurv, hyYoung, hrank', he0, hb0]

end LongTails.Proofs.StochasticEqualityDescent
