import LongTails.Proofs.ManyConstraintPenalty
import LongTails.Proofs.SvrgConvex

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintFinite

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ} [NeZero m]

noncomputable def hpen (β : ℝ) (P : Fin m → E → E) (x : E) : ℝ := 𝔼 j, pen β (P j) x

noncomputable def hgrad (β : ℝ) (P : Fin m → E → E) (x : E) : E :=
  (m : ℝ)⁻¹ • ∑ j, penGrad β (P j) x

noncomputable def hest (β : ℝ) (P : Fin m → E → E) (s x : E) (j : Fin m) : E :=
  penGrad β (P j) x - penGrad β (P j) s + hgrad β P s

variable {K : Fin m → Set E} {P : Fin m → E → E}

omit [NeZero m] in
lemma hgrad_inner (β : ℝ) (x d : E) :
    ⟪hgrad β P x, d⟫ = 𝔼 j, ⟪penGrad β (P j) x, d⟫ := by
  rw [OracleTemplate.FiniteSum.expect_inner_left]; rfl

omit [NeZero m] in
lemma hpen_support (hP : ∀ j z, IsProj (K j) z (P j z)) {β : ℝ} (hβ : 0 ≤ β) (x y : E) :
    hpen β P x + ⟪hgrad β P x, y - x⟫ ≤ hpen β P y := by
  rw [hgrad_inner]
  unfold hpen
  rw [← Finset.expect_add_distrib]
  exact Finset.expect_le_expect fun j _ => pen_support (hP j) hβ x y

lemma hpen_upper (hP : ∀ j z, IsProj (K j) z (P j z)) {β : ℝ} (hβ : 0 ≤ β) (x y : E) :
    hpen β P y ≤ hpen β P x + ⟪hgrad β P x, y - x⟫ + β / 2 * ‖y - x‖ ^ 2 := by
  rw [hgrad_inner]
  unfold hpen
  have h := Finset.expect_le_expect (s := Finset.univ) fun j _ => pen_upper (hP j) hβ x y
  simpa only [Finset.expect_add_distrib, Fintype.expect_const] using h

omit [InnerProductSpace ℝ E] [NeZero m] in
lemma hpen_nonneg {β : ℝ} (hβ : 0 ≤ β) (x : E) : 0 ≤ hpen β P x :=
  Finset.expect_nonneg fun _ _ => pen_nonneg hβ x

lemma hest_unbiased (β : ℝ) (s x : E) :
    (m : ℝ)⁻¹ • ∑ j, hest β P s x j = hgrad β P x := by
  have hn : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [hest, hgrad, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_add, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [mul_inv_cancel₀ hn, mul_one]
  module

lemma hest_variance (hP : ∀ j z, IsProj (K j) z (P j z)) {β : ℝ} (hβ : 0 < β) (s x : E) :
    (𝔼 j, ‖hest β P s x j - hgrad β P x‖ ^ 2) ≤
      2 * β * (hpen β P s - hpen β P x - ⟪hgrad β P x, s - x⟫) := by
  let v := fun j => penGrad β (P j) s - penGrad β (P j) x
  have hv : ∀ j, hest β P s x j - hgrad β P x = -(v j - (m : ℝ)⁻¹ • ∑ i, v i) := by
    intro j
    simp only [v, hest, hgrad, Finset.sum_sub_distrib, smul_sub]
    abel
  simp only [hv, norm_neg]
  apply (OracleTemplate.FiniteSum.centered_second_moment v).trans
  have h := Finset.expect_le_expect (s := Finset.univ) fun j _ =>
    pen_cocoercive (hP j) hβ x s
  rw [hgrad_inner]
  unfold hpen
  simp only [v, ← Finset.mul_expect, Finset.expect_sub_distrib] at h ⊢
  exact h

end LongTails.Proofs.ManyConstraintFinite
