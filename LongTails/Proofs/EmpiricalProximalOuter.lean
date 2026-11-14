import LongTails.Proofs.ProximalStormOuter

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.EmpiricalProximalOuter

open OracleTemplate
open OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma model_energy_step {φ : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ φ) (hg : ∀ x, HasGradientAt φ (g x) x)
    {lam A : ℝ} (hl : 0 < lam) (hA : 0 ≤ A) (x z w u : E) :
    (A + aNext lam A) * (φ w - φ u) +
      ‖z - aNext lam A • g w - u‖ ^ 2 / 2 ≤
    A * (φ x - φ u) + ‖z - u‖ ^ 2 / 2 -
      lam * (A + aNext lam A) / 2 * ‖g w‖ ^ 2 +
      (A + aNext lam A) * ⟪g w, lam • g w + w - mixPt lam A x z⟫ := by
  set a := aNext lam A
  set B := A + a
  set v := mixPt lam A x z
  have ha : 0 < a := aNext_pos hl hA
  have hB : 0 < B := by dsimp [B]; linarith
  have hsq : a ^ 2 = lam * B := aNext_sq hl hA
  have hmix : B • v = A • x + a • z := by
    have he1 : B * (A / B) = A := by field_simp
    have he2 : B * (a / B) = a := by field_simp
    change B • ((A / B) • x + (a / B) • z) = _
    rw [smul_add, smul_smul, smul_smul, he1, he2]
  have hnorm : ‖z - a • g w - u‖ ^ 2 =
      ‖z - u‖ ^ 2 - 2 * a * ⟪g w, z - u⟫ + a ^ 2 * ‖g w‖ ^ 2 := by
    rw [show z - a • g w - u = (z - u) - a • g w by abel,
      norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_comm]
    ring
  have hinner : A * ⟪g w, x - w⟫ + a * ⟪g w, u - w⟫ +
      a * ⟪g w, z - u⟫ = B * ⟪g w, v - w⟫ := by
    have he : B * ⟪g w, v - w⟫ = ⟪g w, B • v⟫ - B * ⟪g w, w⟫ := by
      rw [inner_sub_right, real_inner_smul_right]
      ring
    rw [he, hmix]
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, B]
    ring
  have hr : ⟪g w, lam • g w + w - v⟫ =
      lam * ‖g w‖ ^ 2 - ⟪g w, v - w⟫ := by
    rw [inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, inner_sub_right]
    ring
  have hx := mul_le_mul_of_nonneg_left (Gradient.convex_support hc hg w x) hA
  have hu := mul_le_mul_of_nonneg_left (Gradient.convex_support hc hg w u) ha.le
  change B * (φ w - φ u) + ‖z - a • g w - u‖ ^ 2 / 2 ≤
    A * (φ x - φ u) + ‖z - u‖ ^ 2 / 2 - lam * B / 2 * ‖g w‖ ^ 2 +
      B * ⟪g w, lam • g w + w - v⟫
  rw [hnorm, hr, hsq]
  dsimp only [B] at *
  nlinarith

lemma empirical_energy_step {φ : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ φ) (hg : ∀ x, HasGradientAt φ (g x) x)
    (f : E → ℝ) {lam A : ℝ} (hl : 0 < lam) (hA : 0 ≤ A) (x z w u : E) :
    (A + aNext lam A) * (f w - f u) +
      ‖z - aNext lam A • g w - u‖ ^ 2 / 2 ≤
    A * (f x - f u) + ‖z - u‖ ^ 2 / 2 -
      lam * (A + aNext lam A) / 2 * ‖g w‖ ^ 2 +
      (A + aNext lam A) * ⟪g w, lam • g w + w - mixPt lam A x z⟫ +
      (A + aNext lam A) * (f w - φ w) - A * (f x - φ x) -
      aNext lam A * (f u - φ u) := by
  have he := model_energy_step hc hg hl hA x z w u
  nlinarith

omit [CompleteSpace E] in
lemma residual_inner_bound {lam : ℝ} (hl : 0 < lam) (h r : E) :
    ⟪h, r⟫ ≤ lam / 8 * ‖h‖ ^ 2 + 2 / lam * ‖r‖ ^ 2 := by
  have hi := real_inner_le_norm h r
  have hs := sq_nonneg (lam * ‖h‖ - 4 * ‖r‖)
  have hd : lam * (2 / lam) = 2 := by field_simp
  have hm := mul_le_mul_of_nonneg_left hi hl.le
  nlinarith

omit [CompleteSpace E] in
lemma expected_residual_inner {Ω : Type*} [Fintype Ω]
    {lam : ℝ} (hl : 0 < lam) (h r : Ω → E)
    (hr : (𝔼 ξ, ‖r ξ‖ ^ 2) ≤ lam ^ 2 / 16 * (𝔼 ξ, ‖h ξ‖ ^ 2)) :
    (𝔼 ξ, ⟪h ξ, r ξ⟫) ≤ lam / 4 * (𝔼 ξ, ‖h ξ‖ ^ 2) := by
  have he := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ => residual_inner_bound hl (h ξ) (r ξ))
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at he
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 / lam by positivity)
  have hid : 2 / lam * (lam ^ 2 / 16) = lam / 8 := by field_simp; ring
  rw [← mul_assoc, hid] at hm
  linarith

lemma expected_energy_step {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {φ : Ω → E → ℝ} {g : Ω → E → E}
    (hc : ∀ ξ, ConvexOn ℝ univ (φ ξ))
    (hg : ∀ ξ x, HasGradientAt (φ ξ) (g ξ x) x)
    (f : E → ℝ) {lam A : ℝ} (hl : 0 < lam) (hA : 0 ≤ A)
    (x z u : E) (w : Ω → E) (hmean : ∀ v, (𝔼 ξ, φ ξ v) = f v)
    (hgen : (𝔼 ξ, (f (w ξ) - φ ξ (w ξ))) ≤ lam / 4 * (𝔼 ξ, ‖g ξ (w ξ)‖ ^ 2))
    (hr : (𝔼 ξ, ‖lam • g ξ (w ξ) + w ξ - mixPt lam A x z‖ ^ 2) ≤
      lam ^ 2 / 16 * (𝔼 ξ, ‖g ξ (w ξ)‖ ^ 2)) :
    (𝔼 ξ, ((A + aNext lam A) * (f (w ξ) - f u) +
      ‖z - aNext lam A • g ξ (w ξ) - u‖ ^ 2 / 2)) ≤
        A * (f x - f u) + ‖z - u‖ ^ 2 / 2 := by
  have he := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
    empirical_energy_step (hc ξ) (hg ξ) f hl hA x z (w ξ) u)
  have hcross := expected_residual_inner hl (fun ξ => g ξ (w ξ))
    (fun ξ => lam • g ξ (w ξ) + w ξ - mixPt lam A x z) hr
  have hB : 0 ≤ A + aNext lam A := add_nonneg hA (aNext_pos hl hA).le
  have h₁ := mul_le_mul_of_nonneg_left hgen hB
  have h₂ := mul_le_mul_of_nonneg_left hcross hB
  have heq : (𝔼 ξ, ((A * (f x - f u) + ‖z - u‖ ^ 2 / 2 -
      lam * (A + aNext lam A) / 2 * ‖g ξ (w ξ)‖ ^ 2 +
      (A + aNext lam A) * ⟪g ξ (w ξ), lam • g ξ (w ξ) + w ξ - mixPt lam A x z⟫ +
      (A + aNext lam A) * (f (w ξ) - φ ξ (w ξ)) - A * (f x - φ ξ x) -
      aNext lam A * (f u - φ ξ u)))) =
      A * (f x - f u) + ‖z - u‖ ^ 2 / 2 -
        lam * (A + aNext lam A) / 2 * (𝔼 ξ, ‖g ξ (w ξ)‖ ^ 2) +
        (A + aNext lam A) * (𝔼 ξ, ⟪g ξ (w ξ), lam • g ξ (w ξ) + w ξ - mixPt lam A x z⟫) +
        (A + aNext lam A) * (𝔼 ξ, (f (w ξ) - φ ξ (w ξ))) := by
    simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
      Fintype.expect_const, hmean, sub_self, mul_zero, sub_zero]
  rw [heq] at he
  nlinarith only [he, h₁, h₂]

end LongTails.Proofs.EmpiricalProximalOuter
