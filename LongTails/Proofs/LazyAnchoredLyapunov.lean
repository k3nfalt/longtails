import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LazyAnchoredLyapunov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def potential (x0 : E) (A : ℝ) (z g : E) : ℝ :=
  A * ⟪g, z - x0⟫ + A ^ 2 / 2 * ‖g‖ ^ 2

lemma potential_identity (a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (u gk g1 r : E) :
    (A + a) * ⟪g1, (A / (A + a)) • u - a • g1 + r⟫ + (A + a) ^ 2 / 2 * ‖g1‖ ^ 2 -
        (A * ⟪gk, u⟫ + A ^ 2 / 2 * ‖gk‖ ^ 2) =
      (A + a) ^ 2 / (2 * a ^ 2) *
          (‖r‖ ^ 2 - ‖-(a • g1) + r + (a * A / (A + a)) • gk‖ ^ 2) -
        A * (A + a) / a * ⟪g1 - gk, -((a / (A + a)) • u) - a • g1 + r⟫ := by
  have hA1 : A + a ≠ 0 := by positivity
  have ha0 : a ≠ 0 := ha.ne'
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
    inner_neg_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm gk g1, real_inner_comm u g1, real_inner_comm r g1, real_inner_comm u gk,
    real_inner_comm r gk]
  field_simp
  ring

lemma descent (x0 z z1 g g1 r : E) (a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A)
    (hz1 : z1 - x0 = (A / (A + a)) • (z - x0) - a • g1 + r)
    (hmono : 0 ≤ ⟪g1 - g, z1 - z⟫) :
    potential x0 (A + a) z1 g1 ≤ potential x0 A z g +
      (A + a) ^ 2 / (2 * a ^ 2) *
        (‖r‖ ^ 2 - ‖z1 - (((a / (A + a)) • x0 + (A / (A + a)) • z) -
          (a * A / (A + a)) • g)‖ ^ 2) := by
  have hA1 : A + a ≠ 0 := by positivity
  have hβ : a / (A + a) = 1 - A / (A + a) := by field_simp; ring
  have hγ : a * A / (A + a) = a * (A / (A + a)) := by ring
  have hz : z1 = x0 + ((A / (A + a)) • (z - x0) - a • g1 + r) := by rw [← hz1]; abel
  have hd : z1 - (((a / (A + a)) • x0 + (A / (A + a)) • z) - (a * A / (A + a)) • g) =
      -(a • g1) + r + (a * A / (A + a)) • g := by
    rw [hβ, hγ, hz]
    module
  have hz1z : z1 - z = -((a / (A + a)) • (z - x0)) - a • g1 + r := by
    rw [hβ, hz]
    module
  have key := potential_identity a A ha hA (z - x0) g g1 r
  rw [← hz1z] at key
  have hc : 0 ≤ A * (A + a) / a := by positivity
  unfold potential
  rw [hd, hz1]
  linarith [mul_nonneg hc hmono]

lemma potential_lower (x0 xs z : E) (g : E) (A D : ℝ) (hA : 0 ≤ A)
    (hD : ‖x0 - xs‖ ≤ D) (hg : 0 ≤ ⟪g, z - xs⟫) :
    -(D ^ 2 / 2) ≤ potential x0 A z g := by
  unfold potential
  have h1 : ⟪g, z - x0⟫ = ⟪g, z - xs⟫ + ⟪g, xs - x0⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have h2 : ⟪g, xs - x0⟫ ≥ -(‖g‖ * D) := by
    have := real_inner_le_norm g (x0 - xs)
    have h3 : ⟪g, xs - x0⟫ = -⟪g, x0 - xs⟫ := by
      rw [← inner_neg_right]; congr 1; abel
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left hD (norm_nonneg g)]
  rw [h1]
  nlinarith [sq_nonneg (A * ‖g‖ - D), mul_nonneg hA hg, mul_nonneg hA (norm_nonneg g)]

lemma residual_bound (x0 xs z g : E) (A D : ℝ) (hA : 0 < A) (hD : ‖x0 - xs‖ ≤ D)
    (hg : 0 ≤ ⟪g, z - xs⟫) (hV : potential x0 A z g ≤ 0) : ‖g‖ ≤ 2 * D / A := by
  unfold potential at hV
  have h1 : ⟪g, z - x0⟫ = ⟪g, z - xs⟫ + ⟪g, xs - x0⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have h2 : ⟪g, xs - x0⟫ ≥ -(‖g‖ * D) := by
    have := real_inner_le_norm g (x0 - xs)
    have h3 : ⟪g, xs - x0⟫ = -⟪g, x0 - xs⟫ := by
      rw [← inner_neg_right]; congr 1; abel
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left hD (norm_nonneg g)]
  rw [h1] at hV
  have h4 : A ^ 2 / 2 * ‖g‖ ^ 2 ≤ A * ‖g‖ * D := by nlinarith [mul_nonneg hA.le hg]
  rw [le_div_iff₀ hA]
  rcases eq_or_lt_of_le (norm_nonneg g) with h | h
  · rw [← h]; have : 0 ≤ D := le_trans (norm_nonneg _) hD; linarith
  · have hAg : 0 < A * ‖g‖ := mul_pos hA h
    have h5 : A * ‖g‖ * (‖g‖ * A) ≤ A * ‖g‖ * (2 * D) := by nlinarith
    exact le_of_mul_le_mul_left h5 hAg

end LongTails.Proofs.LazyAnchoredLyapunov
