import LongTails.Proofs.LinearDecaySgdStep
import LongTails.Setups.InterpolatedFiniteSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open Set InnerProductSpace Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.CyclicInterpolation

open LongTails.Setups.InterpolatedFiniteSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_telescope (a b c : E) :
    2 * ⟪a - b, b - c⟫ = ‖a - c‖ ^ 2 - ‖b - c‖ ^ 2 - ‖a - b‖ ^ 2 := by
  have h : a - c = (a - b) + (b - c) := by abel
  rw [h, norm_add_sq_real]
  ring

lemma sum_inner_telescope (p : ℕ → E) (c : E) (J : ℕ) :
    ∑ j ∈ range J, 2 * ⟪p j - p (j + 1), p (j + 1) - c⟫ =
      ‖p 0 - c‖ ^ 2 - ‖p J - c‖ ^ 2 - ∑ j ∈ range J, ‖p j - p (j + 1)‖ ^ 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, sum_range_succ, ih, inner_telescope]
    ring

omit [InnerProductSpace ℝ E] in
lemma path_sq (p : ℕ → E) {a b m : ℕ} (hab : a ≤ b) (hb : b ≤ m) :
    ‖p a - p b‖ ^ 2 ≤ (b - a : ℕ) * ∑ l ∈ range m, ‖p l - p (l + 1)‖ ^ 2 := by
  have h1 : ‖p a - p b‖ ≤ ∑ l ∈ Finset.Ico a b, ‖p l - p (l + 1)‖ := by
    simpa [dist_eq_norm] using dist_le_Ico_sum_dist p hab
  have h2 : (∑ l ∈ Finset.Ico a b, ‖p l - p (l + 1)‖) ^ 2 ≤
      (Finset.Ico a b).card * ∑ l ∈ Finset.Ico a b, ‖p l - p (l + 1)‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ l ∈ Finset.Ico a b, ‖p l - p (l + 1)‖ ^ 2 ≤
      ∑ l ∈ range m, ‖p l - p (l + 1)‖ ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro l hl
      rw [Finset.mem_Ico] at hl
      exact mem_range.mpr (lt_of_lt_of_le hl.2 hb)
    · intro l _ _
      positivity
  have h4 : ‖p a - p b‖ ^ 2 ≤ (∑ l ∈ Finset.Ico a b, ‖p l - p (l + 1)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [Nat.card_Ico] at h2
  have h5 : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ‖p a - p b‖ ^ 2 ≤ (b - a : ℕ) * ∑ l ∈ Finset.Ico a b, ‖p l - p (l + 1)‖ ^ 2 := h4.trans h2
    _ ≤ (b - a : ℕ) * ∑ l ∈ range m, ‖p l - p (l + 1)‖ ^ 2 := mul_le_mul_of_nonneg_left h3 h5

lemma cycle_identity (p q : ℕ → E) (m : ℕ) (hq : q 0 = p m) :
    2 * ∑ j ∈ range m, ⟪q j - q (j + 1), p (j + 1) - q (j + 1)⟫ +
      2 * ∑ j ∈ range m, ⟪(p j - p (j + 1)) - (q j - q (j + 1)), p (j + 1) - p m⟫ =
    ∑ j ∈ range m, ‖q j - q (j + 1)‖ ^ 2 - ∑ j ∈ range m, ‖p j - p (j + 1)‖ ^ 2 +
      ‖p 0 - p m‖ ^ 2 + ‖q 0 - q m‖ ^ 2 := by
  have h1 := sum_inner_telescope p (p m) m
  have h2 := sum_inner_telescope q (q 0) m
  have h3 : ∀ j, ⟪q j - q (j + 1), p (j + 1) - q (j + 1)⟫ +
      ⟪(p j - p (j + 1)) - (q j - q (j + 1)), p (j + 1) - p m⟫ =
      ⟪p j - p (j + 1), p (j + 1) - p m⟫ - ⟪q j - q (j + 1), q (j + 1) - q 0⟫ := by
    intro j
    rw [hq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have h4 : 2 * ∑ j ∈ range m, ⟪q j - q (j + 1), p (j + 1) - q (j + 1)⟫ +
      2 * ∑ j ∈ range m, ⟪(p j - p (j + 1)) - (q j - q (j + 1)), p (j + 1) - p m⟫ =
      ∑ j ∈ range m, 2 * ⟪p j - p (j + 1), p (j + 1) - p m⟫ -
        ∑ j ∈ range m, 2 * ⟪q j - q (j + 1), q (j + 1) - q 0⟫ := by
    rw [← mul_add, ← sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sub, ← sum_sub_distrib]
    congr 1
    exact sum_congr rfl (fun j _ => h3 j)
  rw [h4, h1, h2]
  simp only [sub_self, norm_zero]
  rw [norm_sub_rev (q m) (q 0)]
  ring

variable [CompleteSpace E]

section OneComponent

variable {φ : E → ℝ} {g : E → E} {L : ℝ}

lemma gradient_min_zero (hL : 0 < L) (hg : ∀ x, HasGradientAt φ (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {xstar : E} (hmin : IsMinOn φ univ xstar) :
    g xstar = 0 := by
  have hd := Gradient.descent hL hg hlip xstar
  have hm := hmin (mem_univ (xstar - (1 / L) • g xstar))
  have hm' : φ xstar ≤ φ (xstar - (1 / L) • g xstar) := hm
  have h0 : ‖g xstar‖ ^ 2 / (2 * L) ≤ 0 := by linarith
  have h1 : ‖g xstar‖ ^ 2 ≤ 0 := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp h0
    simpa using this
  have h2 : ‖g xstar‖ = 0 := by nlinarith [norm_nonneg (g xstar)]
  exact norm_eq_zero.mp h2

lemma grad_sq_le (hL : 0 < L) (hc : ConvexOn ℝ univ φ) (hg : ∀ x, HasGradientAt φ (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {xstar : E} (hmin : IsMinOn φ univ xstar) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * L * (φ x - φ xstar) := by
  have h := SampledConvex.cocoercive hL hc hg hlip x xstar
  rw [gradient_min_zero hL hg hlip hmin] at h
  simpa using h

lemma step_fejer (hL : 0 < L) (hc : ConvexOn ℝ univ φ) (hg : ∀ x, HasGradientAt φ (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {xstar : E} (hmin : IsMinOn φ univ xstar) (x : E) :
    ‖x - (1 / L) • g x - xstar‖ ^ 2 ≤ ‖x - xstar‖ ^ 2 - 2 / L * (φ x - φ xstar) := by
  have h := SampledConvex.cocoercive hL hc hg hlip xstar x
  rw [gradient_min_zero hL hg hlip hmin] at h
  have h1 : ‖g x‖ ^ 2 ≤ 2 * L * (φ xstar - φ x - ⟪g x, xstar - x⟫) := by
    simpa [norm_sub_rev] using h
  have h2 : x - (1 / L) • g x - xstar = (x - xstar) - (1 / L) • g x := by abel
  have h3 : ⟪g x, xstar - x⟫ = -⟪x - xstar, g x⟫ := by
    rw [← neg_sub x xstar, inner_neg_right, real_inner_comm]
  rw [h2, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / L)]
  rw [h3] at h1
  have h4 : 2 / L * (φ x - φ xstar) + (1 / L * ‖g x‖) ^ 2 ≤ 2 * (1 / L * ⟪x - xstar, g x⟫) := by
    have h5 : ‖g x‖ ^ 2 / (2 * L) ≤ φ xstar - φ x + ⟪x - xstar, g x⟫ := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * L)]
      linarith
    have h6 : (1 / L * ‖g x‖) ^ 2 = 2 / L * (‖g x‖ ^ 2 / (2 * L)) := by
      field_simp
    have h7 : 2 * (1 / L * ⟪x - xstar, g x⟫) = 2 / L * ⟪x - xstar, g x⟫ := by ring
    rw [h6, h7, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

lemma step_firm (hL : 0 < L) (hc : ConvexOn ℝ univ φ) (hg : ∀ x, HasGradientAt φ (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖(x - (1 / L) • g x) - (y - (1 / L) • g y)‖ ^ 2 ≤
      ‖x - y‖ ^ 2 - ‖(1 / L) • g x - (1 / L) • g y‖ ^ 2 := by
  have h1 := SampledConvex.cocoercive hL hc hg hlip x y
  have h2 := SampledConvex.cocoercive hL hc hg hlip y x
  have h3 : ‖g y - g x‖ = ‖g x - g y‖ := norm_sub_rev _ _
  have h4 : ⟪g x, y - x⟫ = -⟪g x, x - y⟫ := by
    rw [← neg_sub x y, inner_neg_right]
  rw [h3, h4] at h2
  have h5 : ‖g x - g y‖ ^ 2 ≤ L * ⟪g x - g y, x - y⟫ := by
    rw [inner_sub_left]
    linarith
  have h6 : (x - (1 / L) • g x) - (y - (1 / L) • g y) = (x - y) - (1 / L) • (g x - g y) := by
    rw [smul_sub]
    abel
  have h7 : (1 / L) • g x - (1 / L) • g y = (1 / L) • (g x - g y) := (smul_sub _ _ _).symm
  rw [h6, h7, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / L), real_inner_comm]
  have h8 : (1 / L * ‖g x - g y‖) ^ 2 ≤ 1 / L * ⟪g x - g y, x - y⟫ := by
    have : (1 / L * ‖g x - g y‖) ^ 2 = 1 / L * (‖g x - g y‖ ^ 2 / L) := by
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ hL]
    linarith
  linarith

lemma step_gamma (hL : 0 < L) (hc : ConvexOn ℝ univ φ) (hg : ∀ x, HasGradientAt φ (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ⟪(1 / L) • g y, (x - (1 / L) • g x) - (y - (1 / L) • g y)⟫ ≤
      1 / L * (φ x - φ y) + (‖(1 / L) • g y‖ ^ 2 - ‖(1 / L) • g x‖ ^ 2) / 2 := by
  have h1 := SampledConvex.cocoercive hL hc hg hlip x y
  have h2 : (x - (1 / L) • g x) - (y - (1 / L) • g y) =
      (x - y) - ((1 / L) • g x - (1 / L) • g y) := by abel
  have h3 : ⟪(1 / L) • g y, (1 / L) • g x - (1 / L) • g y⟫ =
      (‖(1 / L) • g x‖ ^ 2 - ‖(1 / L) • g y‖ ^ 2 - ‖(1 / L) • g x - (1 / L) • g y‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
    ring
  have h4 : ‖(1 / L) • g x - (1 / L) • g y‖ ^ 2 = 1 / L * (‖g x - g y‖ ^ 2 / L) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / L)]
    field_simp
  have h5 : ‖g x - g y‖ ^ 2 / L ≤ 2 * (φ x - φ y - ⟪g y, x - y⟫) := by
    rw [div_le_iff₀ hL]
    linarith
  have h6 : 1 / L * (‖g x - g y‖ ^ 2 / L) ≤ 1 / L * (2 * (φ x - φ y - ⟪g y, x - y⟫)) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  rw [h2, inner_sub_right, h3, inner_smul_left, h4]
  simp only [RCLike.conj_to_real]
  linarith

end OneComponent

end OracleTemplate.CyclicInterpolation
