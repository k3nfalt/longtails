import LongTails.Proofs.CenteredLogisticGeometry
import LongTails.Proofs.CenteredLogisticExpansion

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticReadout

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open CenteredLogisticGeometry CenteredLogisticExpansion

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def first : Features p.d := (4 : ℝ) • signal G

noncomputable def score (i : Fin p.n) : ℝ := ⟪row G i, first G⟫

noncomputable def force : Features p.d :=
  𝔼 i, Real.sigmoid (-score G i) • row G i

noncomputable def second : Features p.d := first G + (8 : ℝ) • force G

lemma first_norm : ‖first G‖ ≤ 4 * G.ε := by
  rw [first, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact mul_le_mul_of_nonneg_left (signal_norm G) (by norm_num : (0 : ℝ) ≤ 4)

lemma score_abs (i : Fin p.n) : |score G i| ≤ (33 / 8) * G.ε := by
  calc |score G i| ≤ ‖row G i‖ * ‖first G‖ := abs_real_inner_le_norm _ _
       _ ≤ 33 / 32 * (4 * G.ε) := mul_le_mul (row_norm G i) (first_norm G) (norm_nonneg _) (by norm_num)
       _ = _ := by ring

noncomputable def remainder : Features p.d :=
  𝔼 i, (Real.sigmoid (-score G i) - 1 / 2 + score G i / 4) • row G i

lemma remainder_norm : ‖remainder G‖ ≤ 5 * G.ε ^ 3 := by
  apply mean_norm_le
  intro i
  rw [norm_smul, Real.norm_eq_abs]
  have h := sigmoid_cubic (-score G i)
  rw [abs_neg, neg_div, sub_neg_eq_add] at h
  have hcube := pow_le_pow_left₀ (abs_nonneg _) (score_abs G i) 3
  calc _ ≤ (|score G i| ^ 3 / 16) * (33 / 32) := mul_le_mul h (row_norm G i) (norm_nonneg _) (by positivity)
       _ ≤ _ := by nlinarith [pow_pos G.radius_pos 3]

lemma second_expansion : second G = (8 : ℝ) • signal G -
    (8 : ℝ) • (𝔼 i, ⟪row G i, signal G⟫ • row G i) + (8 : ℝ) • remainder G := by
  have hforce : force G = (1 / 2 : ℝ) • signal G -
      (𝔼 i, ⟪row G i, signal G⟫ • row G i) + remainder G := by
    rw [← mean_row G, Finset.smul_expect]
    rw [mean_row G, ← Finset.expect_sub_distrib, remainder, ← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro i _
    simp only [score, first, real_inner_smul_right]
    module
  rw [second, hforce, first]
  module

lemma approximation : ‖second G - (8 : ℝ) • tangent G‖ ≤ 56 * G.ε ^ 3 := by
  let cov := 𝔼 i, ⟪G.h i, signal G⟫ • G.h i
  have hc : ‖cov‖ ≤ G.ε ^ 3 := by
    apply mean_norm_le
    intro i
    rw [norm_smul, Real.norm_eq_abs]
    calc _ ≤ (‖G.h i‖ * ‖signal G‖) * ‖G.h i‖ := mul_le_mul_of_nonneg_right
           (abs_real_inner_le_norm _ _) (norm_nonneg _)
         _ ≤ (G.ε * G.ε) * G.ε := mul_le_mul
           (mul_le_mul (G.radius i) (signal_norm G) (norm_nonneg _) G.radius_pos.le)
           (G.radius i) (norm_nonneg _) (mul_self_nonneg _)
         _ = _ := by ring
  let a := (1 - G.level ^ 2) * ⟪G.axis, signal G⟫
  have ha : ‖a • G.axis‖ ≤ G.ε ^ 3 := by
    have hv : 1 - G.level ^ 2 = 𝔼 i, ‖G.h i‖ ^ 2 := by linarith [G.normalized]
    simp only [a, norm_smul, Real.norm_eq_abs, G.axis_unit, mul_one, abs_mul, hv,
      abs_of_nonneg (variance_nonneg G)]
    have hi := abs_real_inner_le_norm G.axis (signal G)
    rw [G.axis_unit, one_mul] at hi
    calc _ ≤ G.ε ^ 2 * G.ε := mul_le_mul (variance_le G) (hi.trans (signal_norm G))
           (abs_nonneg _) (sq_nonneg _)
         _ = _ := by ring
  have he : second G - (8 : ℝ) • tangent G =
      (8 : ℝ) • ((a • G.axis - cov) + remainder G) := by
    rw [second_expansion, covariance_split]
    unfold tangent
    dsimp only [a, cov]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  linarith [norm_add_le (a • G.axis - cov) (remainder G), norm_sub_le (a • G.axis) cov,
    remainder_norm G]

lemma force_norm : ‖force G‖ ≤ (17 / 32) * G.ε := by
  have he : (8 : ℝ) • force G = second G - (8 : ℝ) • tangent G +
      (4 : ℝ) • ((2 : ℝ) • tangent G - signal G) := by unfold second first; module
  have h := norm_add_le (second G - (8 : ℝ) • tangent G)
    ((4 : ℝ) • ((2 : ℝ) • tangent G - signal G))
  rw [← he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, reflected_norm] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 8), abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h
  have hs := mul_self_le_mul_self G.radius_pos.le G.radius_le
  nlinarith only [h, mul_le_mul_of_nonneg_right hs G.radius_pos.le, approximation G, signal_norm G,
    G.radius_pos]

end LongTails.Proofs.CenteredLogisticReadout
