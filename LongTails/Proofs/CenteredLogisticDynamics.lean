import LongTails.Proofs.CenteredLogisticReadout
import LongTails.Proofs.FiniteScaleConvolutionalSgdGeometry

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticDynamics

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin direction)
open CenteredLogisticGeometry CenteredLogisticReadout TwoSampleQuadraticPerceptronEmbedding

noncomputable def shiftLinear {d : ℕ} : Features d →ₗ[ℝ] Features d where
  toFun := shift
  map_add' := shift_add
  map_smul' := shift_smul

lemma mean_shift {ι : Type*} [Fintype ι] {d : ℕ} (f : ι → Features d) :
    (𝔼 i, shift (f i)) = shift (𝔼 i, f i) :=
  (map_expect (shiftLinear.restrictScalars ℚ≥0) f Finset.univ).symm

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def finalPoint : Space p.d :=
  ((1 + 8 * ⟪force G, first G⟫, 8 * ⟪shift (force G), first G⟫), second G)

lemma shifted_tangent (i : Fin p.n) :
    |⟪shift (row G i), tangent G⟫| ≤ (‖shift G.axis - G.axis‖ + G.ε) * G.ε := by
  have ha : ⟪shift G.axis,tangent G⟫ = ⟪shift G.axis - G.axis,tangent G⟫ := by
    rw [inner_sub_left, axis_tangent, sub_zero]
  have h1 := abs_real_inner_le_norm (shift G.axis - G.axis) (tangent G)
  have h2 := abs_real_inner_le_norm (shift (G.h i)) (tangent G)
  rw [norm_shift] at h2
  rw [row, shift_smul, shift_add, shift_smul, real_inner_smul_left, abs_mul, G.labels, one_mul,
    inner_add_left, real_inner_smul_left, ha]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hlev := mul_le_mul (abs_level G) h1 (abs_nonneg _) zero_le_one
  have hx := mul_le_mul_of_nonneg_left (tangent_norm G) (norm_nonneg (shift G.axis - G.axis))
  have hu := mul_le_mul (G.radius i) (tangent_norm G) (norm_nonneg _) G.radius_pos.le
  nlinarith

lemma score_approximation (i : Fin p.n) :
    |margin .conv p.d (row G i) (finalPoint G) - 8 * ⟪row G i, tangent G⟫| ≤
      (72 + 136 * ‖shift G.axis - G.axis‖) * G.ε ^ 3 := by
  let b := row G i
  let w := second G
  let v := first G
  let f := force G
  let κ := ‖shift G.axis - G.axis‖
  have hb : ‖b‖ ≤ 33 / 32 := row_norm G i
  have hs : ‖shift b‖ ≤ 33 / 32 := by rwa [norm_shift]
  have hf : ‖f‖ ≤ 17 / 32 * G.ε := force_norm G
  have hsf : ‖shift f‖ ≤ 17 / 32 * G.ε := by rwa [norm_shift]
  have hcoef (a : Features p.d) (ha : ‖a‖ ≤ 17 / 32 * G.ε) :
      |8 * ⟪a,v⟫| ≤ 17 * G.ε ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    have h := mul_le_mul ha (first_norm G) (norm_nonneg _) (by linarith [G.radius_pos] :
      0 ≤ 17 / 32 * G.ε)
    change ‖a‖ * ‖v‖ ≤ _ at h
    nlinarith [abs_real_inner_le_norm a v]
  have herr (a : Features p.d) (ha : ‖a‖ ≤ 33 / 32) :
      |⟪a,w⟫ - 8 * ⟪a,tangent G⟫| ≤ 58 * G.ε ^ 3 := by
    rw [← real_inner_smul_right, ← inner_sub_right]
    have h := abs_real_inner_le_norm a (w - (8 : ℝ) • tangent G)
    have h' := mul_le_mul ha (approximation G) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 33 / 32)
    change ‖a‖ * ‖w - (8 : ℝ) • tangent G‖ ≤ _ at h'
    nlinarith [pow_pos G.radius_pos 3]
  have hraw (a : Features p.d) (ha : ‖a‖ ≤ 33 / 32) :
      |⟪a,w⟫| ≤ 58 * G.ε ^ 3 + 8 * |⟪a,tangent G⟫| := by
    have h := abs_add_le (⟪a,w⟫ - 8 * ⟪a,tangent G⟫) (8 * ⟪a,tangent G⟫)
    rw [sub_add_cancel, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at h
    linarith [herr a ha]
  have hbt : |⟪b,tangent G⟫| ≤ G.ε ^ 2 := by
    rw [show b = row G i from rfl, row_tangent, abs_mul, G.labels, one_mul]
    exact (abs_real_inner_le_norm _ _).trans ((mul_le_mul (G.radius i) (tangent_norm G)
      (norm_nonneg _) G.radius_pos.le).trans_eq (sq _).symm)
  have hu : |⟪b,w⟫| ≤ 58 * G.ε ^ 3 + 8 * G.ε ^ 2 := by linarith [hraw b hb]
  have hsu : |⟪shift b,w⟫| ≤ 58 * G.ε ^ 3 + 8 * ((κ + G.ε) * G.ε) := by
    have h : |⟪shift b,tangent G⟫| ≤ (κ + G.ε) * G.ε := shifted_tangent G i
    linarith [hraw (shift b) hs]
  have htotal := abs_add_le (⟪b,w⟫ - 8 * ⟪b,tangent G⟫ + 8 * ⟪f,v⟫ * ⟪b,w⟫)
    (8 * ⟪shift f,v⟫ * ⟪shift b,w⟫)
  have hsum := abs_add_le (⟪b,w⟫ - 8 * ⟪b,tangent G⟫) (8 * ⟪f,v⟫ * ⟪b,w⟫)
  rw [abs_mul (8 * _) _] at hsum htotal
  have h1 := mul_le_mul (hcoef f hf) hu (abs_nonneg _) (by positivity : 0 ≤ 17 * G.ε ^ 2)
  have h2 := mul_le_mul (hcoef (shift f) hsf) hsu (abs_nonneg _) (by positivity : 0 ≤ 17 * G.ε ^ 2)
  have h4 := mul_le_mul_of_nonneg_right G.radius_le (pow_nonneg G.radius_pos.le 3)
  have h5 := mul_le_mul_of_nonneg_right (mul_self_le_mul_self G.radius_pos.le G.radius_le)
    (pow_nonneg G.radius_pos.le 3)
  change |(1 + 8 * ⟪f,v⟫) * ⟪b,w⟫ + 8 * ⟪shift f,v⟫ * ⟪shift b,w⟫ - 8 * ⟪b,tangent G⟫| ≤
    (72 + 136 * κ) * G.ε ^ 3
  rw [show (1 + 8 * ⟪f,v⟫) * ⟪b,w⟫ + 8 * ⟪shift f,v⟫ * ⟪shift b,w⟫ - 8 * ⟪b,tangent G⟫ =
    (⟪b,w⟫ - 8 * ⟪b,tangent G⟫ + 8 * ⟪f,v⟫ * ⟪b,w⟫) + 8 * ⟪shift f,v⟫ * ⟪shift b,w⟫ by ring]
  linarith only [htotal, hsum, h1, h2, h4, h5, herr b hb, pow_nonneg G.radius_pos.le 3]

lemma positive (i : Fin p.n) : 0 < margin .conv p.d (row G i) (finalPoint G) := by
  have h := (abs_le.mp (score_approximation G i)).1
  rw [row_tangent] at h
  have hg : (9 + 17 * ‖shift G.axis - G.axis‖) * G.ε ^ 3 <
      G.y i * ⟪G.h i, tangent G⟫ := G.gap i
  linarith

end LongTails.Proofs.CenteredLogisticDynamics
