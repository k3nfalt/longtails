import LongTails.Proofs.ClippedScalarDescent
import LongTails.Proofs.RademacherDirections
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.MeanInequalitiesPow

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpsaMoments

open OracleTemplate.ClippedSpsa LongTails.Proofs.RademacherDirections
  LongTails.Proofs.ClippedScalarDescent

variable {d : ℕ}

lemma signVec_apply (s : Sign d) (i : Fin d) : signVec s i = sgn (s i) := by
  simp [signVec, sgn]

lemma inner_point (a b : Point d) : ⟪a, b⟫ = ∑ i, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

lemma norm_sq_point (a : Point d) : ‖a‖ ^ 2 = ∑ i, a i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp

lemma inner_signVec (a : Point d) (s : Sign d) : ⟪a, signVec s⟫ = lin (fun i => a i) s := by
  simp [inner_point, signVec_apply, lin]

lemma norm_sq_signVec (s : Sign d) : ‖signVec s‖ ^ 2 = d := by
  rw [norm_sq_point]
  simp [signVec_apply, sgn_sq]

lemma norm_signVec (s : Sign d) : ‖signVec s‖ = Real.sqrt d := by
  rw [← norm_sq_signVec s, Real.sqrt_sq (norm_nonneg _)]

lemma card_sign : (Fintype.card (Sign d) : ℝ) = 2 ^ d := by
  simp [Sign]

lemma signLaw_real_singleton (s : Sign d) : (signLaw d).real {s} = 1 / 2 ^ d := by
  rw [measureReal_def, signLaw, PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _)]
  have h1 : (Fintype.card ({s} : Set (Sign d)) : ENNReal) = 1 := by simp
  rw [h1, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast, card_sign]

lemma integral_signLaw (h : Sign d → ℝ) : ∫ s, h s ∂signLaw d = (∑ s, h s) / 2 ^ d := by
  rw [integral_fintype]
  simp only [signLaw_real_singleton, smul_eq_mul]
  · rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  · exact Integrable.of_finite

lemma avg_inner_mul (a b : Point d) :
    (∑ s, ⟪a, signVec s⟫ * ⟪b, signVec s⟫) / 2 ^ d = ⟪a, b⟫ := by
  simp_rw [inner_signVec]
  rw [sum_lin_mul, inner_point]
  field_simp

lemma avg_inner_sq_mul_sq (a b : Point d) :
    (∑ s, ⟪a, signVec s⟫ ^ 2 * ⟪b, signVec s⟫ ^ 2) / 2 ^ d ≤ 3 * (‖a‖ ^ 2 * ‖b‖ ^ 2) := by
  simp_rw [inner_signVec]
  rw [div_le_iff₀ (by positivity), norm_sq_point, norm_sq_point]
  refine (sum_lin_sq_mul_sq _ _).trans ?_
  have hcs : (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (a i)),
    Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (b i)),
    (by positivity : (0 : ℝ) ≤ 2 ^ d)]

lemma power_mean (X : Sign d → ℝ) {p : ℝ} (hp0 : 0 < p) (hp2 : p ≤ 2) :
    (∑ s, |X s| ^ p) / 2 ^ d ≤ ((∑ s, X s ^ 2) / 2 ^ d) ^ (p / 2) := by
  have hw : ∀ s ∈ (Finset.univ : Finset (Sign d)), (0 : ℝ) ≤ 1 / 2 ^ d := fun _ _ => by positivity
  have hw' : ∑ _s : Sign d, (1 : ℝ) / 2 ^ d = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_sign]; field_simp
  have hz : ∀ s ∈ (Finset.univ : Finset (Sign d)), 0 ≤ |X s| ^ p := fun _ _ => by positivity
  have hr : 1 ≤ 2 / p := by rw [le_div_iff₀ hp0]; linarith
  have hj := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ => (1 : ℝ) / 2 ^ d)
    (fun s => |X s| ^ p) hw hw' hz hr
  have hsimp : ∀ s, (|X s| ^ p) ^ (2 / p) = X s ^ 2 := by
    intro s
    rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hp0.ne']
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp only [hsimp] at hj
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hj
  have hl : (∑ s, |X s| ^ p) / 2 ^ d = 1 / 2 ^ d * ∑ s, |X s| ^ p := by ring
  have hr2 : (∑ s, X s ^ 2) / 2 ^ d = 1 / 2 ^ d * ∑ s, X s ^ 2 := by ring
  rw [hl, hr2]
  have h0 : 0 ≤ 1 / 2 ^ d * ∑ s, |X s| ^ p :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  calc 1 / 2 ^ d * ∑ s, |X s| ^ p = ((1 / 2 ^ d * ∑ s, |X s| ^ p) ^ (2 / p)) ^ (p / 2) := by
        have e : 2 / p * (p / 2) = 1 := by field_simp
        rw [← Real.rpow_mul h0, e, Real.rpow_one]
    _ ≤ (1 / 2 ^ d * ∑ s, X s ^ 2) ^ (p / 2) :=
        Real.rpow_le_rpow (by positivity) hj (by positivity)

lemma avg_abs_inner_rpow (a : Point d) {p : ℝ} (hp0 : 0 < p) (hp2 : p ≤ 2) :
    (∑ s, |⟪a, signVec s⟫| ^ p) / 2 ^ d ≤ ‖a‖ ^ p := by
  refine (power_mean (fun s => ⟪a, signVec s⟫) hp0 hp2).trans (le_of_eq ?_)
  have h := avg_inner_mul a a
  simp only [← sq] at h
  rw [h, real_inner_self_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  push_cast
  congr 1; ring

lemma avg_abs_inner_mul_rpow (a b : Point d) {p : ℝ} (hp0 : 0 < p) (hp2 : p ≤ 2) :
    (∑ s, |⟪a, signVec s⟫ * ⟪b, signVec s⟫| ^ p) / 2 ^ d ≤
      (Real.sqrt 3 * ‖a‖ * ‖b‖) ^ p := by
  refine (power_mean (fun s => ⟪a, signVec s⟫ * ⟪b, signVec s⟫) hp0 hp2).trans ?_
  have h := avg_inner_sq_mul_sq a b
  simp only [mul_pow] at h ⊢
  have hb : 0 ≤ Real.sqrt 3 * ‖a‖ * ‖b‖ := by positivity
  calc ((∑ s, ⟪a, signVec s⟫ ^ 2 * ⟪b, signVec s⟫ ^ 2) / 2 ^ d) ^ (p / 2)
      ≤ (3 * (‖a‖ ^ 2 * ‖b‖ ^ 2)) ^ (p / 2) :=
        Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity))
          h (by positivity)
    _ = ((Real.sqrt 3 * ‖a‖ * ‖b‖) ^ 2) ^ (p / 2) := by
        congr 1
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    _ = (Real.sqrt 3 * ‖a‖ * ‖b‖) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb]; push_cast; congr 1; ring

end LongTails.Proofs.SpsaMoments
