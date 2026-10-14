import LongTails.Proofs.HeavyTailedClipping
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.HeavyTailedMarkovGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def heavyError (a D R p : ℝ) (v e : E) : ℝ :=
  a * ⟪e, v⟫ + min ((a * ‖e‖) ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1))
    (2 * R * a * ‖e‖)

lemma heavyError_bound {a D R p C : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (hR : 0 ≤ R)
    {v e : E} (hv : ‖v‖ ≤ 2 * R) (he : ‖e‖ ≤ C) :
    |heavyError a D R p v e| ≤ 4 * R * a * C := by
  have hm : 0 ≤ min ((a * ‖e‖) ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1))
      (2 * R * a * ‖e‖) := by positivity
  have hmin := min_le_right ((a * ‖e‖) ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1))
    (2 * R * a * ‖e‖)
  have hi : |⟪e, v⟫| ≤ ‖e‖ * (2 * R) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 4 * R * a by positivity)
  calc
    _ ≤ |a * ⟪e, v⟫| + |min ((a * ‖e‖) ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1))
        (2 * R * a * ‖e‖)| := abs_add_le _ _
    _ ≤ 4 * R * a * ‖e‖ := by
      rw [abs_mul, abs_of_nonneg ha, abs_of_nonneg hm]
      have hh' := mul_le_mul_of_nonneg_left hi ha
      nlinarith only [hh', hmin]
    _ ≤ _ := hh

lemma measurable_heavyError [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (a D R p : ℝ) :
    Measurable (fun ve : E × E => heavyError a D R p ve.1 ve.2) := by
  unfold heavyError
  fun_prop

lemma heavyError_le_moment {a : ℝ} (ha : 0 ≤ a) (D R p : ℝ) (v e : E) :
    heavyError a D R p v e ≤ a * ⟪e, v⟫ +
      (a ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) * ‖e‖ ^ p := by
  unfold heavyError
  apply add_le_add (le_refl _)
  calc
    _ ≤ (a * ‖e‖) ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1) := min_le_left _ _
    _ = _ := by rw [Real.mul_rpow ha (norm_nonneg _)]; ring

lemma integral_heavyError_bound {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → E}
    (hg : Measurable g) (hgi : Integrable g P) {u v : E}
    (hmean : ∫ z, g z ∂P = u) {a D R C p σ : ℝ}
    (ha : 0 ≤ a) (hD : 0 < D) (hR : 0 ≤ R) (hC : 0 < C) (hp : 1 ≤ p)
    (hu : ‖u‖ ≤ C / 2) (hv : ‖v‖ ≤ 2 * R)
    (hmi : Integrable (fun z => ‖g z - u‖ ^ p) P)
    (hm : (∫ z, ‖g z - u‖ ^ p ∂P) ≤ σ ^ p) :
    (∫ z, heavyError a D R p v (u - clip C (g z)) ∂P) ≤
      2 * R * a * (σ ^ p / (C / 2) ^ (p - 1)) +
      (a ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) * σ ^ p := by
  let e : Ω → E := fun z => u - clip C (g z)
  let b := a ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he : Measurable e := measurable_const.sub ((measurable_clip C).comp hg)
  have hei : Integrable e P := (integrable_const u).sub (integrable_clip hg hC.le)
  have huC : ‖u‖ ≤ C := by linarith
  have hemi : Integrable (fun z => ‖e z‖ ^ p) P := by
    simpa only [e, norm_sub_rev] using clipped_moment_integrable hg hC.le (by linarith : 0 ≤ p) huC hmi
  have hem : (∫ z, ‖e z‖ ^ p ∂P) ≤ σ ^ p := by
    calc
      _ = ∫ z, ‖clip C (g z) - u‖ ^ p ∂P := by simp only [e, norm_sub_rev]
      _ ≤ ∫ z, ‖g z - u‖ ^ p ∂P := clipped_moment_bound hg hC.le (by linarith) huC hmi
      _ ≤ _ := hm
  have hen : ∀ z, ‖e z‖ ≤ 2 * C := fun z =>
    (norm_sub_le _ _).trans (by have hh := norm_clip_le hC.le (g z); linarith)
  have hhi : Integrable (fun z => heavyError a D R p v (e z)) P :=
    Integrable.of_bound ((measurable_heavyError a D R p).comp
      (measurable_const.prodMk he)).aestronglyMeasurable (4 * R * a * (2 * C))
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact heavyError_bound ha hD hR hv (hen z)))
  have heb : ‖∫ z, e z ∂P‖ ≤ σ ^ p / (C / 2) ^ (p - 1) := by
    dsimp [e]
    rw [integral_sub (integrable_const u) (integrable_clip hg hC.le), integral_const]
    simpa only [probReal_univ, one_smul, norm_sub_rev] using
      clipped_bias_bound hg hgi hmean hC hp hu hmi hm
  have hi : (∫ z, a * ⟪e z, v⟫ ∂P) ≤ 2 * R * a * (σ ^ p / (C / 2) ^ (p - 1)) := by
    have heq : (fun z => ⟪e z, v⟫) = (fun z => ⟪v, e z⟫) :=
      funext (fun z => (real_inner_comm (e z) v).symm)
    rw [integral_const_mul, heq, integral_inner hei]
    have hh := (real_inner_le_norm v (∫ z, e z ∂P)).trans
      (mul_le_mul hv heb (norm_nonneg _) (by positivity))
    nlinarith [mul_le_mul_of_nonneg_left hh ha]
  calc
    _ ≤ ∫ z, a * ⟪e z, v⟫ + b * ‖e z‖ ^ p ∂P :=
      integral_mono hhi ((hei.inner_const v).const_mul a |>.add (hemi.const_mul b))
        (fun z => heavyError_le_moment ha D R p v (e z))
    _ = (∫ z, a * ⟪e z, v⟫ ∂P) + b * ∫ z, ‖e z‖ ^ p ∂P := by
      rw [integral_add ((hei.inner_const v).const_mul a) (hemi.const_mul b), integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add hi (mul_le_mul_of_nonneg_left hem hb)

end OracleTemplate.HeavyTailedMarkovGradient
