import LongTails.Proofs.RelativeCurvatureProducts
import LongTails.Proofs.RelativeCurvatureValidation

namespace LongTails.Proofs.RelativeCurvatureExecution

open OracleTemplate LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.RelativeCurvatureSearch
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma eval_transport {Q R U : Type*} {k l : ℕ} (h : k = l)
    (plan : QueryPlan Q R U k) (O : Q → R) :
    (h ▸ plan).eval O = plan.eval O := by subst l; rfl

lemma transformed_product_error (D C : E →L[ℝ] E) (x : Point E) {H a τ : ℝ}
    (ha : 0 ≤ a) (hτ : 0 ≤ τ) (O : Fin 2 × E → Reply E) (v : E)
    (hp : ‖(product D x H τ v).eval O - C v‖ ≤ τ / 4) :
    ‖(transformedProduct D x H a τ v).eval O -
      RelativeCurvatureSpectrum.transformed C a v‖ ≤ τ := by
  have hd : 0 < 1 + a := by positivity
  have he (w : E) : (1 + a)⁻¹ • ((1 - a) • v - (2 : ℝ) • w) -
      (1 + a)⁻¹ • ((1 - a) • v - (2 : ℝ) • C v) =
        (-(2 / (1 + a))) • (w - C v) := by module
  simp only [transformedProduct, QueryPlan.eval_map, RelativeCurvatureSpectrum.transformed,
    smul_apply, sub_apply, ContinuousLinearMap.id_apply]
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos (by norm_num) hd)]
  have hb : 2 / (1 + a) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
  have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 / (1 + a) by positivity)
  have h' := mul_le_mul_of_nonneg_right hb (show 0 ≤ τ / 4 by positivity)
  linarith

lemma filter_first (D : E →L[ℝ] E) (x : Point E) (H a τ : ℝ) (u : E)
    (O : Fin 2 × E → Reply E) (n : ℕ) :
    ((filter D x H a τ u (n + 1)).eval O).1 = ((filter D x H a τ u n).eval O).2 := by
  simp only [filter, eval_transport, QueryPlan.eval_bind, QueryPlan.eval_map]

lemma filter_recurrence (D : E →L[ℝ] E) (x : Point E) (H a τ : ℝ) (u : E)
    (O : Fin 2 × E → Reply E) (n : ℕ) :
    ((filter D x H a τ u (n + 2)).eval O).2 =
      (2 : ℝ) • ((transformedProduct D x H a τ
        ((filter D x H a τ u (n + 1)).eval O).2).eval O) -
          ((filter D x H a τ u n).eval O).2 := by
  rw [filter]
  simp only [eval_transport, QueryPlan.eval_bind, QueryPlan.eval_map, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte, filter_first]

lemma filter_error (D : E →L[ℝ] E) (x : Point E) (H a τ : ℝ) (u : E)
    (O : Fin 2 × E → Reply E) (Z : E →L[ℝ] E) (hZ : ‖Z‖ ≤ 5) (hτ : 0 ≤ τ)
    (hp : ∀ v, ‖(transformedProduct D x H a τ v).eval O - Z v‖ ≤ τ) (n : ℕ) :
    ‖((filter D x H a τ u n).eval O).2 -
      RelativeCurvatureRecurrence.exactFilter Z u n‖ ≤ τ * 12 ^ n := by
  apply RelativeCurvatureRecurrence.recurrence_error Z hZ u
    (fun k => ((filter D x H a τ u k).eval O).2) hτ
  · rfl
  · simpa [filter, QueryPlan.eval_bind, QueryPlan.eval_map, QueryPlan.eval] using hp u
  · intro k
    rw [filter_recurrence]
    have he (v w z : E) : (2 : ℝ) • v - z - ((2 : ℝ) • w - z) = (2 : ℝ) • (v - w) := by module
    rw [he, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hp _) (by norm_num)

lemma search_sound (D C : E →L[ℝ] E) (x : Point E) (H a : ℝ) (u : E)
    (O : Fin 2 × E → Reply E) (n : ℕ) (out : E)
    (hp : ∀ v, ‖(product D x H (a / 4) v).eval O - C v‖ ≤ a / 16)
    (hs : (search D x H a u n).eval O = some out) :
    ∃ v : E, ‖v‖ = 1 ∧ out = D v ∧ ⟪v, C v⟫ ≤ -7 * a / 16 := by
  classical
  let τ := a / (128 * (12 : ℝ) ^ n)
  let z := ((filter D x H a τ (‖u‖⁻¹ • u) n).eval O).2
  let v := ‖z‖⁻¹ • z
  have he : (search D x H a u n).eval O =
      if z ≠ 0 ∧ ⟪v, (product D x H (a / 4) v).eval O⟫ ≤ -a / 2
      then some (D v) else none := by
    simp only [search, eval_transport, QueryPlan.eval_bind, QueryPlan.eval_map]
    rfl
  rw [he] at hs
  split at hs
  · rename_i h
    have hn : ‖v‖ = 1 := by simp [v, norm_smul, norm_ne_zero_iff.mpr h.1]
    refine ⟨v, hn, (Option.some.inj hs).symm, ?_⟩
    exact RelativeCurvatureValidation.validation_sound C v _ hn.le (hp v) h.2
  · simp at hs

lemma search_complete (D C : E →L[ℝ] E) (x : Point E) (H : ℝ) {a : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) (hC : ‖C‖ ≤ 2) (u : E)
    (O : Fin 2 × E → Reply E) (n : ℕ)
    (hZ : ‖RelativeCurvatureSpectrum.transformed C a‖ ≤ 5)
    (hp : ∀ v, ‖(product D x H (a / (128 * (12 : ℝ) ^ n)) v).eval O - C v‖ ≤
      (a / (128 * (12 : ℝ) ^ n)) / 4)
    (hv : ∀ v, ‖(product D x H (a / 4) v).eval O - C v‖ ≤ a / 16)
    (hw : 16 ≤ a * ‖RelativeCurvatureRecurrence.exactFilter
      (RelativeCurvatureSpectrum.transformed C a) (‖u‖⁻¹ • u) n‖ ^ 2)
    (hq : let w := RelativeCurvatureRecurrence.exactFilter (RelativeCurvatureSpectrum.transformed C a) (‖u‖⁻¹ • u) n;
      ⟪w, C w⟫ + a * ‖w‖ ^ 2 ≤ 2) :
    ∃ out, (search D x H a u n).eval O = some out := by
  classical
  let τ := a / (128 * (12 : ℝ) ^ n)
  let z := ((filter D x H a τ (‖u‖⁻¹ • u) n).eval O).2
  let w := RelativeCurvatureRecurrence.exactFilter
    (RelativeCurvatureSpectrum.transformed C a) (‖u‖⁻¹ • u) n
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have ht : ∀ v, ‖(transformedProduct D x H a τ v).eval O -
      RelativeCurvatureSpectrum.transformed C a v‖ ≤ τ :=
    fun v => transformed_product_error D C x ha.le hτ O v (hp v)
  have he : ‖z - w‖ ≤ a / 128 := by
    have h := filter_error D x H a τ (‖u‖⁻¹ • u) O
      (RelativeCurvatureSpectrum.transformed C a) hZ hτ ht n
    have hcancel : τ * 12 ^ n = a / 128 := by dsimp [τ]; field_simp
    simpa only [hcancel] using h
  obtain ⟨hz, hr⟩ := RelativeCurvatureValidation.validation_complete C hC ha ha₁ w z
    ((product D x H (a / 4) (‖z‖⁻¹ • z)).eval O) hw hq he (hv _)
  refine ⟨D (‖z‖⁻¹ • z), ?_⟩
  simp only [search, eval_transport, QueryPlan.eval_bind, QueryPlan.eval_map]
  change (if z ≠ 0 ∧ ⟪‖z‖⁻¹ • z, (product D x H (a / 4) (‖z‖⁻¹ • z)).eval O⟫ ≤ -a / 2
    then some (D (‖z‖⁻¹ • z)) else none) = _
  rw [ite_eq_left ⟨hz, hr⟩]

end LongTails.Proofs.RelativeCurvatureExecution
