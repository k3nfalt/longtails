import LongTails.Proofs.MarkovNormalizedExecution
import LongTails.Proofs.GdConvex
import LongTails.Proofs.MarkovNormalizedAlignment

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MarkovNormalizedDescent

open Algorithms.MarkovNormalizedBatch MarkovNormalizedExecution

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def alignmentValue (grad : E → E) (g : E → Ω → E) (η : ℝ) (B h : ℕ)
    (x0 : E) (j : ℕ) (ξ : ℕ → Ω) : ℝ :=
  let x := output g η B h x0 ξ j
  ⟪grad x, direction (fun i : Fin B => g x (ξ (j*(B*h)+i.val*h)))⟫

lemma path_descent {f : E → ℝ} {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖)
    (g : E → Ω → E) (B h : ℕ) (x0 : E) (ξ : ℕ → Ω) (K : ℕ) :
    f (output g η B h x0 ξ K) + η*(∑ j ∈ Finset.range K, alignmentValue (gradient f) g η B h x0 j ξ)
      ≤ f x0 + K*(L/2*η^2) := by
  induction K with
  | zero => simp [output]
  | succ k ih =>
    let x := output g η B h x0 ξ k
    let v := direction (fun i : Fin B => g x (ξ (k*(B*h)+i.val*h)))
    have hu := OracleTemplate.Gradient.smooth_upper_bound hg hlip x (x-η • v)
    have hid : x-η • v-x = -(η • v) := by abel
    rw [hid, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_of_nonneg hη] at hu
    have hn : η*‖v‖ ≤ η := mul_le_of_le_one_right hη (norm_direction _)
    have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hη (norm_nonneg _)) hn 2)
      (by positivity : 0 ≤ L/2)
    rw [Finset.sum_range_succ, Nat.cast_succ]
    change f (x-η • v) + η*(_+⟪gradient f x,v⟫) ≤ _
    change f x + _ ≤ _ at ih
    linarith

lemma integrated_descent [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P] {f : E → ℝ} {L η Δ fstar : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖) (hgm : Measurable (gradient f))
    (hlow : ∀ x, fstar ≤ f x) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (B h : ℕ) (x0 : E) (hgap : f x0 - fstar ≤ Δ) (K : ℕ) :
    η*(∑ j ∈ Finset.range K, ∫ ξ, alignmentValue (gradient f) g η B h x0 j ξ ∂P) ≤
      Δ + K*(L/2*η^2) := by
  let A := alignmentValue (gradient f) g η B h x0
  have ha (j) : Integrable (A j) P := by
    have hx := measurable_output hg η B h x0 j
    have hf (i : Fin B) : Measurable (fun ξ => g (output g η B h x0 ξ j) (ξ (j*(B*h)+i.val*h))) :=
      hg.comp (hx.prodMk (measurable_pi_apply _))
    have hm : Measurable (A j) := by
      unfold A alignmentValue direction
      fun_prop
    refine Integrable.of_bound hm.aestronglyMeasurable (‖gradient f x0‖ + j*(L*η)) (.of_forall fun ξ => ?_)
    exact (MarkovBatchContinuation.bound_normalized _ _).trans
      (norm_bound hL hη _ hlip g B h x0 j ξ)
  have hp ξ : η*(∑ j ∈ Finset.range K, A j ξ) ≤ Δ + K*(L/2*η^2) := by
    have hh := path_descent hL hη hgrad hlip g B h x0 ξ K
    have hl := hlow (output g η B h x0 ξ K)
    dsimp only [A]
    linarith
  have hh := integral_mono (μ := P) ((integrable_finsetSum _ (fun j _ => ha j)).const_mul η)
    (integrable_const _) hp
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => ha j), integral_const,
    probReal_univ, one_smul] at hh
  exact hh

end LongTails.Proofs.MarkovNormalizedDescent
