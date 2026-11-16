import LongTails.Proofs.GdConvex
import LongTails.Proofs.SvrgConvex
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManyConstraintStochastic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

structure Regular (law : Measure Ξ) (loss : Ξ → E → ℝ) (grad : Ξ → E → E) (L σ : ℝ)
    (xs : E) : Prop where
  prob : IsProbabilityMeasure law
  measurable : Measurable (Function.uncurry grad)
  convex : ∀ ξ, ConvexOn ℝ univ (loss ξ)
  hasGrad : ∀ ξ x, HasGradientAt (loss ξ) (grad ξ x) x
  lip : ∀ ξ x y, ‖grad ξ x - grad ξ y‖ ≤ L * ‖x - y‖
  lossInt : ∀ x, Integrable (fun ξ => loss ξ x) law
  sqInt : Integrable (fun ξ => ‖grad ξ xs‖ ^ 2) law
  second : ∫ ξ, ‖grad ξ xs‖ ^ 2 ∂law ≤ σ ^ 2

noncomputable def objective (law : Measure Ξ) (loss : Ξ → E → ℝ) (x : E) : ℝ :=
  ∫ ξ, loss ξ x ∂law

noncomputable def meanGrad (law : Measure Ξ) (grad : Ξ → E → E) (x : E) : E :=
  ∫ ξ, grad ξ x ∂law

variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma int_inner {g : Ξ → E} (hg : Integrable g law) (c : E) :
    ∫ ξ, ⟪g ξ, c⟫ ∂law = ⟪∫ ξ, g ξ ∂law, c⟫ := by
  have := integral_inner (𝕜 := ℝ) hg c
  simpa [real_inner_comm] using this

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Regular.gradMeas (h : Regular law loss grad L σ xs) (x : E) :
    Measurable (fun ξ => grad ξ x) :=
  h.measurable.comp (measurable_id.prodMk measurable_const)

lemma Regular.normInt (h : Regular law loss grad L σ xs) :
    Integrable (fun ξ => ‖grad ξ xs‖) law := by
  have := h.prob
  have hm : MemLp (fun ξ => grad ξ xs) 2 law :=
    (memLp_two_iff_integrable_sq_norm (h.gradMeas xs).aestronglyMeasurable).2 h.sqInt
  exact (hm.integrable one_le_two).norm

lemma Regular.gradInt (h : Regular law loss grad L σ xs) (x : E) :
    Integrable (fun ξ => grad ξ x) law := by
  have := h.prob
  refine Integrable.mono' (h.normInt.add (integrable_const (L * ‖x - xs‖)))
    (h.gradMeas x).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  have := h.lip ξ x xs
  calc ‖grad ξ x‖ = ‖grad ξ xs + (grad ξ x - grad ξ xs)‖ := by congr 1; abel
    _ ≤ ‖grad ξ xs‖ + ‖grad ξ x - grad ξ xs‖ := norm_add_le _ _
    _ ≤ ‖grad ξ xs‖ + L * ‖x - xs‖ := by linarith

lemma Regular.sqDiffInt (h : Regular law loss grad L σ xs) (x c : E) :
    Integrable (fun ξ => ‖grad ξ x - c‖ ^ 2) law := by
  have := h.prob
  have hb : ∀ ξ, ‖grad ξ x - c‖ ^ 2 ≤ 2 * ‖grad ξ xs‖ ^ 2 + 2 * (L * ‖x - xs‖ + ‖c‖) ^ 2 := by
    intro ξ
    have h1 : ‖grad ξ x - c‖ ≤ ‖grad ξ xs‖ + (L * ‖x - xs‖ + ‖c‖) := by
      have := h.lip ξ x xs
      calc ‖grad ξ x - c‖ = ‖grad ξ xs + (grad ξ x - grad ξ xs) - c‖ := by congr 1; abel
        _ ≤ ‖grad ξ xs + (grad ξ x - grad ξ xs)‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ ‖grad ξ xs‖ + ‖grad ξ x - grad ξ xs‖ + ‖c‖ := by
            linarith [norm_add_le (grad ξ xs) (grad ξ x - grad ξ xs)]
        _ ≤ _ := by linarith
    have h0 : 0 ≤ ‖grad ξ x - c‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖grad ξ xs‖ - (L * ‖x - xs‖ + ‖c‖))]
  refine Integrable.mono' ((h.sqInt.const_mul 2).add
    (integrable_const (2 * (L * ‖x - xs‖ + ‖c‖) ^ 2)))
    (((h.gradMeas x).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa using hb ξ

lemma Regular.model (h : Regular law loss grad L σ xs) (x y : E) :
    objective law loss y ≤ objective law loss x + ⟪meanGrad law grad x, y - x⟫ +
      L / 2 * ‖y - x‖ ^ 2 := by
  have := h.prob
  have hp : ∀ ξ, loss ξ y ≤ loss ξ x + ⟪grad ξ x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := fun ξ =>
    OracleTemplate.Gradient.smooth_upper_bound (h.hasGrad ξ) (h.lip ξ) x y
  have hi : Integrable (fun ξ => ⟪grad ξ x, y - x⟫) law :=
    (h.gradInt x).inner_const (y - x)
  have hmono := integral_mono (h.lossInt y)
    (((h.lossInt x).add hi).add (integrable_const (L / 2 * ‖y - x‖ ^ 2))) hp
  simp only [Pi.add_apply] at hmono
  have e1 : ∫ ξ, (loss ξ x + ⟪grad ξ x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) ∂law =
      (∫ ξ, loss ξ x ∂law) + ⟪∫ ξ, grad ξ x ∂law, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
    have hA : Integrable (fun ξ => loss ξ x + ⟪grad ξ x, y - x⟫) law := (h.lossInt x).add hi
    rw [integral_add hA (integrable_const _), integral_add (h.lossInt x) hi, integral_const,
      int_inner (h.gradInt x)]
    simp
  rw [e1] at hmono
  simpa [objective, meanGrad] using hmono

lemma Regular.support (h : Regular law loss grad L σ xs) (hL : 0 < L) (x u : E) :
    ⟪meanGrad law grad x, u - x⟫ + (1 / (2 * L)) * ∫ ξ, ‖grad ξ u - grad ξ x‖ ^ 2 ∂law ≤
      objective law loss u - objective law loss x := by
  have := h.prob
  have hp : ∀ ξ, ⟪grad ξ x, u - x⟫ + (1 / (2 * L)) * ‖grad ξ u - grad ξ x‖ ^ 2 ≤
      loss ξ u - loss ξ x := by
    intro ξ
    have := OracleTemplate.FiniteSum.gradient_difference_bound hL (h.convex ξ)
      (fun z => h.hasGrad ξ z) (h.lip ξ) u x
    have hL2 : 0 < 2 * L := by positivity
    have : (1 / (2 * L)) * ‖grad ξ u - grad ξ x‖ ^ 2 ≤
        loss ξ u - loss ξ x - ⟪grad ξ x, u - x⟫ := by
      rw [one_div, inv_mul_le_iff₀ hL2]; linarith
    linarith
  have hi : Integrable (fun ξ => ⟪grad ξ x, u - x⟫) law := (h.gradInt x).inner_const (u - x)
  have hsq : Integrable (fun ξ => ‖grad ξ u - grad ξ x‖ ^ 2) law := by
    have hb : ∀ ξ, ‖grad ξ u - grad ξ x‖ ^ 2 ≤ (L * ‖u - x‖) ^ 2 := fun ξ =>
      pow_le_pow_left₀ (norm_nonneg _) (h.lip ξ u x) 2
    refine Integrable.mono' (integrable_const ((L * ‖u - x‖) ^ 2))
      (((h.gradMeas u).sub (h.gradMeas x)).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb ξ
  have hB : Integrable (fun ξ => ⟪grad ξ x, u - x⟫ + 1 / (2 * L) * ‖grad ξ u - grad ξ x‖ ^ 2)
      law := hi.add (hsq.const_mul _)
  have hC : Integrable (fun ξ => loss ξ u - loss ξ x) law := (h.lossInt u).sub (h.lossInt x)
  have hmono := integral_mono hB hC hp
  rw [integral_add hi (hsq.const_mul _), integral_const_mul, integral_sub (h.lossInt u)
    (h.lossInt x), int_inner (h.gradInt x)] at hmono
  simpa [objective, meanGrad] using hmono

lemma Regular.variance (h : Regular law loss grad L σ xs) (x : E) :
    ∫ ξ, ‖grad ξ x - meanGrad law grad x‖ ^ 2 ∂law ≤
      2 * ∫ ξ, ‖grad ξ xs - grad ξ x‖ ^ 2 ∂law + 2 * σ ^ 2 := by
  have := h.prob
  have hc : ∫ ξ, ‖grad ξ x - meanGrad law grad x‖ ^ 2 ∂law ≤ ∫ ξ, ‖grad ξ x‖ ^ 2 ∂law := by
    have hint := h.gradInt x
    have h2 : Integrable (fun ξ => ‖grad ξ x‖ ^ 2) law := by
      simpa using h.sqDiffInt x 0
    have hexp : ∀ ξ, ‖grad ξ x - meanGrad law grad x‖ ^ 2 =
        ‖grad ξ x‖ ^ 2 - 2 * ⟪grad ξ x, meanGrad law grad x⟫ + ‖meanGrad law grad x‖ ^ 2 := by
      intro ξ; rw [norm_sub_sq_real]
    simp_rw [hexp]
    have hI : Integrable (fun ξ => 2 * ⟪grad ξ x, meanGrad law grad x⟫) law :=
      (hint.inner_const _).const_mul 2
    have hD : Integrable (fun ξ => ‖grad ξ x‖ ^ 2 - 2 * ⟪grad ξ x, meanGrad law grad x⟫) law :=
      h2.sub hI
    rw [integral_add hD (integrable_const _), integral_sub h2 hI, integral_const_mul,
      int_inner hint, integral_const]
    simp only [meanGrad, real_inner_self_eq_norm_sq, probReal_univ, one_smul]
    nlinarith [sq_nonneg ‖∫ ξ, grad ξ x ∂law‖]
  have hp : ∀ ξ, ‖grad ξ x‖ ^ 2 ≤ 2 * ‖grad ξ xs - grad ξ x‖ ^ 2 + 2 * ‖grad ξ xs‖ ^ 2 := by
    intro ξ
    have : ‖grad ξ x‖ ≤ ‖grad ξ xs - grad ξ x‖ + ‖grad ξ xs‖ := by
      calc ‖grad ξ x‖ = ‖grad ξ xs - (grad ξ xs - grad ξ x)‖ := by congr 1; abel
        _ ≤ ‖grad ξ xs‖ + ‖grad ξ xs - grad ξ x‖ := norm_sub_le _ _
        _ = _ := by ring
    have h0 := norm_nonneg (grad ξ x)
    nlinarith [sq_nonneg (‖grad ξ xs - grad ξ x‖ - ‖grad ξ xs‖)]
  have hsq : Integrable (fun ξ => ‖grad ξ xs - grad ξ x‖ ^ 2) law := by
    refine Integrable.mono' (integrable_const ((L * ‖xs - x‖) ^ 2))
      (((h.gradMeas xs).sub (h.gradMeas x)).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h.lip ξ xs x) 2
  have hE : Integrable (fun ξ => 2 * ‖grad ξ xs - grad ξ x‖ ^ 2 + 2 * ‖grad ξ xs‖ ^ 2) law :=
    (hsq.const_mul 2).add (h.sqInt.const_mul 2)
  have hmono := integral_mono (by simpa using h.sqDiffInt x 0) hE hp
  rw [integral_add (hsq.const_mul 2) (h.sqInt.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  linarith [h.second]

end LongTails.Proofs.ManyConstraintStochastic
