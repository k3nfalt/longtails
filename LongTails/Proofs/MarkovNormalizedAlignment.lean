import LongTails.Proofs.MarkovNormalizedExecution
import LongTails.Proofs.FiniteVarianceBatch

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.MarkovNormalizedAlignment

open LongTails.Algorithms.MarkovNormalizedBatch MarkovNormalizedExecution

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma alignment {B : ℕ} (hB : 0 < B) (u : E) (v : Fin B → E) :
    ‖u‖ - 2 * ‖(1 / (B : ℝ)) • ∑ i, v i - u‖ ≤ ⟪u, direction v⟫ := by
  let a := (1 / (B : ℝ)) • ∑ i, v i
  have hp : 0 < (1 / (B : ℝ)) := by positivity
  have ha : ⟪a, direction v⟫ = ‖a‖ := by
    dsimp only [a, direction]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_smul, Real.norm_of_nonneg hp.le]
    by_cases hz : ‖∑ i, v i‖ = 0 <;> simp [hz, sq]
  have hc := abs_real_inner_le_norm (a - u) (direction v)
  have hd := mul_le_mul_of_nonneg_left (norm_direction v) (norm_nonneg (a - u))
  rw [inner_sub_left, ha] at hc
  have ht : ‖u‖ ≤ ‖a - u‖ + ‖a‖ := by
    have := norm_sub_le a (a - u)
    rw [sub_sub_cancel] at this
    linarith
  change ‖u‖ - 2 * ‖a - u‖ ≤ _
  linarith [le_abs_self (‖a‖ - ⟪u, direction v⟫)]

lemma iid_alignment [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → E) (u : E) (hX : Measurable X) (hi : Integrable X P)
    (hm : (∫ z, X z ∂P) = u) (h2 : Integrable (fun z => ‖X z - u‖ ^ 2) P)
    {σ ε : ℝ} (hε : 0 < ε) (hv : (∫ z, ‖X z - u‖ ^ 2 ∂P) ≤ σ ^ 2)
    (B : ℕ) (hB : 0 < B) (hsize : 256 * σ ^ 2 ≤ (B : ℝ) * ε ^ 2) :
    ‖u‖ - ε / 4 ≤ (∫ z : Fin B → Ω, ⟪u, direction (fun i => X (z i))⟫
      ∂Measure.pi (fun _ : Fin B => P)) := by
  let Q := Measure.pi (fun _ : Fin B => P)
  let v := fun z : Fin B → Ω => direction (fun i => X (z i))
  let e := fun z : Fin B → Ω => ‖(1 / (B : ℝ)) • ∑ i, X (z i) - u‖
  have he := OracleTemplate.RobustGradient.finite_mean_variance (P := P) hX hi u h2 hm B hB
  have hvm : Measurable v := by
    have hx (i : Fin B) : Measurable (fun z : Fin B → Ω => X (z i)) :=
      hX.comp (measurable_pi_apply i)
    dsimp [v, direction]
    fun_prop
  have hvi : Integrable (fun z => ⟪u, v z⟫) Q :=
    Integrable.of_bound (show Measurable (fun z => ⟪u, v z⟫) by fun_prop).aestronglyMeasurable ‖u‖
      (.of_forall fun z => (abs_real_inner_le_norm _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (norm_direction _)))
  have hp (z : Fin B → Ω) : ‖u‖ - ε / 8 - (8 / ε) * (e z) ^ 2 ≤ ⟪u, v z⟫ := by
    have h := alignment hB u (fun i => X (z i))
    change ‖u‖ - 2 * e z ≤ ⟪u, v z⟫ at h
    have hquad : 2 * e z ≤ ε / 8 + 8 / ε * e z ^ 2 := by
      field_simp
      nlinarith [sq_nonneg (8 * e z - ε)]
    linarith
  have hh := integral_mono (μ := Q) ((integrable_const _).sub (he.1.const_mul (8 / ε))) hvi hp
  change (∫ z, ‖u‖ - ε / 8 - (8 / ε) * (e z) ^ 2 ∂Q) ≤ _ at hh
  have hei : Integrable (fun z => e z ^ 2) Q := he.1
  rw [integral_sub (integrable_const _) (hei.const_mul _), integral_const, probReal_univ,
    one_smul, integral_const_mul] at hh
  have ha : (∫ z, e z ^ 2 ∂Q) ≤ ε ^ 2 / 256 := by
    rw [he.2]
    apply (div_le_iff₀ (by exact_mod_cast hB : 0 < (B : ℝ))).mpr
    linarith
  change ‖u‖ - ε / 4 ≤ ∫ z, ⟪u, v z⟫ ∂Q
  have hmul := mul_le_mul_of_nonneg_left ha (show 0 ≤ 8 / ε by positivity)
  have hid : 8 / ε * (ε ^ 2 / 256) = ε / 32 := by field_simp; ring
  rw [hid] at hmul
  linarith

end LongTails.Proofs.MarkovNormalizedAlignment

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.MarkovBatchContinuation

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def value (P : Measure Ω) (g : E → Ω → E) (grad : E → E) (n : ℕ) (x v : E) : ℝ :=
  ∫ y : Fin n → Ω, let a := v + ∑ i, g x (y i)
    ⟪grad x, ‖a‖⁻¹ • a⟫ ∂Measure.pi (fun _ : Fin n => P)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma bound_normalized (u v : E) : |⟪u, ‖v‖⁻¹ • v⟫| ≤ ‖u‖ := by
  refine (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  by_cases hz : ‖v‖ = 0 <;> simp [hz]

lemma measurable_value (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {grad : E → E}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad) (n : ℕ) :
    Measurable (Function.uncurry (value P g grad n)) := by
  let F := fun z : (E × E) × (Fin n → Ω) =>
    let a := z.1.2 + ∑ i, g z.1.1 (z.2 i)
    ⟪grad z.1.1, ‖a‖⁻¹ • a⟫
  have hm (i : Fin n) : Measurable (fun z : (E × E) × (Fin n → Ω) => g z.1.1 (z.2 i)) :=
    hg.comp ((measurable_fst.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hF : Measurable F := by dsimp [F]; fun_prop
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma value_bound (P : Measure Ω) [IsProbabilityMeasure P] (g : E → Ω → E)
    (grad : E → E) (n : ℕ) (x v : E) : |value P g grad n x v| ≤ ‖grad x‖ := by
  simpa [value] using norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin n => P))
    (f := fun y => let a := v + ∑ i, g x (y i); ⟪grad x, ‖a‖⁻¹ • a⟫)
    (.of_forall fun y => bound_normalized (grad x) _)

lemma value_succ (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (grad : E → E) (n : ℕ) (x v : E) :
    value P g grad (n + 1) x v = ∫ z, value P g grad n x (v + g x z) ∂P := by
  let F := fun z : Ω × (Fin n → Ω) =>
    let a := v + g x z.1 + ∑ i, g x (z.2 i)
    ⟪grad x, ‖a‖⁻¹ • a⟫
  have hgx : Measurable (g x) := hg.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable F := by dsimp [F]; fun_prop
  let Q := Measure.pi (fun _ : Fin n => P)
  let R := Measure.pi (fun _ : Fin (n + 1) => P)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
  have he : MeasurePreserving e R (P.prod Q) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
  have hi : Integrable F (P.prod Q) := Integrable.of_bound hF.aestronglyMeasurable ‖grad x‖
    (.of_forall fun _ => bound_normalized _ _)
  have heq : value P g grad (n+1) x v = ∫ y, F (e y) ∂R := by
    unfold value
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [Fin.sum_univ_succ]
    simp [F, e, add_assoc, MeasurableEquiv.piFinSuccAbove, Fin.tail]
  rw [heq, ← integral_map he.measurable.aemeasurable hF.aestronglyMeasurable, he.map_eq,
    integral_prod _ hi]
  rfl

end LongTails.Proofs.MarkovBatchContinuation
