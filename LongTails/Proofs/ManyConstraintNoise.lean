import LongTails.Proofs.ManyConstraintStep
import LongTails.Proofs.FiniteVarianceBatch

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintNoise

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]

noncomputable def batch (grad : Ξ → E → E) {b : ℕ} (ω : Fin b → Ξ) (x : E) : E :=
  (1 / (b : ℝ)) • ∑ i, grad (ω i) x

variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E}

lemma batch_measurable (h : Regular law loss grad L σ xs) (b : ℕ) (x : E) :
    Measurable (fun ω : Fin b → Ξ => batch grad ω x) := by
  unfold batch
  refine Measurable.const_smul ?_ _
  exact Finset.measurable_sum _ fun i _ => (h.gradMeas x).comp (measurable_pi_apply i)

lemma batch_integrable (h : Regular law loss grad L σ xs) (b : ℕ) (x : E) :
    Integrable (fun ω : Fin b → Ξ => batch grad ω x) (Measure.pi fun _ => law) := by
  have := h.prob
  unfold batch
  refine Integrable.smul _ (integrable_finsetSum _ fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : Fin b => law) i).integrable_comp_of_integrable
    (h.gradInt x)

lemma batch_mean (h : Regular law loss grad L σ xs) {b : ℕ} (hb : 0 < b) (x : E) :
    ∫ ω, batch grad ω x ∂(Measure.pi fun _ : Fin b => law) = meanGrad law grad x := by
  have := h.prob
  unfold batch
  have hI : ∀ i ∈ (Finset.univ : Finset (Fin b)),
      Integrable (fun ω : Fin b → Ξ => grad (ω i) x) (Measure.pi fun _ => law) := fun i _ =>
    (measurePreserving_eval (fun _ : Fin b => law) i).integrable_comp_of_integrable (h.gradInt x)
  rw [integral_smul, integral_finsetSum _ hI]
  have hi (i : Fin b) : ∫ ω, grad (ω i) x ∂(Measure.pi fun _ : Fin b => law) =
      meanGrad law grad x :=
    (show HasLaw (fun ω : Fin b → Ξ => ω i) law (Measure.pi fun _ : Fin b => law) from
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩).integral_comp
        (h.gradMeas x).aestronglyMeasurable
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul]
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [one_div, inv_mul_cancel₀ hb', one_smul]

lemma batch_variance (h : Regular law loss grad L σ xs) {b : ℕ} (hb : 0 < b) (x : E) :
    Integrable (fun ω : Fin b → Ξ => ‖batch grad ω x - meanGrad law grad x‖ ^ 2)
      (Measure.pi fun _ => law) ∧
    ∫ ω, ‖batch grad ω x - meanGrad law grad x‖ ^ 2 ∂(Measure.pi fun _ : Fin b => law) ≤
      (2 * ∫ ξ, ‖grad ξ xs - grad ξ x‖ ^ 2 ∂law + 2 * σ ^ 2) / b := by
  have := h.prob
  have hv := OracleTemplate.RobustGradient.finite_mean_variance (P := law) (h.gradMeas x)
    (h.gradInt x) (meanGrad law grad x) (h.sqDiffInt x _) rfl b hb
  refine ⟨hv.1, ?_⟩
  change ∫ ω, ‖(1 / (b : ℝ)) • ∑ i, grad (ω i) x - meanGrad law grad x‖ ^ 2
    ∂(Measure.pi fun _ : Fin b => law) ≤ _
  rw [hv.2]
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact div_le_div_of_nonneg_right (h.variance x) hbR.le

lemma noise_bound (h : Regular law loss grad L σ xs) (hP : ∀ j z, IsProj (K j) z (P j z))
    {β c : ℝ} (hβ : 0 < β) (hc : 0 ≤ c) {b : ℕ} (hb : 0 < b) (s x w : E) :
    let G := Fgrad law grad β P x
    let v := fun (j : Fin m) (ω : Fin b → Ξ) => batch grad ω x + hest β P s x j
    (∀ j, Integrable (fun ω => ⟪G - v j ω, w⟫ + c * ‖G - v j ω‖ ^ 2)
      (Measure.pi fun _ => law)) ∧
    (𝔼 j, ∫ ω, (⟪G - v j ω, w⟫ + c * ‖G - v j ω‖ ^ 2) ∂(Measure.pi fun _ => law)) ≤
      c * (2 * β * (hpen β P s - hpen β P x - ⟪hgrad β P x, s - x⟫) +
        (2 * ∫ ξ, ‖grad ξ xs - grad ξ x‖ ^ 2 ∂law + 2 * σ ^ 2) / b) := by
  intro G v
  have := h.prob
  set μb := Measure.pi fun _ : Fin b => law with hμb
  have hbi := batch_integrable h b x
  obtain ⟨hvi, hvb⟩ := batch_variance h hb x
  set a := fun ω : Fin b → Ξ => meanGrad law grad x - batch grad ω x with ha
  set d := fun j : Fin m => hgrad β P x - hest β P s x j with hd
  have hsplit : ∀ j ω, G - v j ω = a ω + d j := by
    intro j ω; simp only [G, v, Fgrad, a, d]; abel
  have hai : Integrable a μb := (integrable_const _).sub hbi
  have ha0 : ∫ ω, a ω ∂μb = 0 := by
    rw [integral_sub (integrable_const _) hbi, batch_mean h hb, integral_const]; simp
  have hasq : Integrable (fun ω => ‖a ω‖ ^ 2) μb := by
    simpa [a, norm_sub_rev] using hvi
  have hpoint : ∀ j ω, ⟪G - v j ω, w⟫ + c * ‖G - v j ω‖ ^ 2 =
      (⟪a ω, w⟫ + c * (‖a ω‖ ^ 2 + 2 * ⟪a ω, d j⟫)) + (⟪d j, w⟫ + c * ‖d j‖ ^ 2) := by
    intro j ω
    rw [hsplit, inner_add_left, norm_add_sq_real]; ring
  have hint : ∀ j, Integrable (fun ω => (⟪a ω, w⟫ + c * (‖a ω‖ ^ 2 + 2 * ⟪a ω, d j⟫)))
      μb := fun j =>
    (hai.inner_const w).add ((hasq.add ((hai.inner_const (d j)).const_mul 2)).const_mul c)
  refine ⟨fun j => ?_, ?_⟩
  · simp_rw [hpoint j]; exact (hint j).add (integrable_const _)
  · have hj : ∀ j, ∫ ω, (⟪G - v j ω, w⟫ + c * ‖G - v j ω‖ ^ 2) ∂μb =
        c * ∫ ω, ‖a ω‖ ^ 2 ∂μb + (⟪d j, w⟫ + c * ‖d j‖ ^ 2) := by
      intro j
      simp_rw [hpoint j]
      rw [integral_add (hint j) (integrable_const _), integral_const]
      have e1 : Integrable (fun ω => ‖a ω‖ ^ 2 + 2 * ⟪a ω, d j⟫) μb :=
        hasq.add ((hai.inner_const (d j)).const_mul 2)
      rw [integral_add (hai.inner_const w) (e1.const_mul c), integral_const_mul,
        integral_add hasq ((hai.inner_const (d j)).const_mul 2), integral_const_mul,
        int_inner hai, int_inner hai, ha0]
      simp
    simp_rw [hj]
    have hdmean : (𝔼 j, ⟪d j, w⟫) = 0 := by
      have hu := hest_unbiased (P := P) β s x
      simp only [d, inner_sub_left, Finset.expect_sub_distrib, Fintype.expect_const,
        OracleTemplate.FiniteSum.expect_inner_left, hu, sub_self]
    have hvar := hest_variance hP hβ s x
    have hdv : (𝔼 j, ‖d j‖ ^ 2) ≤ 2 * β * (hpen β P s - hpen β P x - ⟪hgrad β P x, s - x⟫) := by
      simpa only [d, norm_sub_rev] using hvar
    simp only [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect, hdmean]
    have hab : ∫ ω, ‖a ω‖ ^ 2 ∂μb ≤ (2 * ∫ ξ, ‖grad ξ xs - grad ξ x‖ ^ 2 ∂law + 2 * σ ^ 2) / b := by
      simpa [a, norm_sub_rev] using hvb
    nlinarith [mul_le_mul_of_nonneg_left hab hc, mul_le_mul_of_nonneg_left hdv hc]

end LongTails.Proofs.ManyConstraintNoise
