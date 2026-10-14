import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.ClippedExtragradientMoments
import LongTails.Proofs.GeneralizedMonotoneRegularization

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ClippedExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma measurable_batch_reply {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (n : ℕ) (r : ℝ) (c : E) :
    Measurable (fun w : E × (Fin n → Ω) =>
      regularizedReply r c w.1 ((1 / (n : ℝ)) • ∑ i, g w.1 (w.2 i))) := by
  unfold regularizedReply
  apply Measurable.add
  · apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i _
    exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · fun_prop

lemma batch_reply_moments {g : E → Ω → E} {F : E → E} {σ r : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = F x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) P)
    (hv : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ 2 ∂P) ≤ σ ^ 2)
    (n : ℕ) (hn : 0 < n) (c x : E) :
    Integrable (fun ξ : Fin n → Ω =>
      regularizedReply r c x ((1 / (n : ℝ)) • ∑ i, g x (ξ i)))
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω,
      regularizedReply r c x ((1 / (n : ℝ)) • ∑ i, g x (ξ i))
      ∂Measure.pi (fun _ : Fin n => P)) = HolderMonotone.reg F r c x ∧
    Integrable (fun ξ : Fin n → Ω =>
      ‖regularizedReply r c x ((1 / (n : ℝ)) • ∑ i, g x (ξ i)) -
        HolderMonotone.reg F r c x‖ ^ 2) (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω,
      ‖regularizedReply r c x ((1 / (n : ℝ)) • ∑ i, g x (ξ i)) -
        HolderMonotone.reg F r c x‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => P)) ≤ σ ^ 2 / n := by
  have hm := LightTail.finite_mean_integral (hgi x) n hn
  have hvv := RobustGradient.finite_mean_variance
    (hg.comp measurable_prodMk_left) (hgi x) (F x) (hvi x) (hmean x) n hn
  simp only [Function.comp_def, Function.uncurry_apply_pair] at hvv
  have he (ξ : Fin n → Ω) :
      regularizedReply r c x ((1 / (n : ℝ)) • ∑ i, g x (ξ i)) -
        HolderMonotone.reg F r c x = (1 / (n : ℝ)) • ∑ i, g x (ξ i) - F x := by
    unfold regularizedReply HolderMonotone.reg
    abel
  refine ⟨hm.1.add (integrable_const _), ?_, ?_, ?_⟩
  · unfold regularizedReply HolderMonotone.reg
    rw [integral_add hm.1 (integrable_const _), hm.2, hmean]
    simp
  · simpa only [he] using hvv.1
  · simp_rw [he]
    rw [hvv.2]
    exact div_le_div_of_nonneg_right (hv x) (Nat.cast_nonneg n)

end OracleTemplate.ClippedExtragradient
