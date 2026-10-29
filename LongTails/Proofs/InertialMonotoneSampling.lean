import LongTails.Algorithms.InertialRegularizedExtragradient
import LongTails.Proofs.InertialMonotoneMoments
import LongTails.Proofs.RegularizedProxEgSampling

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.InertialMonotone

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] [IsProbabilityMeasure P] in
lemma batchTrial_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (μ η : ℝ) (b : ℕ) :
    Measurable (fun a : (E × E) × ((Fin b → Ω) × (Fin b → Ω)) =>
      batchTrial g μ η b a.1 a.2.1 a.2.2) := by
  have hs1 : Measurable (fun a : (E × E) × ((Fin b → Ω) × (Fin b → Ω)) =>
      ∑ i, g a.1.2 (a.2.1 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hg.comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
  have hy : Measurable (fun a : (E × E) × ((Fin b → Ω) × (Fin b → Ω)) =>
      extrapolated μ η b a.1.1 a.1.2 (∑ i, g a.1.2 (a.2.1 i))) := by
    unfold extrapolated
    fun_prop
  have hs2 : Measurable (fun a : (E × E) × ((Fin b → Ω) × (Fin b → Ω)) =>
      ∑ i, g (extrapolated μ η b a.1.1 a.1.2 (∑ j, g a.1.2 (a.2.1 j))) (a.2.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hg.comp (hy.prodMk (by fun_prop))
  unfold batchTrial
  fun_prop

lemma batch_trial_contraction {F : E → E} {g : E → Ω → E} {σ L μ η : ℝ}
    (hF : Continuous F) (hμ : 0 ≤ μ) (hη : 0 ≤ η)
    (hcap : 2 * η * μ + 2 * η ^ 2 * (L + μ) ^ 2 ≤ 1)
    (hmono : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g σ)
    (x z p : E) (hp : HolderMonotone.reg F μ x p = 0) {b : ℕ} (hb : 0 < b) :
    let Q := Measure.pi (fun _ : Fin b => P)
    Integrable (fun ω => ‖batchTrial g μ η b (x, z) ω.1 ω.2 - p‖ ^ 2) (Q.prod Q) ∧
    (∫ ω, ‖batchTrial g μ η b (x, z) ω.1 ω.2 - p‖ ^ 2 ∂Q.prod Q) ≤
      (1 - η * μ) * ‖z - p‖ ^ 2 + 3 * η ^ 2 * (σ ^ 2 / b) := by
  intro Q
  let H := HolderMonotone.reg F μ x
  let ζ : E → (Fin b → Ω) → E := fun a u => (1 / (b : ℝ)) • ∑ i, g a (u i) - F a
  have hζm : Measurable (Function.uncurry ζ) := by
    have hgm (i : Fin b) : Measurable (fun a : E × (Fin b → Ω) => g a.1 (a.2 i)) :=
      hg.measurable.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact ((Finset.measurable_sum _ (fun i _ => hgm i)).const_smul _).sub
      (hF.measurable.comp measurable_fst)
  have hζs (a : E) := StochasticCohypomonotone.batch_integrable hg a hb
  have hHm : Continuous H := by
    change Continuous (fun a => F a + μ • (a - x))
    fun_prop
  have hHs (a : E) : μ * ‖a - p‖ ^ 2 ≤ ⟪H a, a - p⟫ := by
    have hh := HolderMonotone.reg_strong hmono μ x a p
    simpa only [hp, sub_zero] using hh
  have hHl (a c : E) : ‖H a - H c‖ ≤ (L + μ) * ‖a - c‖ := by
    dsimp [H]
    rw [HolderMonotone.reg_sub]
    have hh := norm_add_le (F a - F c) (μ • (a - c))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at hh
    linarith [hlip a c]
  have hh := operator_two_integral (P := Q) (ξ := ζ z) (ζ := ζ) hη hμ hcap H hHm z p hHs hHl
    (hζm.comp measurable_prodMk_left) (hζs z).2.2.1 (hζs z).2.2.2
    hζm (fun a => (hζs a).1) (fun a => (hζs a).2.2.1)
    (fun a => (hζs a).2.1) (fun a => (hζs a).2.2.2)
  have hy (u : Fin b → Ω) : z - η • (H z + ζ z u) =
      extrapolated μ η b x z (∑ i, g z (u i)) := by
    dsimp [H, ζ, HolderMonotone.reg, extrapolated]
    module
  have hw (u v : Fin b → Ω) :
      z - η • (H (z - η • (H z + ζ z u)) + ζ (z - η • (H z + ζ z u)) v) =
        batchTrial g μ η b (x, z) u v := by
    rw [hy]
    dsimp [H, ζ, HolderMonotone.reg, batchTrial]
    module
  simpa only [hw] using hh

end OracleTemplate.InertialMonotone
