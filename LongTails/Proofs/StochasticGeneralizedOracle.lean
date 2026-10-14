import LongTails.Proofs.StochasticGeneralizedMeasurability
import LongTails.Proofs.NormSubGaussianBatch

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma batchReply_center (oracle : E → Ω → E) (x v : E) {m : ℕ} (hm : 0 < m)
    (ξ : Fin m → Ω) :
    batchReply oracle x ξ-v = (1/(m : ℝ)) • ∑ i, (oracle x (ξ i)-v) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [batchReply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hm']

omit [CompleteSpace E] in
@[fun_prop] lemma measurable_batchReply {oracle : E → Ω → E}
    (hg : Measurable (Function.uncurry oracle)) (m : ℕ) :
    Measurable (fun w : E × (Fin m → Ω) => batchReply oracle w.1 w.2) := by
  unfold batchReply
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro i hi
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma batchReply_control {oracle : E → Ω → E} {f : E → ℝ} {σ v : ℝ}
    (hg : IsLightTailGradient E Ω p f oracle σ) (hσ : 0 ≤ σ) (x : E)
    (m : ℕ) (hm : 0 < m) (hscale : 32*σ^2/m ≤ v) :
    Integrable (fun ξ : Fin m → Ω => batchReply oracle x ξ) (Measure.pi fun _ : Fin m => p) ∧
      (∫ ξ : Fin m → Ω, batchReply oracle x ξ ∂Measure.pi (fun _ : Fin m => p)) = gradient f x ∧
      Integrable (fun ξ : Fin m → Ω => Real.exp (‖batchReply oracle x ξ-gradient f x‖^2/v))
        (Measure.pi fun _ : Fin m => p) ∧
      (∫ ξ : Fin m → Ω, Real.exp (‖batchReply oracle x ξ-gradient f x‖^2/v)
        ∂Measure.pi (fun _ : Fin m => p)) ≤ Real.exp 1 := by
  have hmean := LightTail.finite_mean_integral (hg.integrable x) m hm
  refine ⟨hmean.1, hmean.2.trans (hg.unbiased x), ?_⟩
  let X : Ω → E := fun ω => oracle x ω-gradient f x
  have hX : Measurable X := ((hg.measurable.comp measurable_prodMk_left).sub_const _)
  have hXi : Integrable X p := (hg.integrable x).sub (integrable_const _)
  have hzero : (∫ ω, X ω ∂p) = 0 := by
    dsimp [X]
    rw [integral_sub (hg.integrable x) (integrable_const _), hg.unbiased]
    simp
  have he : (fun ξ : Fin m → Ω => Real.exp (‖batchReply oracle x ξ-gradient f x‖^2/v)) =
      fun ξ : Fin m → Ω => Real.exp (‖(1/(m : ℝ)) • ∑ i, X (ξ i)‖^2/v) := by
    ext ξ
    rw [batchReply_center oracle x (gradient f x) hm]
  rw [he]
  by_cases hσ0 : σ = 0
  · have hv0 : (∫ ω, ‖X ω‖^2 ∂p) ≤ 0 := by simpa [X, hσ0] using hg.variance x
    have hz := LightTail.ae_zero_of_integral_sq_norm_nonpos (hg.variance_integrable x) hv0
    exact LightTail.finite_mean_exp_of_ae_zero hz m v
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
    have hbatch := LightTail.finite_mean_norm_exp_control hσpos hX hXi hzero
      (hg.exponential_integrable x) (hg.exponential x) m hm
    have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
    exact LightTail.norm_exp_enlarge (show 0 < 32*σ^2/m by positivity) hscale
      (by fun_prop) hbatch.1 hbatch.2

end OracleTemplate.StochasticGeneralized
