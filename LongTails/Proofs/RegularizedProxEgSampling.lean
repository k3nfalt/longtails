import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Setups.StochasticGeneralizedMonotone

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticCohypomonotone

section Laws

variable {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]

lemma map_tuple_infinitePi {n : ℕ} (ι : Fin n → ℕ) (hι : Function.Injective ι) :
    (Measure.infinitePi fun _ : ℕ => p).map (fun ξ (i : Fin n) => ξ (ι i)) =
      Measure.pi fun _ : Fin n => p := by
  have h := StochasticGeneralized.infinitePi_iid p
  have hi := h.independent.precomp hι
  have hp := hi.map_fun_eq_pi_map (fun i => (h.measurable (ι i)).aemeasurable)
  simpa only [h.marginal] using hp

lemma lintegral_tuple {n : ℕ} (ι : Fin n → ℕ) (hι : Function.Injective ι)
    (h : (Fin n → Ω) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ ξ, h (fun i => ξ (ι i)) ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫⁻ u, h u ∂(Measure.pi fun _ : Fin n => p) := by
  rw [← map_tuple_infinitePi p ι hι, lintegral_map hh (by fun_prop)]

lemma lintegral_split (n : ℕ) (h : (Fin n → Ω) → (ℕ → Ω) → ℝ≥0∞)
    (hh : Measurable (Function.uncurry h)) :
    ∫⁻ ξ, h (fun i => ξ i) (fun i => ξ (n + i)) ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫⁻ u, ∫⁻ t, h u t ∂(Measure.infinitePi fun _ : ℕ => p) ∂(Measure.pi fun _ : Fin n => p) := by
  have hm := StochasticGeneralized.splitStream_preserving p n
  calc ∫⁻ ξ, h (fun i => ξ i) (fun i => ξ (n + i)) ∂(Measure.infinitePi fun _ : ℕ => p)
      = ∫⁻ ξ, Function.uncurry h (StochasticGeneralized.splitStream (Ω := Ω) n ξ)
          ∂(Measure.infinitePi fun _ : ℕ => p) := rfl
    _ = ∫⁻ z, Function.uncurry h z
          ∂((Measure.pi fun _ : Fin n => p).prod (Measure.infinitePi fun _ : ℕ => p)) :=
        hm.lintegral_comp hh
    _ = _ := lintegral_prod _ hh.aemeasurable

end Laws

section Batch

variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma batch_integrable {F : E → E} {g : E → Ω → E} {σ : ℝ}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ) (x : E) {b : ℕ} (hb : 0 < b) :
    Integrable (fun u : Fin b → Ω => (1 / (b : ℝ)) • ∑ i, g x (u i) - F x)
        (Measure.pi fun _ : Fin b => p) ∧
      ∫ u, (1 / (b : ℝ)) • ∑ i, g x (u i) - F x ∂(Measure.pi fun _ : Fin b => p) = 0 ∧
      Integrable (fun u : Fin b → Ω => ‖(1 / (b : ℝ)) • ∑ i, g x (u i) - F x‖ ^ 2)
        (Measure.pi fun _ : Fin b => p) ∧
      ∫ u, ‖(1 / (b : ℝ)) • ∑ i, g x (u i) - F x‖ ^ 2 ∂(Measure.pi fun _ : Fin b => p) ≤
        σ ^ 2 / b := by
  have hmx : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hl (i : Fin b) : HasLaw (fun u : Fin b → Ω => u i) p (Measure.pi fun _ : Fin b => p) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have hint (i : Fin b) : Integrable (fun u : Fin b → Ω => g x (u i)) (Measure.pi fun _ => p) :=
    (hl i).integrable_comp (hg.integrable x)
  have hsum : Integrable (fun u : Fin b → Ω => (1 / (b : ℝ)) • ∑ i, g x (u i))
      (Measure.pi fun _ => p) := (integrable_finsetSum _ fun i _ => hint i).smul _
  have hv := RobustGradient.finite_mean_variance (P := p) hmx (hg.integrable x) (F x)
    (hg.variance_integrable x) (hg.unbiased x) b hb
  refine ⟨hsum.sub (integrable_const _), ?_, hv.1, ?_⟩
  · rw [integral_sub hsum (integrable_const _), integral_smul, integral_finsetSum _ fun i _ => hint i]
    have hm (i : Fin b) : ∫ u, g x (u i) ∂(Measure.pi fun _ : Fin b => p) = F x :=
      ((hl i).integral_comp (hg.integrable x).aestronglyMeasurable).trans (hg.unbiased x)
    simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, integral_const,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    simp [hb']
  · rw [hv.2]
    gcongr
    exact hg.variance x

lemma batch_lintegral_sq {F : E → E} {g : E → Ω → E} {σ : ℝ}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ) (x : E) {b : ℕ} (hb : 0 < b) :
    ∫⁻ u, ENNReal.ofReal (‖(1 / (b : ℝ)) • ∑ i, g x (u i) - F x‖ ^ 2)
        ∂(Measure.pi fun _ : Fin b => p) ≤ ENNReal.ofReal (σ ^ 2 / b) := by
  obtain ⟨-, -, h2, h3⟩ := batch_integrable hg x hb
  rw [← ofReal_integral_eq_lintegral_ofReal h2 (Filter.Eventually.of_forall fun _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal h3

lemma batch_lintegral_centered {F : E → E} {g : E → Ω → E} {σ : ℝ}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ) (x a : E) (t : ℝ)
    {b : ℕ} (hb : 0 < b) :
    ∫⁻ u, ENNReal.ofReal (‖a - t • ((1 / (b : ℝ)) • ∑ i, g x (u i) - F x)‖ ^ 2)
        ∂(Measure.pi fun _ : Fin b => p) ≤ ENNReal.ofReal (‖a‖ ^ 2 + t ^ 2 * (σ ^ 2 / b)) := by
  obtain ⟨h0, h1, h2, h3⟩ := batch_integrable hg x hb
  set N : (Fin b → Ω) → E := fun u => (1 / (b : ℝ)) • ∑ i, g x (u i) - F x
  have hexp : ∀ u, ‖a - t • N u‖ ^ 2 = ‖a‖ ^ 2 - 2 * t * ⟪a, N u⟫ + t ^ 2 * ‖N u‖ ^ 2 := by
    intro u
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  have hi1 : Integrable (fun u => 2 * t * ⟪a, N u⟫) (Measure.pi fun _ : Fin b => p) :=
    (h0.const_inner a).const_mul _
  have hi2 : Integrable (fun u => t ^ 2 * ‖N u‖ ^ 2) (Measure.pi fun _ : Fin b => p) :=
    h2.const_mul _
  have hi12 : Integrable (fun u => ‖a‖ ^ 2 - 2 * t * ⟪a, N u⟫) (Measure.pi fun _ : Fin b => p) :=
    (integrable_const _).sub hi1
  have hiall : Integrable (fun u => ‖a - t • N u‖ ^ 2) (Measure.pi fun _ : Fin b => p) := by
    simp_rw [hexp]; exact hi12.add hi2
  rw [← ofReal_integral_eq_lintegral_ofReal hiall (Filter.Eventually.of_forall fun _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [hexp]
  rw [integral_add hi12 hi2, integral_sub (integrable_const _) hi1,
    integral_const_mul, integral_inner h0, h1, inner_zero_right, integral_const_mul]
  simp only [integral_const, smul_eq_mul, mul_zero,
    sub_zero, probReal_univ]
  have := mul_le_mul_of_nonneg_left h3 (sq_nonneg t)
  linarith

end Batch

end OracleTemplate.StochasticCohypomonotone
