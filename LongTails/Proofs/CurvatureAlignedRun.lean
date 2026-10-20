import LongTails.Proofs.CurvatureAlignedStep
import LongTails.Proofs.PLHessianConvergence

open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.CurvatureAligned

open OracleTemplate.PLHessian

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E} {Q : E → E →L[ℝ] E}
  {lower Lg Lξ σ : ℝ}

local notation "Pω" => Measure.infinitePi fun _ : ℕ => p

lemma Hyp.run_step (H : Hyp p f g Q lower Lg Lξ σ) (hg : Measurable (Function.uncurry g))
    {η : ℝ} (hη : 0 ≤ η) (hηL : η * Lg ≤ 1) (x0 : E) (n : ℕ)
    (hI : Integrable (fun ξ => f (sgdSeq g η x0 ξ n) - lower) Pω) :
    Integrable (fun ξ => f (sgdSeq g η x0 ξ (n + 1)) - lower) Pω ∧
      Integrable (fun ξ => ‖gradient f (sgdSeq g η x0 ξ n)‖ ^ 2) Pω ∧
      ∫ ξ, (f (sgdSeq g η x0 ξ (n + 1)) - lower) ∂Pω ≤
        ∫ ξ, (f (sgdSeq g η x0 ξ n) - lower) ∂Pω -
          η / 2 * ∫ ξ, ‖gradient f (sgdSeq g η x0 ξ n)‖ ^ 2 ∂Pω + η ^ 2 * Lξ * σ ^ 2 / 2 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  set S := fun ξ : ℕ → Ω => sgdSeq g η x0 ξ n with hSdef
  have hS : Measurable S := measurable_sgdSeq hg η x0 n
  have hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n → ξ i = ξ' i) → S ξ = S ξ' :=
    fun ξ ξ' h => sgdSeq_congr g η x0 n h
  have hgm : ∀ y, Measurable fun ω => g y ω := fun y =>
    hg.comp (measurable_const.prodMk measurable_id)
  have hstep := fun y => H.step η y (hgm y)
  have hfc := H.continuous
  have hgr : Measurable (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
  set c := η ^ 2 * Lξ * σ ^ 2 / 2 with hcdef
  set Φf : E → Ω → ℝ := fun y ω => f (y - η • g y ω) - lower with hΦfdef
  have hΦm : Measurable (Function.uncurry Φf) :=
    (hfc.measurable.comp (measurable_fst.sub (hg.const_smul η))).sub_const _
  have hnext : ∀ ξ, f (sgdSeq g η x0 ξ (n + 1)) - lower = Φf (S ξ) (ξ n) := fun ξ => rfl
  have hbound : ∀ y, ∫ ω, Φf y ω ∂p ≤
      (f y - lower) - η / 2 * ‖gradient f y‖ ^ 2 + c := by
    intro y
    obtain ⟨hi, hb⟩ := hstep y
    simp only [Φf]
    rw [integral_sub hi (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    have hg2 : 0 ≤ ‖gradient f y‖ ^ 2 := by positivity
    have : η / 2 * ‖gradient f y‖ ^ 2 ≤ η * (1 - η * Lg / 2) * ‖gradient f y‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hg2; nlinarith
    linarith
  have hnn : ∀ y ω, 0 ≤ Φf y ω := fun y ω => sub_nonneg.mpr (H.lower_le _)
  have hgsq : Integrable (fun ξ => ‖gradient f (S ξ)‖ ^ 2) Pω := by
    refine Integrable.mono' (hI.const_mul (2 * Lg))
      ((hgr.comp hS).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact H.grad_sq_le (S ξ)
  have inext : Integrable (fun ξ => f (sgdSeq g η x0 ξ (n + 1)) - lower) Pω := by
    refine NormalizedStorm.integrable_of_lintegral_le
      ((hfc.measurable.comp (measurable_sgdSeq hg η x0 (n + 1))).sub_const _)
      (fun ξ => sub_nonneg.mpr (H.lower_le _)) (hI.add (integrable_const c)) ?_
    simp_rw [hnext]
    have hh : Measurable fun z : E × Ω => ENNReal.ofReal (Φf z.1 z.2) :=
      ENNReal.measurable_ofReal.comp hΦm
    rw [HessianNcsc.fresh_lintegral p n S hS hdep (fun z => ENNReal.ofReal (Φf z.1 z.2)) hh]
    refine lintegral_mono fun ξ => ?_
    have hi : Integrable (Φf (S ξ)) p := (hstep (S ξ)).1.sub (integrable_const _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hnn (S ξ)))]
    refine ENNReal.ofReal_le_ofReal ((hbound (S ξ)).trans ?_)
    have : 0 ≤ η / 2 * ‖gradient f (S ξ)‖ ^ 2 := by positivity
    simp only [Pi.add_apply]
    linarith
  refine ⟨inext, hgsq, ?_⟩
  set Ψ : E → Ω → ℝ := fun y ω => Φf y ω -
    ((f y - lower) - η / 2 * ‖gradient f y‖ ^ 2 + c) with hΨdef
  have hΨm : Measurable (Function.uncurry Ψ) := by
    refine hΦm.sub ?_
    have hm1 : Measurable fun z : E × Ω => f z.1 - lower :=
      (hfc.measurable.comp measurable_fst).sub_const _
    have hm2 : Measurable fun z : E × Ω => ‖gradient f z.1‖ ^ 2 :=
      ((hgr.comp measurable_fst).norm.pow_const 2)
    exact (hm1.sub (hm2.const_mul _)).add_const _
  have ibd : Integrable (fun ξ => (f (S ξ) - lower) - η / 2 * ‖gradient f (S ξ)‖ ^ 2 + c) Pω :=
    (hI.sub (hgsq.const_mul _)).add (integrable_const _)
  have iΨ : Integrable (fun ξ => Ψ (S ξ) (ξ n)) Pω := inext.sub ibd
  have hΨeq := TwoSidedPL.integral_prefix_dep p n S hS hdep Ψ hΨm iΨ
  have hΨle : ∫ ξ, Ψ (S ξ) (ξ n) ∂Pω ≤ 0 := by
    rw [hΨeq]
    refine integral_nonpos fun ξ => ?_
    show ∫ ω, Ψ (S ξ) ω ∂p ≤ 0
    have hi : Integrable (Φf (S ξ)) p := (hstep (S ξ)).1.sub (integrable_const _)
    simp only [Ψ]
    rw [integral_sub hi (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    linarith [hbound (S ξ)]
  have hsplit : ∫ ξ, Ψ (S ξ) (ξ n) ∂Pω =
      ∫ ξ, (f (sgdSeq g η x0 ξ (n + 1)) - lower) ∂Pω -
        (∫ ξ, (f (S ξ) - lower) ∂Pω - η / 2 * ∫ ξ, ‖gradient f (S ξ)‖ ^ 2 ∂Pω + c) := by
    have inext' : Integrable (fun ξ => Φf (S ξ) (ξ n)) Pω := inext
    have hI' : Integrable (fun ξ => f (S ξ) - lower) Pω := hI
    have i2 : Integrable (fun ξ => η / 2 * ‖gradient f (S ξ)‖ ^ 2) Pω := hgsq.const_mul _
    have i12 : Integrable (fun ξ => f (S ξ) - lower - η / 2 * ‖gradient f (S ξ)‖ ^ 2) Pω :=
      hI'.sub i2
    simp only [Ψ, hnext]
    rw [integral_sub inext' ibd, integral_add i12 (integrable_const _),
      integral_sub hI' i2, integral_const_mul, integral_const]
    simp
  rw [hsplit] at hΨle
  linarith

end OracleTemplate.CurvatureAligned
