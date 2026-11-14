import LongTails.Setups.RipmGeneral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.RipmConditional

lemma conditional_kernel
    {Ω Ξ Z V : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (P : ProbabilityMeasure Ω) (nu : ProbabilityMeasure Ξ)
    (M : MeasurableSpace Ω) (hM : M ≤ mΩ) :
    letI : MeasurableSpace Ω := mΩ
    ∀ (xi : Ω → Ξ) (X : Ω → Z) (k : Z → Ξ → V)
    (_hxi : Measurable xi) (_hX : @Measurable Ω Z M _ X)
    (_hk : Measurable (Function.uncurry k))
    (_hfresh : Indep (MeasurableSpace.comap xi inferInstance) M P.toMeasure)
    (_hlaw : P.toMeasure.map xi = (nu : Measure Ξ))
    (_hjoint : Integrable (fun omega => k (X omega) (xi omega)) P.toMeasure)
    (_haverage : Integrable (fun omega => ∫ s, k (X omega) s ∂(nu : Measure Ξ))
      P.toMeasure),
    MeasureTheory.condExp M P.toMeasure (fun omega => k (X omega) (xi omega)) =ᵐ[P.toMeasure]
      (fun omega => ∫ s, k (X omega) s ∂(nu : Measure Ξ)) := by
  classical
  intro xi X k hxi hX hk hfresh hlaw hjoint haverage
  let : MeasurableSpace Ω := mΩ
  have hXm : @Measurable Ω Z mΩ _ X := hX.mono hM le_rfl
  have havg : StronglyMeasurable (fun z => ∫ s, k z s ∂nu.toMeasure) :=
    hk.stronglyMeasurable.integral_prod_right
  have hmap (s : Set Ω) (hs : MeasurableSet[M] s) :
      (P.toMeasure.restrict s).map (fun omega => (X omega, xi omega)) =
        ((P.toMeasure.restrict s).map X).prod nu.toMeasure := by
    symm
    apply Measure.prod_eq
    intro a b ha hb
    rw [Measure.map_apply (hXm.prodMk hxi) (ha.prod hb),
      Measure.map_apply hXm ha]
    change P.toMeasure.restrict s ((X ⁻¹' a) ∩ (xi ⁻¹' b)) =
      P.toMeasure.restrict s (X ⁻¹' a) * nu.toMeasure b
    rw [Measure.restrict_apply ((hXm ha).inter (hxi hb)),
      Measure.restrict_apply (hXm ha)]
    have hxiB : MeasurableSet[MeasurableSpace.comap xi inferInstance] (xi ⁻¹' b) :=
      ⟨b, hb, rfl⟩
    have hind := (Indep_iff _ _ _).mp hfresh (xi ⁻¹' b) ((X ⁻¹' a) ∩ s)
      hxiB ((hX ha).inter hs)
    have hbLaw : P.toMeasure (xi ⁻¹' b) = nu.toMeasure b := by
      rw [← hlaw, Measure.map_apply hxi hb]
    calc
      P.toMeasure (((X ⁻¹' a) ∩ (xi ⁻¹' b)) ∩ s) =
          P.toMeasure ((xi ⁻¹' b) ∩ ((X ⁻¹' a) ∩ s)) := by
        congr 1
        ext omega
        simp only [Set.mem_inter_iff]
        tauto
      _ = P.toMeasure (xi ⁻¹' b) * P.toMeasure ((X ⁻¹' a) ∩ s) := hind
      _ = _ := by rw [hbLaw, mul_comm]
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hM hjoint
  · intro s hs hfinite
    exact haverage.integrableOn
  · intro s hs hfinite
    have hkmap : Integrable (Function.uncurry k)
        ((P.toMeasure.restrict s).map (fun omega => (X omega, xi omega))) :=
      (integrable_map_measure hk.stronglyMeasurable.aestronglyMeasurable
        (hXm.prodMk hxi).aemeasurable).mpr hjoint.integrableOn
    rw [hmap s hs] at hkmap
    calc
      (∫ omega in s, (∫ z, k (X omega) z ∂nu.toMeasure) ∂P.toMeasure) =
          ∫ x, (∫ z, k x z ∂nu.toMeasure) ∂((P.toMeasure.restrict s).map X) :=
        (integral_map_of_stronglyMeasurable hXm havg).symm
      _ = ∫ x, Function.uncurry k x
          ∂(((P.toMeasure.restrict s).map X).prod nu.toMeasure) :=
        (integral_prod (Function.uncurry k) hkmap).symm
      _ = ∫ x, Function.uncurry k x
          ∂((P.toMeasure.restrict s).map (fun omega => (X omega, xi omega))) := by
        rw [hmap s hs]
      _ = ∫ omega in s, k (X omega) (xi omega) ∂P.toMeasure :=
        integral_map_of_stronglyMeasurable (hXm.prodMk hxi) hk.stronglyMeasurable
  · exact (havg.comp_measurable hX).aestronglyMeasurable


end LongTails.Proofs.RipmConditional
