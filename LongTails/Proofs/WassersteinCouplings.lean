import LongTails.Setups.WassersteinSmoothComposite
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory
open LongTails.Setups.WassersteinSmoothComposite

namespace LongTails.Proofs.WassersteinCouplings

lemma couplingCost_nonnegative {d : ℕ} {μ ν : Distribution d} (π : Coupling μ ν) :
    0 ≤ couplingCost π :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma squaredDistance_nonnegative {d : ℕ} (μ ν : Distribution d) :
    0 ≤ squaredDistance μ ν := by
  apply Real.sInf_nonneg
  rintro _ ⟨π, rfl⟩
  exact couplingCost_nonnegative π

lemma squaredDistance_le_cost {d : ℕ} {μ ν : Distribution d} (π : Coupling μ ν) :
    squaredDistance μ ν ≤ couplingCost π := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨ρ, rfl⟩
    exact couplingCost_nonnegative ρ
  · exact ⟨π, rfl⟩

noncomputable def independentCoupling {d : ℕ} (μ ν : Distribution d) : Coupling μ ν where
  law := ⟨(μ.law : Measure (Space d)).prod (ν.law : Measure (Space d)), inferInstance⟩
  first := by simp
  second := by simp
  finiteCost := by
    have hbound := ((μ.secondMoment.comp_fst (ν.law : Measure (Space d))).add
      (ν.secondMoment.comp_snd (μ.law : Measure (Space d)))).const_mul 2
    apply hbound.mono'
    · fun_prop
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change ‖z.1 - z.2‖ ^ 2 ≤ 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
      have hn := norm_sub_le z.1 z.2
      have hnn := norm_nonneg (z.1 - z.2)
      nlinarith [sq_nonneg (‖z.1‖ - ‖z.2‖), norm_nonneg z.1, norm_nonneg z.2]

lemma coupling_exists {d : ℕ} (μ ν : Distribution d) : Nonempty (Coupling μ ν) :=
  ⟨independentCoupling μ ν⟩

noncomputable def graphCoupling {d : ℕ} {μ ν : Distribution d}
    (T : Space d → Space d) (hT : Measurable T)
    (hpush : (μ.law : Measure (Space d)).map T = ν.law)
    (hcost : Integrable (fun x => ‖x - T x‖ ^ 2) (μ.law : Measure (Space d))) :
    Coupling μ ν where
  law := μ.law.map (fun x => (x, T x))
  first := by
    change ((μ.law : Measure (Space d)).map (fun x => (x, T x))).map Prod.fst = _
    have hm : Measurable (fun x : Space d => (x, T x)) := measurable_id.prodMk hT
    rw [Measure.map_map measurable_fst hm]
    simp [Function.comp_def]
  second := by
    change ((μ.law : Measure (Space d)).map (fun x => (x, T x))).map Prod.snd = _
    have hm : Measurable (fun x : Space d => (x, T x)) := measurable_id.prodMk hT
    rw [Measure.map_map measurable_snd hm]
    simpa [Function.comp_def] using hpush
  finiteCost := by
    change Integrable (fun z : Space d × Space d => ‖z.1 - z.2‖ ^ 2)
      ((μ.law : Measure (Space d)).map (fun x => (x, T x)))
    exact (integrable_map_measure (by fun_prop)
      (measurable_id.prodMk hT).aemeasurable).mpr hcost

lemma graphCoupling_cost {d : ℕ} {μ ν : Distribution d}
    (T : Space d → Space d) (hT : Measurable T)
    (hpush : (μ.law : Measure (Space d)).map T = ν.law)
    (hcost : Integrable (fun x => ‖x - T x‖ ^ 2) (μ.law : Measure (Space d))) :
    couplingCost (graphCoupling T hT hpush hcost) =
      ∫ x, ‖x - T x‖ ^ 2 ∂(μ.law : Measure (Space d)) := by
  exact integral_map (measurable_id.prodMk hT).aemeasurable (by fun_prop)

lemma squaredDistance_eq_optimal_cost {d : ℕ} {μ ν : Distribution d}
    (π : Coupling μ ν) (hopt : ∀ ρ : Coupling μ ν, couplingCost π ≤ couplingCost ρ) :
    squaredDistance μ ν = couplingCost π := by
  apply le_antisymm (squaredDistance_le_cost π)
  apply le_csInf
  · exact ⟨couplingCost π, π, rfl⟩
  · rintro _ ⟨ρ, rfl⟩
    exact hopt ρ

lemma squaredDistance_eq_map_cost {d : ℕ} {μ ν : Distribution d}
    (T : Space d → Space d) (hT : Measurable T)
    (hpush : (μ.law : Measure (Space d)).map T = ν.law)
    (hcost : Integrable (fun x => ‖x - T x‖ ^ 2) (μ.law : Measure (Space d)))
    (hopt : ∀ π : Coupling μ ν,
      (∫ x, ‖x - T x‖ ^ 2 ∂(μ.law : Measure (Space d))) ≤ couplingCost π) :
    squaredDistance μ ν = ∫ x, ‖x - T x‖ ^ 2 ∂(μ.law : Measure (Space d)) := by
  rw [squaredDistance_eq_optimal_cost (graphCoupling T hT hpush hcost)]
  · exact graphCoupling_cost T hT hpush hcost
  · intro ρ
    rw [graphCoupling_cost]
    exact hopt ρ

lemma integrable_sq_sub_of_maps {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ ν : Distribution d) (f g : Ω → Space d)
    (hf : Measurable f) (hg : Measurable g)
    (hfm : P.map f = μ.law) (hgm : P.map g = ν.law) :
    Integrable (fun ω => ‖f ω - g ω‖ ^ 2) P := by
  have hi : Integrable (fun ω => ‖f ω‖ ^ 2) P := by
    have hm : Integrable (fun x : Space d => ‖x‖ ^ 2) (P.map f) := by
      rw [hfm]
      exact μ.secondMoment
    exact (integrable_map_measure (by fun_prop) hf.aemeasurable).mp hm
  have hj : Integrable (fun ω => ‖g ω‖ ^ 2) P := by
    have hm : Integrable (fun x : Space d => ‖x‖ ^ 2) (P.map g) := by
      rw [hgm]
      exact ν.secondMoment
    exact (integrable_map_measure (by fun_prop) hg.aemeasurable).mp hm
  apply ((hi.add hj).const_mul 2).mono'
  · fun_prop
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖f ω - g ω‖ ^ 2 ≤ 2 * (‖f ω‖ ^ 2 + ‖g ω‖ ^ 2)
    have hn := norm_sub_le (f ω) (g ω)
    nlinarith [sq_nonneg (‖f ω‖ - ‖g ω‖), norm_nonneg (f ω),
      norm_nonneg (g ω), norm_nonneg (f ω - g ω)]

noncomputable def couplingOfMaps {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (μ ν : Distribution d) (f g : Ω → Space d)
    (hf : Measurable f) (hg : Measurable g)
    (hfm : (P : Measure Ω).map f = μ.law) (hgm : (P : Measure Ω).map g = ν.law) :
    Coupling μ ν where
  law := P.map (fun ω => (f ω, g ω))
  first := by
    change ((P : Measure Ω).map (fun ω => (f ω, g ω))).map Prod.fst = _
    rw [Measure.map_map measurable_fst (hf.prodMk hg)]
    simpa [Function.comp_def] using hfm
  second := by
    change ((P : Measure Ω).map (fun ω => (f ω, g ω))).map Prod.snd = _
    rw [Measure.map_map measurable_snd (hf.prodMk hg)]
    simpa [Function.comp_def] using hgm
  finiteCost := by
    change Integrable (fun z : Space d × Space d => ‖z.1 - z.2‖ ^ 2)
      ((P : Measure Ω).map (fun ω => (f ω, g ω)))
    exact (integrable_map_measure (by fun_prop) (hf.prodMk hg).aemeasurable).mpr
      (by simpa only [Function.comp_def] using
        integrable_sq_sub_of_maps (P : Measure Ω) μ ν f g hf hg hfm hgm)

lemma couplingOfMaps_cost {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (μ ν : Distribution d) (f g : Ω → Space d)
    (hf : Measurable f) (hg : Measurable g)
    (hfm : (P : Measure Ω).map f = μ.law) (hgm : (P : Measure Ω).map g = ν.law) :
    couplingCost (couplingOfMaps P μ ν f g hf hg hfm hgm) =
      ∫ ω, ‖f ω - g ω‖ ^ 2 ∂(P : Measure Ω) := by
  exact integral_map (hf.prodMk hg).aemeasurable (by fun_prop)

lemma squaredDistance_le_joint_cost {d : ℕ} {base μ ν : Distribution d}
    (π : JointPlan base μ ν) :
    squaredDistance μ ν ≤ ∫ z, ‖z.2.1 - z.2.2‖ ^ 2 ∂(π.law : Measure (Space d × Space d × Space d)) := by
  have hc := squaredDistance_le_cost (couplingOfMaps π.law μ ν
    (fun z => z.2.1) (fun z => z.2.2) (by fun_prop) (by fun_prop)
    π.firstMarginal π.secondMarginal)
  rwa [couplingOfMaps_cost] at hc

lemma inverse_pushforward {d : ℕ} (μ ν : Distribution d)
    (A B : Space d → Space d) (hA : Measurable A) (hB : Measurable B)
    (hleft : Function.LeftInverse B A)
    (hpush : (μ.law : Measure (Space d)).map A = ν.law) :
    (ν.law : Measure (Space d)).map B = μ.law := by
  rw [← hpush, Measure.map_map hB hA]
  have he : B ∘ A = id := funext hleft
  rw [he, Measure.map_id]

noncomputable def pullbackFirst {d : ℕ} {μ ν ρ : Distribution d}
    (π : Coupling ν ρ) (A B : Space d → Space d)
    (hA : Measurable A) (hB : Measurable B)
    (hleft : Function.LeftInverse B A)
    (hpush : (μ.law : Measure (Space d)).map A = ν.law) : Coupling μ ρ :=
  couplingOfMaps π.law μ ρ (fun z => B z.1) Prod.snd
    (hB.comp measurable_fst) measurable_snd
    (by
      change (π.law : Measure (Space d × Space d)).map (B ∘ Prod.fst) = _
      rw [← Measure.map_map hB measurable_fst, π.first]
      exact inverse_pushforward μ ν A B hA hB hleft hpush)
    π.second

noncomputable def reverseCoupling {d : ℕ} {μ ν : Distribution d}
    (π : Coupling μ ν) : Coupling ν μ :=
  couplingOfMaps π.law ν μ Prod.snd Prod.fst measurable_snd measurable_fst
    π.second π.first

lemma reverseCoupling_cost {d : ℕ} {μ ν : Distribution d} (π : Coupling μ ν) :
    couplingCost (reverseCoupling π) = couplingCost π := by
  rw [reverseCoupling, couplingOfMaps_cost]
  simp only [couplingCost, norm_sub_rev]

lemma squaredDistance_reverse_le {d : ℕ} (μ ν : Distribution d) :
    squaredDistance μ ν ≤ squaredDistance ν μ := by
  apply le_csInf
  · obtain ⟨π⟩ := coupling_exists ν μ
    exact ⟨couplingCost π, π, rfl⟩
  · rintro _ ⟨π, rfl⟩
    have hc := squaredDistance_le_cost (reverseCoupling π)
    rwa [reverseCoupling_cost] at hc

lemma squaredDistance_symm {d : ℕ} (μ ν : Distribution d) :
    squaredDistance μ ν = squaredDistance ν μ :=
  le_antisymm (squaredDistance_reverse_le μ ν) (squaredDistance_reverse_le ν μ)

lemma integrable_sq_of_linear_growth {d : ℕ} (μ : Distribution d)
    (f : Space d → Space d) (hf : Measurable f) (a b : ℝ)
    (hbound : ∀ x, ‖f x‖ ≤ a + b * ‖x‖) :
    Integrable (fun x => ‖f x‖ ^ 2) (μ.law : Measure (Space d)) := by
  have hi : Integrable (fun x : Space d => 2 * a ^ 2 + 2 * b ^ 2 * ‖x‖ ^ 2)
      (μ.law : Measure (Space d)) :=
    (integrable_const (2 * a ^ 2)).add (μ.secondMoment.const_mul (2 * b ^ 2))
  apply hi.mono'
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn := hbound x
    have hs : ‖f x‖ ^ 2 ≤ (a + b * ‖x‖) ^ 2 := by
      nlinarith [norm_nonneg (f x), norm_nonneg x]
    nlinarith [sq_nonneg (a - b * ‖x‖)]

lemma integral_of_marginal {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Distribution d) (f : Ω → Space d) (hf : Measurable f)
    (hfm : P.map f = μ.law) (V : Space d → ℝ) (hV : Measurable V) :
    (∫ ω, V (f ω) ∂P) = ∫ x, V x ∂(μ.law : Measure (Space d)) := by
  rw [← hfm]
  exact (integral_map hf.aemeasurable hV.aestronglyMeasurable).symm

lemma integrable_of_marginal {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Distribution d) (f : Ω → Space d) (hf : Measurable f)
    (hfm : P.map f = μ.law) (V : Space d → ℝ)
    (hV : Integrable V (μ.law : Measure (Space d))) : Integrable (V ∘ f) P := by
  have hm : Integrable V (P.map f) := by rwa [hfm]
  exact hm.comp_measurable hf

lemma pullbackFirst_forward_cost {d : ℕ} {μ ν ρ : Distribution d}
    (π : Coupling ν ρ) (A B : Space d → Space d)
    (hA : Measurable A) (hB : Measurable B)
    (hleft : Function.LeftInverse B A) (hright : Function.RightInverse B A)
    (hpush : (μ.law : Measure (Space d)).map A = ν.law) :
    (∫ z, ‖A z.1 - z.2‖ ^ 2
      ∂((pullbackFirst π A B hA hB hleft hpush).law : Measure (Space d × Space d))) =
      couplingCost π := by
  change (∫ z, ‖A z.1 - z.2‖ ^ 2
    ∂((π.law : Measure (Space d × Space d)).map (fun z => (B z.1, z.2)))) = _
  have hpair : Measurable (fun z : Space d × Space d => (B z.1, z.2)) :=
    (hB.comp measurable_fst).prodMk measurable_snd
  rw [integral_map hpair.aemeasurable (by fun_prop)]
  change ∀ x, A (B x) = x at hright
  simp only [hright, couplingCost]

noncomputable def optimalMapCoupling {d : ℕ} {μ ν : Distribution d}
    (T : OptimalTransport μ ν) : Coupling μ ν :=
  graphCoupling T.toFun T.measurable T.pushforward T.finiteCost

lemma optimalMapCoupling_cost {d : ℕ} {μ ν : Distribution d}
    (T : OptimalTransport μ ν) : couplingCost (optimalMapCoupling T) =
      squaredDistance μ ν := by
  rw [optimalMapCoupling, graphCoupling_cost]
  exact (squaredDistance_eq_map_cost T.toFun T.measurable T.pushforward
    T.finiteCost T.optimal).symm

end LongTails.Proofs.WassersteinCouplings
