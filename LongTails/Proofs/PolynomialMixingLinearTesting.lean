import LongTails.Proofs.PolynomialMixingBurstTesting
import LongTails.TemplateLowerBound
import Mathlib.Analysis.Convex.Function

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PolynomialMixingLinearTesting

open LongTails.Setups.PolynomialMixingSubgradient
open LongTails.Proofs.PolynomialMixingLowerBound
open LongTails.Proofs.PolynomialMixingBurst

variable {q : Params}

noncomputable def gated (A : Set ℝ) (v : Space q) (_ : ↥(Domain q)) : ℝ → Space q :=
  A.indicator (fun _ => v)

noncomputable def linear (u : Space q) (x : Space q) := ⟪u, x⟫

lemma linear_admissible {P : ProbabilityMeasure Path} (hreg : AbsolutelyRegular P q.τ q.β)
    (A : Set ℝ) (hA : MeasurableSet A) (v : Space q)
    (hp : 0 < q.p)
    (hmoment : ((P : Measure Path).map (fun z => z 0)).real A * ‖v‖ ^ q.p ≤ q.G ^ q.p) :
    let π := (P : Measure Path).map (fun z => z 0)
    spec.admissible q (linear (π.real A • v)) (sampledOracle (gated A v) P) := by
  let π := (P : Measure Path).map (fun z => z 0)
  let : IsProbabilityMeasure π := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply 0).aemeasurable).mpr inferInstance
  let u := π.real A • v
  have hlin : Continuous (linear u) := (innerSL ℝ u).continuous
  have hne : (Domain q).Nonempty := ⟨0, by simpa only [Domain, Metric.mem_closedBall, dist_self] using q.hR⟩
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : Space q) q.R).exists_isMinOn hne hlin.continuousOn
  refine ⟨gated A v, P, rfl, hreg, (innerSL ℝ u).toLinearMap.convexOn (convex_closedBall _ _),
    ⟨x, hx, hmin⟩, ?_⟩
  have hm : Measurable (A.indicator (fun _ : ℝ => v)) := measurable_const.indicator hA
  have hpEq : (fun z : ℝ => ‖A.indicator (fun _ : ℝ => v) z‖ ^ q.p) =
      A.indicator (fun _ : ℝ => ‖v‖ ^ q.p) := by
    funext z
    by_cases hz : z ∈ A <;> simp [hz, Real.zero_rpow hp.ne']
  constructor
  · exact hm.comp measurable_snd
  · intro x
    exact (integrable_const v).indicator hA
  · intro x
    simp only [gated, hpEq]
    exact (integrable_const _).indicator hA
  · intro x
    change (∫ z, ‖A.indicator (fun _ : ℝ => v) z‖ ^ q.p ∂π) ≤ _
    rw [hpEq, integral_indicator_const _ hA, smul_eq_mul]
    exact hmoment
  · intro x y
    change ⟪u, x.val⟫ + ⟪∫ z, A.indicator (fun _ : ℝ => v) z ∂π, y.val - x.val⟫ ≤ ⟪u, y.val⟫
    rw [integral_indicator_const _ hA]
    change ⟪u, x.val⟫ + ⟪u, y.val - x.val⟫ ≤ ⟪u, y.val⟫
    rw [inner_sub_right]
    linarith

lemma linear_obstruction (P : ProbabilityMeasure Path) (A : Set ℝ)
    (b : ℝ) (hb : b ∉ A) (v : Space q) (hv : ‖v‖ = 1) (s : ℝ)
    (hsep : q.ε < q.R * (((P : Measure Path).map (fun z => z 0)).real A * s))
    (alg : OracleTemplate.Algorithm (↥(Domain q)) (Space q) (↥(Domain q))) (N : ℕ)
    (hprob : 2 * q.δ < (P : Measure Path).real (commonPrefix b N)) :
    let π := (P : Measure Path).map (fun z => z 0)
    let test := fun w : Space q => spec.successful q (linear (π.real A • w))
      (fun z : alg.Seed × Path =>
        OracleTemplate.execute (sampledOracle (gated A w) P) alg (fun _ => N) z.1 z.2)
      ⟨(alg.law : Measure alg.Seed).prod (P : Measure Path), inferInstance⟩
    ¬(test (s • v) ∧ test (-(s • v))) := by
  let π := (P : Measure Path).map (fun z => z 0)
  let u := π.real A • (s • v)
  let μ := (alg.law : Measure alg.Seed).prod (P : Measure Path)
  let out := fun w : Space q => fun z : alg.Seed × Path =>
    OracleTemplate.execute (sampledOracle (gated A w) P) alg (fun _ => N) z.1 z.2
  dsimp only
  rintro ⟨⟨hm₁, x₁, _, hmin₁, hs₁⟩, ⟨hm₂, x₂, _, hmin₂, hs₂⟩⟩
  have hnorm : ‖q.R • v‖ = q.R := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg q.hR, hv, mul_one]
  have hx : q.R • v ∈ Domain q := by simpa only [Domain, Metric.mem_closedBall, dist_zero_right, hnorm] using (le_refl q.R)
  have hxn : -(q.R • v) ∈ Domain q := by simpa only [Domain, Metric.mem_closedBall, dist_zero_right, norm_neg, hnorm] using (le_refl q.R)
  let B := {x : ↥(Domain q) | linear u x.val - linear u x₁ ≤ q.ε}
  let C := {x : ↥(Domain q) | linear (π.real A • -(s • v)) x.val - linear (π.real A • -(s • v)) x₂ ≤ q.ε}
  have hdis : Disjoint B C := by
    apply Set.disjoint_left.mpr
    intro x hx₁ hx₂
    have h₁ := hmin₁ hxn
    have h₂ := hmin₂ hx
    change linear u x₁ ≤ linear u (-(q.R • v)) at h₁
    change linear (π.real A • -(s • v)) x₂ ≤ linear (π.real A • -(s • v)) (q.R • v) at h₂
    change linear u x.val - linear u x₁ ≤ q.ε at hx₁
    change linear (π.real A • -(s • v)) x.val - linear (π.real A • -(s • v)) x₂ ≤ q.ε at hx₂
    simp only [linear, u, smul_neg, inner_neg_left, inner_neg_right,
      real_inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, one_pow, mul_one] at h₁ h₂ hx₁ hx₂
    change q.ε < q.R * (π.real A * s) at hsep
    linarith
  have hmb : MeasurableSet B := measurableSet_le
    (((innerSL ℝ u).continuous.measurable.comp measurable_subtype_coe).sub_const _) measurable_const
  have hmc : MeasurableSet C := measurableSet_le
    (((innerSL ℝ _).continuous.measurable.comp measurable_subtype_coe).sub_const _) measurable_const
  apply common_failure μ (Set.univ ×ˢ commonPrefix b N) (out (s • v)) (out (-(s • v))) B C
    (hm₁ hmb) (hm₂ hmc) hdis _ _ ⟨hs₁, hs₂⟩
  · intro w hw
    exact execute_commonPrefix _ _ P P b (fun _ => by simp [gated, hb]) alg w.1 w.2 N hw.2
  · simpa [μ, measureReal_prod_prod] using hprob

end LongTails.Proofs.PolynomialMixingLinearTesting
