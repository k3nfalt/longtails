import LongTails.Proofs.HeavyTailedMarkovLaw
import LongTails.Proofs.HeavyTailedError

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.HeavyTailedMarkovGradient

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

variable {E H : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace H] [MeasurableSpace Ω]

lemma averaged_heavyError_bound (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) {ρ : Measure H} [IsProbabilityMeasure ρ]
    {z : H → Ω} (hz : Measurable z) (hmap : ρ.map z = (π : Measure Ω))
    (t : ℕ) (hd : Integrable (mixingDistance κ π t) (π : Measure Ω))
    {G : H → Ω → E} {u v : H → E}
    (hG : Measurable (Function.uncurry G)) (hu : Measurable u) (hv : Measurable v)
    (hGi : ∀ h, Integrable (G h) (π : Measure Ω))
    (hmean : ∀ h, ∫ y, G h y ∂(π : Measure Ω) = u h)
    {a D R C p σ δ : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (hR : 0 ≤ R)
    (hC : 0 < C) (hp : 1 ≤ p)
    (hun : ∀ h, ‖u h‖ ≤ C / 2) (hvn : ∀ h, ‖v h‖ ≤ 2 * R)
    (hmi : ∀ h, Integrable (fun y => ‖G h y - u h‖ ^ p) (π : Measure Ω))
    (hm : ∀ h, (∫ y, ‖G h y - u h‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (hmix : (∫ y, mixingDistance κ π t y ∂(π : Measure Ω)) ≤ δ) :
    (∫ h, ∫ y, heavyError a D R p (v h) (u h - clip C (G h y))
      ∂(κ ^ t) (z h) ∂ρ) ≤
      2 * R * a * (σ ^ p / (C / 2) ^ (p - 1)) +
      (a ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) * σ ^ p +
      12 * R * a * C * δ := by
  let W : H → Ω → ℝ := fun h y => heavyError a D R p (v h) (u h - clip C (G h y))
  have hW : Measurable (Function.uncurry W) :=
    (measurable_heavyError a D R p).comp ((hv.comp measurable_fst).prodMk
      ((hu.comp measurable_fst).sub ((measurable_clip C).comp hG)))
  have hbound : ∀ h y, |W h y| ≤ 6 * R * a * C := by
    intro h y
    have he : ‖u h - clip C (G h y)‖ ≤ 3 * C / 2 :=
      (norm_sub_le _ _).trans (by have hh := norm_clip_le hC.le (G h y); have hh' := hun h; linarith)
    exact (heavyError_bound ha hD hR (hvn h) he).trans (by ring_nf; rfl)
  have hmix' := averaged_mixing_bound κ π hz hmap t hd hW
    (by positivity : 0 ≤ 6 * R * a * C) hbound hmix
  have hstat : ∀ h, (∫ y, W h y ∂(π : Measure Ω)) ≤
      2 * R * a * (σ ^ p / (C / 2) ^ (p - 1)) +
      (a ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) * σ ^ p := fun h =>
    integral_heavyError_bound (hG.comp (measurable_const.prodMk measurable_id))
      (hGi h) (hmean h) ha hD hR hC hp (hun h) (hvn h) (hmi h) (hm h)
  have hi : Integrable (fun h => ∫ y, W h y ∂(π : Measure Ω)) ρ :=
    Integrable.of_bound
      (hW.stronglyMeasurable.integral_kernel_prod_right (κ := Kernel.const H (π : Measure Ω))).aestronglyMeasurable
      (6 * R * a * C) (Filter.Eventually.of_forall (fun h => by
        simpa using norm_integral_le_of_norm_le_const (μ := (π : Measure Ω))
          (f := W h) (Filter.Eventually.of_forall (hbound h))))
  have hh := integral_mono hi (integrable_const
    (2 * R * a * (σ ^ p / (C / 2) ^ (p - 1)) +
      (a ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) * σ ^ p)) hstat
  simp only [integral_const, probReal_univ, one_smul] at hh
  have hdiff := (le_abs_self _).trans hmix'
  change (∫ h, ∫ y, W h y ∂(κ ^ t) (z h) ∂ρ) ≤ _
  linarith

end OracleTemplate.HeavyTailedMarkovGradient
