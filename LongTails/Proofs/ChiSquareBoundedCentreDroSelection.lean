import LongTails.Proofs.ChiSquareSelection
import LongTails.Proofs.ChiSquareDuality

open MeasureTheory ProbabilityTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open ChiSquareDro

variable {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]

lemma square_variance_width {X : Ω → ℝ} (hm : Measurable X) {a b : ℝ} (ha : 0 ≤ a)
    (hx : ∀ ω, X ω ∈ Icc a b) :
    variance (fun ω => X ω ^ 2) p ≤ (b-a)^2 * ∫ ω, X ω ^ 2 ∂p := by
  have hi : Integrable (fun ω => X ω ^ 2) p :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (b^2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (ha.trans (hx ω).1) (hx ω).2 2)
  rw [← variance_sub_const (hm.pow_const 2).aestronglyMeasurable (a*b)]
  refine (variance_le_expectation_sq ((hm.pow_const 2).sub_const _).aestronglyMeasurable).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (hi.const_mul _) (ae_of_all _ fun ω => ?_)
  have ⟨h1,h2⟩ := hx ω
  have h3 : |X ω ^ 2-a*b| ≤ (b-a)*X ω := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ X ω+b by linarith)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ X ω+a by linarith)]
  simpa [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) h3 2

lemma rms_width {X : Ω → ℝ} (hm : Measurable X) {a b : ℝ} (ha : 0 ≤ a)
    (hx : ∀ ω, X ω ∈ Icc a b) {m : ℕ} (hmpos : 0 < m) :
    let M := fun ξ : Fin m → Ω => (m:ℝ)⁻¹ * ∑ i, X (ξ i) ^ 2
    let S := ∫ ω, X ω ^ 2 ∂p
    (∫ ξ, (Real.sqrt (M ξ) - Real.sqrt S)^2 ∂Measure.pi (fun _ : Fin m => p)) ≤ (b-a)^2/m := by
  intro M S
  let ν := Measure.pi (fun _ : Fin m => p)
  have hS : 0 ≤ S := integral_nonneg fun ω => sq_nonneg _
  have hM (ξ) : 0 ≤ M ξ := by dsimp [M]; positivity
  have hmb : (m:ℝ) ≠ 0 := by positivity
  have hX0 := fun ω => ha.trans (hx ω).1
  have hXb := fun ω => (hx ω).2
  obtain ⟨hi,hE⟩ := mean_integral p hm hX0 hXb hmpos
  change Integrable M ν at hi
  change (∫ ξ, M ξ ∂ν) = S at hE
  have hY : MemLp (fun ω => X ω ^ 2) 2 p :=
    MemLp.of_bound (hm.pow_const 2).aestronglyMeasurable (b^2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hX0 ω) (hx ω).2 2)
  have hv : variance M ν = variance (fun ω => X ω ^ 2) p / m := by
    dsimp [M]; rw [variance_const_mul]
    have h := variance_sum_pi (μ := fun _ : Fin m => p) (X := fun _ ω => X ω ^ 2) (fun _ => hY)
    have HE : (∑ i : Fin m, fun ξ : Fin m → Ω => X (ξ i)^2) = (fun ξ => ∑ i, X (ξ i)^2) := by ext; simp
    rw [HE] at h
    change variance (fun ξ : Fin m → Ω => ∑ i, X (ξ i)^2) ν = _ at h
    rw [h]; simp [nsmul_eq_mul]; field_simp
  by_cases hzero : S = 0
  · simp only [hzero, Real.sqrt_zero, sub_zero, Real.sq_sqrt (hM _)]
    change (∫ ξ, M ξ ∂ν) ≤ _
    rw [hE,hzero]; positivity
  · have hs := lt_of_le_of_ne hS (Ne.symm hzero)
    have hsq (ξ) : (Real.sqrt (M ξ)-Real.sqrt S)^2 ≤ (M ξ-S)^2/S := by
      rw [le_div_iff₀ hs]
      have hfac : M ξ-S = (Real.sqrt (M ξ)-Real.sqrt S)*(Real.sqrt (M ξ)+Real.sqrt S) := by
        nlinarith [Real.sq_sqrt (hM ξ), Real.sq_sqrt hS]
      rw [hfac, mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg (M ξ), Real.sqrt_nonneg S,
        mul_nonneg (Real.sqrt_nonneg (M ξ)) (Real.sqrt_nonneg S)]
    have hI := (mean_sq_dev p hm hX0 hXb hmpos).1
    change Integrable (fun ξ => (M ξ-S)^2) ν at hI
    have hle := integral_mono_of_nonneg (μ := ν) (ae_of_all _ fun ξ => sq_nonneg (Real.sqrt (M ξ)-Real.sqrt S))
      (hI.div_const S) (ae_of_all _ hsq)
    refine hle.trans ?_
    rw [integral_div, le_div_iff₀ (by positivity : (0:ℝ)<m)]
    rw [variance_eq_integral hi.aemeasurable, hE] at hv
    have hw := square_variance_width p hm ha hx
    change variance (fun ω => X ω ^ 2) p ≤ (b-a)^2*S at hw
    rw [hv]
    calc _ = variance (fun ω => X ω ^ 2) p / S := by field_simp
      _ ≤ _ := (div_le_iff₀ hs).mpr hw

end OracleTemplate.ChiSquareBoundedCentreDro
