import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.ChiSquareDro

variable {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]

lemma integrable_of_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν) {g : β → ℝ}
    (hg : Integrable g ν) : Integrable (fun x => g (f x)) μ :=
  (hf.integrable_comp hg.aestronglyMeasurable).mpr hg

lemma abs_le_amgm {x a : ℝ} (ha : 0 < a) : |x| ≤ x ^ 2 / (2 * a) + a / 2 := by
  rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (|x| - a), sq_abs x, abs_nonneg x]

lemma sqrt_le_amgm {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) : Real.sqrt x ≤ x / (2 * a) + a / 2 := by
  have h := abs_le_amgm (x := Real.sqrt x) ha
  rwa [abs_of_nonneg (Real.sqrt_nonneg x), Real.sq_sqrt hx] at h

lemma mean_sq_dev {X : Ω → ℝ} (hX : Measurable X) {b : ℝ} (hX0 : ∀ ω, 0 ≤ X ω)
    (hXb : ∀ ω, X ω ≤ b) {m : ℕ} (hm : 0 < m) :
    Integrable (fun ξ : Fin m → Ω => ((m : ℝ)⁻¹ * ∑ i : Fin m, X (ξ i) ^ 2 - ∫ ω, X ω ^ 2 ∂p) ^ 2)
      (Measure.pi fun _ => p) ∧
    (∫ ξ : Fin m → Ω, ((m : ℝ)⁻¹ * ∑ i : Fin m, X (ξ i) ^ 2 - ∫ ω, X ω ^ 2 ∂p) ^ 2
      ∂(Measure.pi fun _ => p)) ≤ b ^ 2 * (∫ ω, X ω ^ 2 ∂p) / m := by
  let Q : Measure (Fin m → Ω) := Measure.pi fun _ => p
  let Y : Ω → ℝ := fun ω => X ω ^ 2
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  have hb0 : 0 ≤ b := le_trans (hX0 ω0) (hXb ω0)
  have hYm : Measurable Y := hX.pow_const 2
  have hYb : ∀ ω, ‖Y ω‖ ≤ b ^ 2 := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hX0 ω) (hXb ω) 2
  have hY : MemLp Y 2 p := MemLp.of_bound hYm.aestronglyMeasurable (b ^ 2) (ae_of_all _ hYb)
  have hcoord (i : Fin m) : MemLp (fun ξ : Fin m → Ω => Y (ξ i)) 2 Q :=
    hY.comp_measurePreserving (measurePreserving_eval _ i)
  have hsum : MemLp (fun ξ : Fin m → Ω => ∑ i : Fin m, Y (ξ i)) 2 Q :=
    memLp_finsetSum _ (fun i _ => hcoord i)
  have havg := hsum.const_mul (m : ℝ)⁻¹
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hint : (∫ ξ, (m : ℝ)⁻¹ * ∑ i : Fin m, Y (ξ i) ∂Q) = ∫ ω, Y ω ∂p := by
    rw [integral_const_mul, integral_finsetSum]
    · have hi (i : Fin m) : (∫ ξ, Y (ξ i) ∂Q) = ∫ ω, Y ω ∂p := by
        have hp := measurePreserving_eval (fun _ : Fin m => p) i
        have he := integral_map hp.measurable.aemeasurable
          (show AEStronglyMeasurable Y (Q.map (fun ξ => ξ i)) from by
            rw [hp.map_eq]; exact hY.aestronglyMeasurable)
        rw [hp.map_eq] at he
        exact he.symm
      simp_rw [hi]
      simp [hm']
    · exact fun i _ => (hcoord i).integrable (by norm_num)
  have hv : variance (fun ξ : Fin m → Ω => (m : ℝ)⁻¹ * ∑ i : Fin m, Y (ξ i)) Q =
      variance Y p / m := by
    rw [variance_const_mul]
    have he := variance_sum_pi (μ := fun _ : Fin m => p) (X := fun _ => Y) (fun _ => hY)
    have hf : (∑ i : Fin m, fun ξ : Fin m → Ω => Y (ξ i)) = (fun ξ => ∑ i : Fin m, Y (ξ i)) := by
      ext ξ
      simp
    rw [hf] at he
    rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvY : variance Y p ≤ b ^ 2 * ∫ ω, X ω ^ 2 ∂p := by
    refine (variance_le_expectation_sq hY.aestronglyMeasurable).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) ?_ (ae_of_all _ fun ω => ?_)
    · exact (hY.integrable (by norm_num)).const_mul _
    · change (X ω ^ 2) ^ 2 ≤ b ^ 2 * X ω ^ 2
      have := pow_le_pow_left₀ (hX0 ω) (hXb ω) 2
      nlinarith [sq_nonneg (X ω)]
  have hvar : variance (fun ξ : Fin m → Ω => (m : ℝ)⁻¹ * ∑ i : Fin m, Y (ξ i)) Q =
      ∫ ξ, ((m : ℝ)⁻¹ * ∑ i : Fin m, Y (ξ i) - ∫ ω, Y ω ∂p) ^ 2 ∂Q := by
    rw [variance_eq_integral havg.aestronglyMeasurable.aemeasurable, hint]
  refine ⟨(havg.sub (memLp_const (∫ ω, Y ω ∂p))).integrable_sq, ?_⟩
  calc _ = variance (fun ξ : Fin m → Ω => (m : ℝ)⁻¹ * ∑ i : Fin m, Y (ξ i)) Q := hvar.symm
    _ = variance Y p / m := hv
    _ ≤ _ := div_le_div_of_nonneg_right hvY (by positivity)

lemma mean_integral {X : Ω → ℝ} (hX : Measurable X) {b : ℝ} (hX0 : ∀ ω, 0 ≤ X ω)
    (hXb : ∀ ω, X ω ≤ b) {m : ℕ} (hm : 0 < m) :
    Integrable (fun ξ : Fin m → Ω => (m : ℝ)⁻¹ * ∑ i : Fin m, X (ξ i) ^ 2) (Measure.pi fun _ => p) ∧
    (∫ ξ : Fin m → Ω, (m : ℝ)⁻¹ * ∑ i : Fin m, X (ξ i) ^ 2 ∂(Measure.pi fun _ => p)) =
      ∫ ω, X ω ^ 2 ∂p := by
  have hc : Integrable (fun ω => X ω ^ 2) p :=
    Integrable.of_bound ((hX.pow_const 2).aestronglyMeasurable) (b ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hX0 ω) (hXb ω) 2)
  have hci (i : Fin m) : Integrable (fun ξ : Fin m → Ω => X (ξ i) ^ 2) (Measure.pi fun _ => p) :=
    integrable_of_preserving (g := fun ω => X ω ^ 2) (measurePreserving_eval (fun _ : Fin m => p) i) hc
  refine ⟨Integrable.const_mul (integrable_finsetSum _ fun i _ => hci i) _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hci i]
  have hi (i : Fin m) : (∫ ξ : Fin m → Ω, X (ξ i) ^ 2 ∂(Measure.pi fun _ => p)) = ∫ ω, X ω ^ 2 ∂p := by
    have hp := measurePreserving_eval (fun _ : Fin m => p) i
    have he := integral_map hp.measurable.aemeasurable
      (show AEStronglyMeasurable (fun ω => X ω ^ 2) ((Measure.pi fun _ : Fin m => p).map
        (fun ξ => ξ i)) from by rw [hp.map_eq]; exact hc.aestronglyMeasurable)
    rw [hp.map_eq] at he
    exact he.symm
  simp_rw [hi]
  simp [hm.ne']

lemma sqrt_mean_dev {X : Ω → ℝ} (hX : Measurable X) {b : ℝ} (hX0 : ∀ ω, 0 ≤ X ω)
    (hXb : ∀ ω, X ω ≤ b) {m : ℕ} (hm : 0 < m) :
    Integrable (fun ξ : Fin m → Ω => (Real.sqrt ((∑ i : Fin m, X (ξ i) ^ 2) / m) -
      Real.sqrt (∫ ω, X ω ^ 2 ∂p)) ^ 2) (Measure.pi fun _ => p) ∧
    (∫ ξ : Fin m → Ω, (Real.sqrt ((∑ i : Fin m, X (ξ i) ^ 2) / m) -
      Real.sqrt (∫ ω, X ω ^ 2 ∂p)) ^ 2 ∂(Measure.pi fun _ => p)) ≤ b ^ 2 / m := by
  obtain ⟨hi, hb⟩ := mean_sq_dev p hX hX0 hXb hm
  set μ := ∫ ω, X ω ^ 2 ∂p
  have hμ : 0 ≤ μ := integral_nonneg fun ω => sq_nonneg _
  have hM : ∀ ξ : Fin m → Ω, 0 ≤ (∑ i : Fin m, X (ξ i) ^ 2) / m := fun ξ =>
    div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
  have hdiv : ∀ ξ : Fin m → Ω, (∑ i : Fin m, X (ξ i) ^ 2) / m = (m : ℝ)⁻¹ * ∑ i : Fin m, X (ξ i) ^ 2 :=
    fun ξ => by rw [div_eq_inv_mul]
  have hmeas : Measurable (fun ξ : Fin m → Ω => (Real.sqrt ((∑ i : Fin m, X (ξ i) ^ 2) / m) -
      Real.sqrt μ) ^ 2) := by
    have : Measurable (fun ξ : Fin m → Ω => ∑ i : Fin m, X (ξ i) ^ 2) :=
      Finset.measurable_sum _ fun i _ => (hX.comp (measurable_pi_apply i)).pow_const 2
    exact ((this.div_const _).sqrt.sub_const _).pow_const 2
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  have hb0 : 0 ≤ b := le_trans (hX0 ω0) (hXb ω0)
  rcases eq_or_lt_of_le hμ with h0 | hpos
  · have hpt : ∀ ξ : Fin m → Ω, (Real.sqrt ((∑ i : Fin m, X (ξ i) ^ 2) / m) - Real.sqrt μ) ^ 2 =
        (m : ℝ)⁻¹ * ∑ i : Fin m, X (ξ i) ^ 2 := by
      intro ξ
      rw [← h0, Real.sqrt_zero, sub_zero, Real.sq_sqrt (hM ξ), hdiv]
    obtain ⟨hint, hE⟩ := mean_integral p hX hX0 hXb hm
    simp_rw [hpt]
    refine ⟨hint, ?_⟩
    rw [hE, show (∫ ω, X ω ^ 2 ∂p) = 0 from h0.symm]
    positivity
  · have hpt : ∀ ξ : Fin m → Ω, (Real.sqrt ((∑ i : Fin m, X (ξ i) ^ 2) / m) - Real.sqrt μ) ^ 2 ≤
        ((m : ℝ)⁻¹ * ∑ i : Fin m, X (ξ i) ^ 2 - μ) ^ 2 / μ := by
      intro ξ
      set M := (∑ i : Fin m, X (ξ i) ^ 2) / m
      have hMn := hM ξ
      rw [← hdiv ξ]
      have hsM := Real.sq_sqrt hMn
      have hsμ := Real.sq_sqrt hμ
      have hpos' : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hpos
      have hk : (M - μ) = (Real.sqrt M - Real.sqrt μ) * (Real.sqrt M + Real.sqrt μ) := by
        nlinarith
      rw [hk, mul_pow, le_div_iff₀ hpos]
      have : μ ≤ (Real.sqrt M + Real.sqrt μ) ^ 2 := by
        nlinarith [Real.sqrt_nonneg M]
      exact le_trans (by rw [← hsμ]) (mul_le_mul_of_nonneg_left this (sq_nonneg _))
    have hi2 : Integrable (fun ξ : Fin m → Ω => ((m : ℝ)⁻¹ * ∑ i : Fin m, X (ξ i) ^ 2 - μ) ^ 2 / μ)
        (Measure.pi fun _ => p) := hi.div_const μ
    have hint : Integrable (fun ξ : Fin m → Ω => (Real.sqrt ((∑ i : Fin m, X (ξ i) ^ 2) / m) -
        Real.sqrt μ) ^ 2) (Measure.pi fun _ => p) :=
      hi2.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ξ)
    refine ⟨hint, ?_⟩
    refine (integral_mono hint hi2 hpt).trans ?_
    rw [integral_div, div_le_iff₀ hpos]
    calc _ ≤ b ^ 2 * μ / m := hb
      _ = b ^ 2 / m * μ := by ring

end OracleTemplate.ChiSquareDro
