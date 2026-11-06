import LongTails.Proofs.StochasticQuasarEnergy
import LongTails.Proofs.StochasticQuasarClipping

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma measurable_energy_jump {Q : Set E} {P : E → E} (hP : ConstrainedMonotone.Proj Q P)
    {f : E → ℝ} (hf : Continuous f) {h : Ω → E} (hm : Measurable h)
    (u x z : E) (A η c : ℝ) :
    Measurable (fun ω => GradientOnlyQuasar.weightedEnergy f u A (x - η • h ω) (P (z - c • h ω)) -
      GradientOnlyQuasar.weightedEnergy f u A x z) := by
  have hx := (measurable_const (a := x)).sub (hm.const_smul η)
  have hz := ((hP.lipschitz.continuous.measurable).comp
    ((measurable_const (a := z)).sub (hm.const_smul c))).sub_const u
  exact (((hf.measurable.comp hx).sub_const (f u)).const_mul A |>.add
    ((hz.norm.pow_const 2).div_const 2)).sub_const _

lemma bounded_energy_jump_second {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} (hP : ConstrainedMonotone.Proj Q P)
    {f : E → ℝ} {G : E → E} {u x z : E} {h : Ω → E}
    {A η c L q B H p V : ℝ} (hu : u ∈ Q) (hz : z ∈ Q)
    (hA : 0 < A) (hη : 0 < η) (hc0 : 0 ≤ c) (hL : 0 < L)
    (hq : 0 ≤ q) (hB : 0 ≤ B) (hH : 0 ≤ H) (hp : 2 ≤ p)
    (hLη : L * η = q) (hc : c ^ 2 ≤ A * η * q)
    (hsmall : 32 * p * q ≤ 1) (hqcap : q ≤ 1 / 16)
    (hbalance : p * (A * η) * H ^ 2 = B)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ x, f u ≤ f x) (henergy : GradientOnlyQuasar.weightedEnergy f u A x z ≤ B)
    (hm : Measurable h) (hh : ∀ ω, ‖h ω‖ ≤ H)
    (h2i : Integrable (fun ω => ‖h ω - G x‖ ^ 2) μ)
    (h2 : (∫ ω, ‖h ω - G x‖ ^ 2 ∂μ) ≤ V) :
    let J := fun ω => GradientOnlyQuasar.weightedEnergy f u A (x - η • h ω) (P (z - c • h ω)) -
      GradientOnlyQuasar.weightedEnergy f u A x z
    Measurable J ∧ Integrable J μ ∧ Integrable (fun ω => J ω ^ 2) μ ∧
      (∀ ω, |J ω| ≤ B / p) ∧
      (∫ ω, J ω ^ 2 ∂μ) ≤ 18 * q * B * (A * η * ‖G x‖ ^ 2) + 66 * q * (A * η) * B * V := by
  let J := fun ω => GradientOnlyQuasar.weightedEnergy f u A (x - η • h ω) (P (z - c • h ω)) -
    GradientOnlyQuasar.weightedEnergy f u A x z
  let J0 := GradientOnlyQuasar.weightedEnergy f u A (x - η • G x) (P (z - c • G x)) -
    GradientOnlyQuasar.weightedEnergy f u A x z
  have hp0 : 0 < p := by linarith
  have hqhalf : q ≤ 1 / 2 := by linarith
  have hqfour : q ≤ 1 / 4 := by linarith
  have hqp : 8 * q ≤ p := by linarith
  have hpt (ω : Ω) := localized_clipped_jump hP hz hA hη hc0 hL hq hB hH hp0 hLη hc
    hsmall hqhalf hbalance (hh ω) hG hlip hmin henergy
  have hJb (ω : Ω) : |J ω| ≤ B / p := (hpt ω).2
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hG y).differentiableAt.continuousAt
  have hJm : Measurable J := measurable_energy_jump hP hfc hm u x z A η c
  have hJi : Integrable J μ := Integrable.of_bound hJm.aestronglyMeasurable (B / p)
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hJb ω))
  have hJ2i : Integrable (fun ω => J ω ^ 2) μ := Integrable.of_bound
    (hJm.pow_const 2).aestronglyMeasurable ((B / p) ^ 2) (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (J ω)) (hJb ω) 2))
  have hJ0 : J0 ^ 2 ≤ 9 * q * B * (A * η * ‖G x‖ ^ 2) :=
    localized_exact_jump_square hP hz hA.le hη.le hc0 hL hq hLη hc hqcap hG hlip hmin henergy
  have hsecond (ω : Ω) : J ω ^ 2 ≤ 18 * q * B * (A * η * ‖G x‖ ^ 2) +
      66 * q * (A * η) * B * ‖h ω - G x‖ ^ 2 := by
    have he : ‖h ω - G x‖ ≤ 2 * H := (norm_sub_le _ _).trans (by have hg := (hpt ω).1; have hh' := hh ω; linarith)
    have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
    have hcap : p * (A * η) * ‖h ω - G x‖ ^ 2 ≤ 4 * B := by
      have ht := mul_le_mul_of_nonneg_left he2 (by positivity : 0 ≤ p * (A * η))
      nlinarith [hbalance]
    have hd := localized_jump_difference (h := h ω) hP hu hA.le hη.le hc0 hL hq hB hLη hc hqfour
      hG hlip hmin henergy
    have hd' := energy_perturbation_second (mul_nonneg hA.le hη.le) hq hB hp0 hcap hqp hd
    have hdiff : J ω - J0 =
        GradientOnlyQuasar.weightedEnergy f u A (x - η • h ω) (P (z - c • h ω)) -
        GradientOnlyQuasar.weightedEnergy f u A (x - η • G x) (P (z - c • G x)) := by dsimp [J, J0]; ring
    rw [← hdiff] at hd'
    nlinarith [sq_nonneg (J ω - 2 * J0)]
  have hupper := (integrable_const (18 * q * B * (A * η * ‖G x‖ ^ 2))).add
    (h2i.const_mul (66 * q * (A * η) * B))
  have hint := integral_mono hJ2i hupper hsecond
  simp only [Pi.add_apply] at hint
  rw [integral_add (integrable_const _) (h2i.const_mul _)] at hint
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul] at hint
  have hv := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 66 * q * (A * η) * B)
  exact ⟨hJm, hJi, hJ2i, hJb, by linarith⟩

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma biased_energy_jump_drift {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} (hP : ConstrainedMonotone.Proj Q P)
    {f : E → ℝ} {G : E → E} {u x z : E} {h : Ω → E}
    {A η c L q B γ β V : ℝ} (hu : u ∈ Q) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hc0 : 0 ≤ c) (hL : 0 < L) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hLη : L * η = q) (hc : c ^ 2 ≤ A * η * q) (hqcap : q ≤ 1 / 2)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ x, f u ≤ f x) (henergy : GradientOnlyQuasar.weightedEnergy f u A x z ≤ B)
    (hquasar : γ * (f x - f u) ≤ ⟪G x, x - u⟫)
    (hi : Integrable h μ) (h2i : Integrable (fun ω => ‖h ω - G x‖ ^ 2) μ)
    (hb : ‖(∫ ω, h ω ∂μ) - G x‖ ≤ β) (h2 : (∫ ω, ‖h ω - G x‖ ^ 2 ∂μ) ≤ V)
    (hJi : Integrable (fun ω =>
      GradientOnlyQuasar.weightedEnergy f u A (x - η • h ω) (P (z - c • h ω)) -
        GradientOnlyQuasar.weightedEnergy f u A x z) μ) :
    γ * c * (f x - f u) + c * ⟪G x, z - x⟫ +
      (∫ ω, GradientOnlyQuasar.weightedEnergy f u A (x - η • h ω) (P (z - c • h ω)) -
        GradientOnlyQuasar.weightedEnergy f u A x z ∂μ) ≤
      -(1 - q) * (A * η * ‖G x‖ ^ 2) + 3 * Real.sqrt (q * (A * η) * B) * β + q * (A * η) * V := by
  let J := fun ω => GradientOnlyQuasar.weightedEnergy f u A (x - η • h ω) (P (z - c • h ω)) -
    GradientOnlyQuasar.weightedEnergy f u A x z
  let e := fun ω => h ω - G x
  let T := ((2 * q - 1) * (A * η)) • G x - c • (z - u)
  let F := γ * c * (f x - f u) + c * ⟪G x, z - x⟫
  let C := -(1 - q) * (A * η * ‖G x‖ ^ 2)
  have hei : Integrable e μ := hi.sub (integrable_const (G x))
  have he2i : Integrable (fun ω => ‖e ω‖ ^ 2) μ := h2i
  have hpt (ω : Ω) : F + J ω ≤ C + ⟪T, e ω⟫ + q * (A * η) * ‖e ω‖ ^ 2 := by
    have hh := projected_noisy_energy_drift (z := z) (h := h ω) hP hu hA hc0 hLη hc hG hlip hquasar
    change F + J ω ≤ C + ⟪e ω, T⟫ + q * (A * η) * ‖e ω‖ ^ 2 at hh
    simpa only [real_inner_comm T (e ω)] using hh
  have hCi : Integrable (fun ω => C + ⟪T, e ω⟫) μ := (integrable_const C).add (hei.const_inner T)
  have hupper := hCi.add (he2i.const_mul (q * (A * η)))
  have hint := integral_mono ((integrable_const F).add hJi) hupper hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add (integrable_const F) hJi,
    integral_add hCi (he2i.const_mul _),
    integral_add (integrable_const C) (hei.const_inner T), integral_const_mul, integral_inner hei] at hint
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul] at hint
  have hloc := energy_localization hA hL hG hlip hmin henergy
  have hg : (A * η) * ‖G x‖ ^ 2 ≤ 2 * q * B := by
    have ht := mul_le_mul_of_nonneg_left hloc.2 hη
    have he : η * (2 * L * B) = 2 * q * B := by rw [← hLη]; ring
    rw [he] at ht
    nlinarith
  have hT : ‖T‖ ≤ 3 * Real.sqrt (q * (A * η) * B) :=
    noisy_drift_coefficient (mul_nonneg hA hη) hq hB hqcap hc hg hloc.1
  have hmean : ‖∫ ω, e ω ∂μ‖ ≤ β := by
    dsimp [e]
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
    exact hb
  have hinner := (real_inner_le_norm T (∫ ω, e ω ∂μ)).trans
    (mul_le_mul hT hmean (norm_nonneg _) (by positivity : 0 ≤ 3 * Real.sqrt (q * (A * η) * B)))
  have hv := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ q * (A * η))
  change F + (∫ ω, J ω ∂μ) ≤ C + 3 * Real.sqrt (q * (A * η) * B) * β + q * (A * η) * V
  dsimp only [J, C, e] at hint hinner hv ⊢
  linarith

lemma clipped_energy_moments {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} (hP : ConstrainedMonotone.Proj Q P)
    {f : E → ℝ} {G : E → E} {u x z : E} {Z : Ω → E}
    {A η c L q B H p γ β V : ℝ} (hu : u ∈ Q) (hz : z ∈ Q)
    (hA : 0 < A) (hη : 0 < η) (hc0 : 0 ≤ c) (hL : 0 < L)
    (hq : 0 ≤ q) (hB : 0 ≤ B) (hH : 0 < H) (hp : 2 ≤ p)
    (hLη : L * η = q) (hc : c ^ 2 ≤ A * η * q)
    (hsmall : 144 * p * q ≤ 1) (hqcap : q ≤ 1 / 16)
    (hbalance : p * (A * η) * H ^ 2 = B)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ x, f u ≤ f x) (henergy : GradientOnlyQuasar.weightedEnergy f u A x z ≤ B)
    (hquasar : γ * (f x - f u) ≤ ⟪G x, x - u⟫)
    (hm : Measurable Z) (hi : Integrable Z μ)
    (h2i : Integrable (fun ω => ‖Z ω - G x‖ ^ 2) μ)
    (hb : ‖(∫ ω, Z ω ∂μ) - G x‖ ≤ β) (h2 : (∫ ω, ‖Z ω - G x‖ ^ 2 ∂μ) ≤ V) :
    let J := fun ω => GradientOnlyQuasar.weightedEnergy f u A (x - η • clip H (Z ω))
      (P (z - c • clip H (Z ω))) - GradientOnlyQuasar.weightedEnergy f u A x z
    Measurable J ∧ Integrable J μ ∧ Integrable (fun ω => J ω ^ 2) μ ∧
      (∀ ω, |J ω| ≤ B / p) ∧
      (∫ ω, J ω ^ 2 ∂μ) ≤ 18 * q * B * (A * η * ‖G x‖ ^ 2) + 66 * q * (A * η) * B * V ∧
      γ * c * (f x - f u) + c * ⟪G x, z - x⟫ + (∫ ω, J ω ∂μ) ≤
        -(1 - q) * (A * η * ‖G x‖ ^ 2) + A * η * V + 3 * Real.sqrt (q * (A * η) * B) * β := by
  have hp0 : 0 < p := by linarith
  have hqhalf : q ≤ 1 / 2 := by linarith
  have hs32 : 32 * p * q ≤ 1 := by nlinarith [mul_nonneg hp0.le hq]
  have hg := (localized_clipped_jump (h := (0 : E)) hP hz hA hη hc0 hL hq hB hH.le hp0 hLη hc
    hs32 hqhalf hbalance (by simpa only [norm_zero] using hH.le) hG hlip hmin henergy).1
  have hclip := biased_clipping_moments hH hg hm hi h2i hb h2
  have hcm : Measurable (fun ω => clip H (Z ω)) := (measurable_clip H).comp hm
  have hs := bounded_energy_jump_second hP hu hz hA hη hc0 hL hq hB hH.le hp hLη hc hs32 hqcap hbalance
    hG hlip hmin henergy hcm (fun ω => norm_clip_le hH.le (Z ω)) hclip.2.1 hclip.2.2.1
  have hd := biased_energy_jump_drift hP hu hA.le hη.le hc0 hL hq hB hLη hc hqhalf
    hG hlip hmin henergy hquasar hclip.1 hclip.2.1 hclip.2.2.2.1 hclip.2.2.1 hs.2.1
  have hn := clipping_noise_absorption (mul_nonneg hA.le hη.le) hq hB hH.le hqhalf hsmall hbalance
  have hV0 : 0 ≤ V := (integral_nonneg (μ := μ) (fun ω => sq_nonneg ‖Z ω - G x‖)).trans h2
  have hn' : 6 * Real.sqrt (q * (A * η) * B) * V / H ≤ (1 - q) * (A * η) * V := by
    apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_right hn hV0
    nlinarith
  have he : 3 * Real.sqrt (q * (A * η) * B) * (β + 2 * V / H) =
      3 * Real.sqrt (q * (A * η) * B) * β + 6 * Real.sqrt (q * (A * η) * B) * V / H := by ring
  rw [he] at hd
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, ?_⟩
  dsimp only
  nlinarith

end OracleTemplate.StochasticQuasar
