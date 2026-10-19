import LongTails.Setups.QuantileSymmetricRemainderConvex
import LongTails.Algorithms.CharacteristicGradient
import LongTails.Proofs.CharacteristicLogEstimator
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.CharacteristicLogMoments

open LongTails.Algorithms.CharacteristicGradient

lemma norm_product_le_two_pow {ι : Type*} (s : Finset ι) (u : ι → ℂ)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 2) : ‖∏ i ∈ s, u i‖ ≤ (2 : ℝ) ^ s.card := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _i ∈ s, (2 : ℝ) := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hu
    _ = _ := by simp

lemma integrable_bounded_product {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {U : ι → Ω → ℂ}
    (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, U i ω) P := by
  apply Integrable.of_bound (Finset.measurable_fun_prod s
    (fun i _ => hUm i)).aestronglyMeasurable ((2 : ℝ) ^ s.card)
  exact Filter.Eventually.of_forall fun ω => norm_product_le_two_pow s (fun i => U i ω)
    (fun i _ => hUb i ω)

lemma independent_finset_product_integral {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ι → Ω → ℂ} (hU : iIndepFun U P)
    (hUm : ∀ i, AEStronglyMeasurable (U i) P) (s : Finset ι) :
    (∫ ω, ∏ i ∈ s, U i ω ∂P) = ∏ i ∈ s, ∫ ω, U i ω ∂P := by
  have h := (hU.restrict s).integral_fun_prod_eq_prod_integral (fun i => hUm i)
  change (∫ ω, ∏ i : s, U i ω ∂P) = ∏ i : s, ∫ ω, U i ω ∂P at h
  have hp (ω : Ω) := Finset.prod_coe_sort s (fun i => U i ω)
  simp_rw [hp] at h
  rw [Finset.prod_coe_sort s (fun i => ∫ ω, U i ω ∂P)] at h
  exact h

lemma independent_finset_product_square {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ι → Ω → ℂ} (hU : iIndepFun U P)
    (hUm : ∀ i, AEStronglyMeasurable (U i) P) (s : Finset ι) :
    (∫ ω, ‖∏ i ∈ s, U i ω‖ ^ 2 ∂P) = ∏ i ∈ s, ∫ ω, ‖U i ω‖ ^ 2 ∂P := by
  have hV := hU.comp (fun _ (z : ℂ) => ‖z‖ ^ 2) (fun _ => by fun_prop)
  have h := (hV.restrict s).integral_fun_prod_eq_prod_integral
    (fun i => (hUm i).norm.pow 2)
  change (∫ ω, ∏ i : s, ‖U i ω‖ ^ 2 ∂P) = ∏ i : s, ∫ ω, ‖U i ω‖ ^ 2 ∂P at h
  have hp (ω : Ω) := Finset.prod_coe_sort s (fun i => ‖U i ω‖ ^ 2)
  simp_rw [hp] at h
  rw [Finset.prod_coe_sort s (fun i => ∫ ω, ‖U i ω‖ ^ 2 ∂P)] at h
  simpa only [norm_prod, ← Finset.prod_pow] using h

lemma norm_sum_sq_le_weighted {ι : Type*} (s : Finset ι) (z : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hs : ∑ i ∈ s, w i ≤ 1) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ ∑ i ∈ s, ‖z i‖ ^ 2 / w i := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => ‖z i‖) (f := w) (g := fun i => ‖z i‖ ^ 2 / w i)
    (fun i hi => (hw i hi).le)
    (fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le)
    (fun i hi => by rw [mul_div_cancel₀ _ (ne_of_gt (hw i hi))])
  have hn := norm_sum_le s z
  have hn0 := norm_nonneg (∑ i ∈ s, z i)
  have hsum0 : 0 ≤ ∑ i ∈ s, ‖z i‖ ^ 2 / w i :=
    Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le
  have hm := mul_le_mul_of_nonneg_right hs hsum0
  nlinarith

lemma integrable_logPolynomial {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {U : Fin K → Ω → ℂ}
    (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2) :
    Integrable (fun ω => logPolynomial (fun i => U i ω)) P := by
  unfold logPolynomial
  apply integrable_finsetSum
  intro k _
  exact (integrable_bounded_product hUm hUb (Finset.Iic k)).div_const _

lemma integral_logPolynomial {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U : Fin K → Ω → ℂ} {m : ℂ}
    (hU : iIndepFun U P) (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2)
    (hm : ∀ i, (∫ ω, U i ω ∂P) = m) :
    (∫ ω, logPolynomial (fun i => U i ω) ∂P) =
      ∑ k ∈ Finset.range (K + 1), m ^ k / k := by
  unfold logPolynomial
  rw [integral_finsetSum _ (fun k _ =>
    (integrable_bounded_product hUm hUb (Finset.Iic k)).div_const _)]
  simp_rw [integral_div, independent_finset_product_integral hU
    (fun i => (hUm i).aestronglyMeasurable), hm, Finset.prod_const, Fin.card_Iic]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => m ^ (k + 1) / ((k : ℂ) + 1))]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.cast_zero, div_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  simp

lemma half_power_sum_le_one (K : ℕ) :
    (∑ k : Fin K, (1 / 2 : ℝ) ^ (k.val + 1)) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1))]
  simp_rw [pow_succ, ← Finset.sum_mul]
  have h := sum_geometric_two_le K
  nlinarith

lemma integrable_bounded_product_square {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {U : ι → Ω → ℂ}
    (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2) (s : Finset ι) :
    Integrable (fun ω => ‖∏ i ∈ s, U i ω‖ ^ 2) P := by
  apply Integrable.of_bound ((Finset.measurable_fun_prod s
    (fun i _ => hUm i)).norm.pow_const 2).aestronglyMeasurable (((2 : ℝ) ^ s.card) ^ 2)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_product_le_two_pow s (fun i => U i ω)
    (fun i _ => hUb i ω)) 2

lemma norm_logPolynomial_sq_le {K : ℕ} (u : Fin K → ℂ) :
    ‖logPolynomial u‖ ^ 2 ≤
      ∑ k : Fin K, ‖∏ j ∈ Finset.Iic k, u j‖ ^ 2 / (1 / 2 : ℝ) ^ (k.val + 1) := by
  have h := norm_sum_sq_le_weighted Finset.univ
    (fun k : Fin K => (∏ j ∈ Finset.Iic k, u j) / ((k.val : ℂ) + 1))
    (fun k => (1 / 2 : ℝ) ^ (k.val + 1)) (fun _ _ => by positivity)
    (half_power_sum_le_one K)
  apply h.trans
  apply Finset.sum_le_sum
  intro k _
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hn : ‖(k.val : ℂ) + 1‖ = (k.val : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k.val + 1)
  rw [norm_div, hn]
  have hk : 1 ≤ (k.val : ℝ) + 1 := by
    have hk0 : 0 ≤ (k.val : ℝ) := by positivity
    linarith
  have hb := div_le_self (norm_nonneg (∏ j ∈ Finset.Iic k, u j))
    hk
  exact pow_le_pow_left₀ (by positivity) hb 2

lemma measurable_logPolynomial {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {U : Fin K → Ω → ℂ} (hUm : ∀ i, Measurable (U i)) :
    Measurable (fun ω => logPolynomial (fun i => U i ω)) := by
  unfold logPolynomial
  exact Finset.measurable_fun_sum _ fun k _ =>
    (Finset.measurable_fun_prod _ fun j _ => hUm j).div_const _

lemma integrable_logPolynomial_square {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {U : Fin K → Ω → ℂ}
    (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2) :
    Integrable (fun ω => ‖logPolynomial (fun i => U i ω)‖ ^ 2) P := by
  have hi : Integrable (fun ω => ∑ k : Fin K,
      ‖∏ j ∈ Finset.Iic k, U j ω‖ ^ 2 / (1 / 2 : ℝ) ^ (k.val + 1)) P :=
    integrable_finsetSum _ fun k _ =>
      (integrable_bounded_product_square hUm hUb (Finset.Iic k)).div_const _
  apply hi.mono_nonneg ((measurable_logPolynomial hUm).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  exact Filter.Eventually.of_forall fun ω => norm_logPolynomial_sq_le (fun i => U i ω)

lemma integral_logPolynomial_square_le {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U : Fin K → Ω → ℂ}
    (hU : iIndepFun U P) (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2)
    (hq : ∀ i, (∫ ω, ‖U i ω‖ ^ 2 ∂P) ≤ 1 / 4) :
    (∫ ω, ‖logPolynomial (fun i => U i ω)‖ ^ 2 ∂P) ≤ 1 := by
  have hp (k : Fin K) : (∫ ω, ‖∏ j ∈ Finset.Iic k, U j ω‖ ^ 2 ∂P) ≤
      (1 / 4 : ℝ) ^ (k.val + 1) := by
    rw [independent_finset_product_square hU (fun i => (hUm i).aestronglyMeasurable)]
    calc
      _ ≤ ∏ _j ∈ Finset.Iic k, (1 / 4 : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (fun j _ => hq j)
      _ = _ := by simp [Fin.card_Iic]
  have hi (k : Fin K) : Integrable (fun ω =>
      ‖∏ j ∈ Finset.Iic k, U j ω‖ ^ 2 / (1 / 2 : ℝ) ^ (k.val + 1)) P :=
    (integrable_bounded_product_square hUm hUb (Finset.Iic k)).div_const _
  calc
    _ ≤ ∫ ω, ∑ k : Fin K,
        ‖∏ j ∈ Finset.Iic k, U j ω‖ ^ 2 / (1 / 2 : ℝ) ^ (k.val + 1) ∂P :=
      integral_mono (integrable_logPolynomial_square hUm hUb)
        (integrable_finsetSum _ fun k _ => hi k)
        (fun ω => norm_logPolynomial_sq_le (fun i => U i ω))
    _ = ∑ k : Fin K, (∫ ω, ‖∏ j ∈ Finset.Iic k, U j ω‖ ^ 2 ∂P) /
        (1 / 2 : ℝ) ^ (k.val + 1) := by
      rw [integral_finsetSum _ (fun k _ => hi k)]
      simp_rw [integral_div]
    _ ≤ ∑ k : Fin K, (1 / 4 : ℝ) ^ (k.val + 1) / (1 / 2 : ℝ) ^ (k.val + 1) :=
      Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right (hp k) (by positivity)
    _ = ∑ k : Fin K, (1 / 2 : ℝ) ^ (k.val + 1) := by
      simp_rw [← div_pow]
      norm_num
    _ ≤ 1 := half_power_sum_le_one K

lemma polynomial_im_integrable {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {U : Fin K → Ω → ℂ}
    (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2) (t : ℝ) :
    Integrable (fun ω => -(logPolynomial (fun i => U i ω)).im / t) P :=
  (integrable_logPolynomial hUm hUb).im.neg.div_const t

lemma polynomial_im_square_integrable {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {U : Fin K → Ω → ℂ}
    (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2) (t : ℝ) :
    Integrable (fun ω => (-(logPolynomial (fun i => U i ω)).im / t) ^ 2) P := by
  have hi := (integrable_logPolynomial_square (P := P) hUm hUb).div_const (t ^ 2)
  apply hi.mono_nonneg (by
    exact ((((Complex.measurable_im.comp (measurable_logPolynomial hUm)).neg).div_const t).pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  apply Filter.Eventually.of_forall
  intro ω
  rw [div_pow, neg_sq]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  have h := Complex.abs_im_le_norm (logPolynomial (fun i => U i ω))
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

lemma polynomial_im_square_bound {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U : Fin K → Ω → ℂ}
    (hU : iIndepFun U P) (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2)
    (hq : ∀ i, (∫ ω, ‖U i ω‖ ^ 2 ∂P) ≤ 1 / 4) (t : ℝ) :
    (∫ ω, (-(logPolynomial (fun i => U i ω)).im / t) ^ 2 ∂P) ≤ 1 / t ^ 2 := by
  calc
    _ ≤ ∫ ω, ‖logPolynomial (fun i => U i ω)‖ ^ 2 / t ^ 2 ∂P := by
      apply integral_mono (polynomial_im_square_integrable hUm hUb t)
        ((integrable_logPolynomial_square hUm hUb).div_const _)
      intro ω
      dsimp only
      rw [div_pow, neg_sq]
      apply div_le_div_of_nonneg_right _ (sq_nonneg t)
      have h := Complex.abs_im_le_norm (logPolynomial (fun i => U i ω))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (∫ ω, ‖logPolynomial (fun i => U i ω)‖ ^ 2 ∂P) / t ^ 2 := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right
      (integral_logPolynomial_square_le hU hUm hUb hq) (sq_nonneg t)

lemma polynomial_im_bias_bound {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U : Fin K → Ω → ℂ} {m : ℂ}
    (hU : iIndepFun U P) (hUm : ∀ i, Measurable (U i)) (hUb : ∀ i ω, ‖U i ω‖ ≤ 2)
    (hm : ∀ i, (∫ ω, U i ω ∂P) = m) (hmn : ‖m‖ ≤ 1 / 2)
    {t g B : ℝ} (ht : 0 < t) (hb : |(Complex.log (1 - m)).im - t * g| ≤ B) :
    |(∫ ω, -(logPolynomial (fun i => U i ω)).im / t ∂P) - g| ≤
      (B + (1 / 2 : ℝ) ^ K) / t := by
  have hint := integral_logPolynomial hU hUm hUb hm
  have him := integral_im (integrable_logPolynomial (P := P) hUm hUb)
  have he : (∫ ω, -(logPolynomial (fun i => U i ω)).im / t ∂P) =
      -(∑ k ∈ Finset.range (K + 1), m ^ k / k).im / t := by
    rw [integral_div, integral_neg]
    rw [show (∫ ω, (logPolynomial (fun i => U i ω)).im ∂P) =
      (∫ ω, logPolynomial (fun i => U i ω) ∂P).im from him, hint]
  rw [he]
  have hr := CharacteristicLogEstimator.log_series_remainder_half K hmn
  have hi := (Complex.abs_im_le_norm
    (Complex.log (1 - m) + ∑ k ∈ Finset.range (K + 1), m ^ k / k)).trans hr
  rw [Complex.add_im] at hi
  have htri := abs_add_le
    (-((Complex.log (1 - m)).im + (∑ k ∈ Finset.range (K + 1), m ^ k / k).im))
    ((Complex.log (1 - m)).im - t * g)
  rw [abs_neg] at htri
  have hb' : |-(∑ k ∈ Finset.range (K + 1), m ^ k / k).im - t * g| ≤
      B + (1 / 2 : ℝ) ^ K := by
    have hid : -((Complex.log (1 - m)).im + (∑ k ∈ Finset.range (K + 1), m ^ k / k).im) +
        ((Complex.log (1 - m)).im - t * g) =
        -(∑ k ∈ Finset.range (K + 1), m ^ k / k).im - t * g := by ring
    rw [hid] at htri
    linarith
  rw [show -(∑ k ∈ Finset.range (K + 1), m ^ k / k).im / t - g =
    (-(∑ k ∈ Finset.range (K + 1), m ^ k / k).im - t * g) / t by field_simp,
    abs_div, abs_of_pos ht]
  exact div_le_div_of_nonneg_right hb' ht.le

lemma coordinate_estimator_bounds {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {Z : Fin K → Ω → ℝ} (hZ : iIndepFun Z P) (hZm : ∀ i, Measurable (Z i))
    (hZlaw : ∀ i, P.map (Z i) = μ) {t g r M : ℝ}
    (hμ : LongTails.Setups.QuantileSymmetricRemainderConvex.NoiseCondition μ r M)
    (ht : 0 < t) (hr : 0 ≤ r) (htr : t * (|g| + r) ≤ 1 / 4) :
    Integrable (fun ω => coordinateEstimate t (fun i => g + Z i ω)) P ∧
    |(∫ ω, coordinateEstimate t (fun i => g + Z i ω) ∂P) - g| ≤
      M * t + (1 / 2 : ℝ) ^ K / t ∧
    Integrable (fun ω => (coordinateEstimate t (fun i => g + Z i ω)) ^ 2) P ∧
    (∫ ω, (coordinateEstimate t (fun i => g + Z i ω)) ^ 2 ∂P) ≤ 1 / t ^ 2 := by
  let U : Fin K → Ω → ℂ := fun i ω => phaseIncrement t (g + Z i ω)
  let c := ∫ z : ℝ, Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) ∂μ
  have hUm : ∀ i, Measurable (U i) := by
    intro i
    dsimp [U, phaseIncrement]
    fun_prop
  have hUb : ∀ i ω, ‖U i ω‖ ≤ 2 := by
    intro i ω
    dsimp [U, phaseIncrement]
    rw [norm_sub_rev]
    exact CharacteristicLogEstimator.phase_increment_norm_le_two _
  have hUi : iIndepFun U P := hZ.comp (fun _ z => phaseIncrement t (g + z))
    (fun _ => by unfold phaseIncrement; fun_prop)
  have hm : ∀ i, (∫ ω, U i ω ∂P) = 1 - c := by
    intro i
    have h := integral_map (μ := P) (hZm i).aemeasurable
      (f := fun z => phaseIncrement t (g + z)) (by unfold phaseIncrement; fun_prop)
    rw [hZlaw i] at h
    change (∫ ω, phaseIncrement t (g + Z i ω) ∂P) = _
    rw [← h]
    unfold phaseIncrement
    rw [integral_sub (integrable_const 1) (CharacteristicLogEstimator.integrable_phase μ t g)]
    simp only [integral_const, probReal_univ, one_smul, c]
  have hq : ∀ i, (∫ ω, ‖U i ω‖ ^ 2 ∂P) ≤ 1 / 4 := by
    intro i
    have h := integral_map (μ := P) (hZm i).aemeasurable
      (f := fun z => ‖phaseIncrement t (g + z)‖ ^ 2) (by unfold phaseIncrement; fun_prop)
    rw [hZlaw i] at h
    change (∫ ω, ‖phaseIncrement t (g + Z i ω)‖ ^ 2 ∂P) ≤ _
    rw [← h]
    simp_rw [phaseIncrement, norm_sub_rev]
    exact (CharacteristicLogEstimator.phase_square_quantile_bound ht.le htr hμ.2).trans
      (by norm_num)
  have hmn : ‖1 - c‖ ≤ 1 / 2 := by
    rw [norm_sub_rev]
    exact CharacteristicLogEstimator.phase_mean_close ht.le htr hμ.2
  have hb : |(Complex.log (1 - (1 - c))).im - t * g| ≤ t ^ 2 * M := by
    rw [sub_sub_cancel]
    apply CharacteristicLogEstimator.phase_log_bias ht.le hr htr hμ.2
    obtain ⟨S, A, hSA, hS, hi, hc, hi2, hM⟩ := hμ.1
    exact CharacteristicLogEstimator.mixture_sin_integral_bound hSA hS hi hc hi2 hM t
  refine ⟨polynomial_im_integrable hUm hUb t, ?_,
    polynomial_im_square_integrable hUm hUb t, polynomial_im_square_bound hUi hUm hUb hq t⟩
  have h := polynomial_im_bias_bound hUi hUm hUb hm hmn ht hb
  change |(∫ ω, coordinateEstimate t (fun i => g + Z i ω) ∂P) - g| ≤ _ at h
  have he : (t ^ 2 * M + (1 / 2 : ℝ) ^ K) / t = M * t + (1 / 2 : ℝ) ^ K / t := by
    field_simp [ht.ne']
  rw [he] at h
  exact h

lemma scalar_error_second_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {t g : ℝ}
    (hi : Integrable X P) (hi2 : Integrable (fun ω => X ω ^ 2) P)
    (hv : (∫ ω, X ω ^ 2 ∂P) ≤ 1 / t ^ 2)
    (ht : 0 < t) (hg : |t * g| ≤ 1) :
    Integrable (fun ω => (X ω - g) ^ 2) P ∧
    (∫ ω, (X ω - g) ^ 2 ∂P) ≤ 4 / t ^ 2 := by
  have hierr : Integrable (fun ω => (X ω - g) ^ 2) P := by
    have he (ω : Ω) : (X ω - g) ^ 2 = X ω ^ 2 - (2 * g) * X ω + g ^ 2 := by ring
    simp_rw [he]
    exact (hi2.sub (hi.const_mul _)).add (integrable_const _)
  refine ⟨hierr, ?_⟩
  have hb := integral_mono hierr ((hi2.const_mul 2).add (integrable_const (2 * g ^ 2)))
    (fun ω => by dsimp; nlinarith [sq_nonneg (X ω + g)])
  simp only [Pi.add_apply] at hb
  rw [integral_add (hi2.const_mul 2) (integrable_const (2 * g ^ 2)), integral_const_mul] at hb
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
  have hg2 : g ^ 2 ≤ 1 / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    have hs := pow_le_pow_left₀ (abs_nonneg (t * g)) hg 2
    rw [sq_abs, mul_pow, one_pow] at hs
    nlinarith
  rw [show 4 / t ^ 2 = 2 * (1 / t ^ 2) + 2 * (1 / t ^ 2) by ring]
  linarith

end LongTails.Proofs.CharacteristicLogMoments
