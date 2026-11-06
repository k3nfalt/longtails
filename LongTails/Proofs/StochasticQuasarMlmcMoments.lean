import LongTails.Algorithms.StochasticQuasarMlmc
import Mathlib.Algebra.Field.GeomSum

open MeasureTheory
open scoped BigOperators ENNReal

namespace OracleTemplate.StochasticQuasar

lemma mlmc_normalizer_pos (m : ℕ) : 0 < ∑ j : Fin (m + 1), (1 / 4 : ℝ) ^ j.val := by
  exact Finset.sum_pos (fun _ _ => by positivity) Finset.univ_nonempty

lemma mlmc_weight_pos (m : ℕ) (j : Fin (m + 1)) : 0 < mlmcWeight m j := by
  unfold mlmcWeight
  exact div_pos (by positivity) (mlmc_normalizer_pos m)

lemma mlmc_weight_sum (m : ℕ) : ∑ j : Fin (m + 1), mlmcWeight m j = 1 := by
  simp only [mlmcWeight, ← Finset.sum_div]
  exact div_self (mlmc_normalizer_pos m).ne'

lemma mlmc_level_probability (m : ℕ) (j : Fin (m + 1)) :
    (mlmcLevelPMF m j).toReal = mlmcWeight m j := by
  change (ENNReal.ofReal ((1 / 4 : ℝ) ^ j.val) *
    (∑' i : Fin (m + 1), ENNReal.ofReal ((1 / 4 : ℝ) ^ i.val))⁻¹).toReal = _
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (mlmc_normalizer_pos m).le]
  rfl

lemma mlmc_normalizer_formula (m : ℕ) :
    (∑ j : Fin (m + 1), (1 / 4 : ℝ) ^ j.val) =
      (4 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ (m + 1)) := by
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
  ring

lemma mlmc_normalizer_bounds (m : ℕ) :
    1 ≤ (∑ j : Fin (m + 1), (1 / 4 : ℝ) ^ j.val) ∧
      (∑ j : Fin (m + 1), (1 / 4 : ℝ) ^ j.val) ≤ 4 / 3 := by
  constructor
  · calc
      1 = (1 / 4 : ℝ) ^ (0 : Fin (m + 1)).val := by simp
      _ ≤ _ := Finset.single_le_sum (f := fun j : Fin (m + 1) => (1 / 4 : ℝ) ^ j.val)
        (fun _ _ => by positivity) (Finset.mem_univ (0 : Fin (m + 1)))
  · rw [mlmc_normalizer_formula]
    have hn : 0 ≤ (1 / 4 : ℝ) ^ (m + 1) := by positivity
    linarith

lemma mlmc_inverse_weight_sum (m : ℕ) :
    (∑ j : Fin (m + 1), (mlmcWeight m j)⁻¹ * (1 / 4 : ℝ) ^ (j.val + 1)) =
      (m + 1 : ℝ) / 4 * (∑ j : Fin (m + 1), (1 / 4 : ℝ) ^ j.val) := by
  have he (j : Fin (m + 1)) :
      (mlmcWeight m j)⁻¹ * (1 / 4 : ℝ) ^ (j.val + 1) =
      (1 / 4 : ℝ) * (∑ i : Fin (m + 1), (1 / 4 : ℝ) ^ i.val) := by
    unfold mlmcWeight
    rw [inv_div, pow_succ]
    have hn : (1 / 4 : ℝ) ^ j.val ≠ 0 := by positivity
    field_simp
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  ring

lemma mlmc_inverse_weight_bound (m : ℕ) :
    (∑ j : Fin (m + 1), (mlmcWeight m j)⁻¹ * (1 / 4 : ℝ) ^ (j.val + 1)) ≤
      (m + 1 : ℝ) / 3 := by
  rw [mlmc_inverse_weight_sum]
  have hh := mul_le_mul_of_nonneg_left (mlmc_normalizer_bounds m).2
    (by positivity : 0 ≤ (m + 1 : ℝ) / 4)
  nlinarith

lemma mlmc_second_weight_bound (m : ℕ) (r : ℝ) :
    (∑ j : Fin (m + 1), mlmcWeight m j *
      (2 * r ^ 2 + 20 * ((mlmcWeight m j)⁻¹) ^ 2 * r ^ 2 * (1 / 4 : ℝ) ^ (j.val + 1))) ≤
      10 * (m + 1 : ℝ) * r ^ 2 := by
  have he (j : Fin (m + 1)) : mlmcWeight m j *
      (2 * r ^ 2 + 20 * ((mlmcWeight m j)⁻¹) ^ 2 * r ^ 2 * (1 / 4 : ℝ) ^ (j.val + 1)) =
      2 * r ^ 2 * mlmcWeight m j +
        20 * r ^ 2 * ((mlmcWeight m j)⁻¹ * (1 / 4 : ℝ) ^ (j.val + 1)) := by
    have hp := (mlmc_weight_pos m j).ne'
    field_simp
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, mlmc_weight_sum, mul_one]
  have hh := mul_le_mul_of_nonneg_left (mlmc_inverse_weight_bound m) (by positivity : 0 ≤ 20 * r ^ 2)
  have hn : 0 ≤ (m : ℝ) * r ^ 2 := by positivity
  nlinarith [sq_nonneg r]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma mlmc_finite_telescope (m : ℕ) (a : ℕ → E) :
    (∫ j, a 0 + (mlmcWeight m j)⁻¹ • (a (j.val + 1) - a j.val)
      ∂(mlmcLevelLaw m : Measure (Fin (m + 1)))) = a (m + 1) := by
  change (∫ j, a 0 + (mlmcWeight m j)⁻¹ • (a (j.val + 1) - a j.val)
    ∂(mlmcLevelPMF m).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp_rw [mlmc_level_probability]
  have he (j : Fin (m + 1)) :
      mlmcWeight m j • (a 0 + (mlmcWeight m j)⁻¹ • (a (j.val + 1) - a j.val)) =
      mlmcWeight m j • a 0 + (a (j.val + 1) - a j.val) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ (mlmc_weight_pos m j).ne', one_smul]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, mlmc_weight_sum, one_smul,
    Fin.sum_univ_eq_sum_range (fun j => a (j + 1) - a j) (m + 1), Finset.sum_range_sub]
  abel

omit [CompleteSpace E] in
lemma mlmc_value_squared (base upper lower v : E) (w : ℝ) :
    ‖base + w⁻¹ • (upper - lower) - v‖ ^ 2 ≤
      2 * ‖base - v‖ ^ 2 + 4 * (w⁻¹) ^ 2 * (‖upper - v‖ ^ 2 + ‖lower - v‖ ^ 2) := by
  have hd : ‖upper - lower‖ ≤ ‖upper - v‖ + ‖lower - v‖ := by
    calc
      ‖upper - lower‖ = ‖(upper - v) + (v - lower)‖ := by congr 1; abel
      _ ≤ ‖upper - v‖ + ‖v - lower‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev v lower]
  have hd2 : ‖upper - lower‖ ^ 2 ≤ 2 * (‖upper - v‖ ^ 2 + ‖lower - v‖ ^ 2) := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hd 2
    nlinarith [sq_nonneg (‖upper - v‖ - ‖lower - v‖)]
  have he : base + w⁻¹ • (upper - lower) - v = (base - v) + w⁻¹ • (upper - lower) := by abel
  rw [he]
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (base - v) (w⁻¹ • (upper - lower))) 2
  have ha := sq_nonneg (‖base - v‖ - ‖w⁻¹ • (upper - lower)‖)
  have hs : ‖w⁻¹ • (upper - lower)‖ ^ 2 = (w⁻¹) ^ 2 * ‖upper - lower‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hm := mul_le_mul_of_nonneg_left hd2 (sq_nonneg w⁻¹)
  nlinarith

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma mlmc_random_mean (m : ℕ) (a : ℕ → E) (base : Ω → E)
    (upper lower : Fin (m + 1) → Ω → E)
    (hb : Measurable base) (hu : ∀ j, Measurable (upper j)) (hl : ∀ j, Measurable (lower j))
    (hbi : Integrable base μ) (hui : ∀ j, Integrable (upper j) μ)
    (hli : ∀ j, Integrable (lower j) μ)
    (hbm : (∫ ω, base ω ∂μ) = a 0)
    (hum : ∀ j, (∫ ω, upper j ω ∂μ) = a (j.val + 1))
    (hlm : ∀ j, (∫ ω, lower j ω ∂μ) = a j.val) :
    let Z := fun w : Fin (m + 1) × Ω => base w.2 +
      (mlmcWeight m w.1)⁻¹ • (upper w.1 w.2 - lower w.1 w.2)
    Integrable Z ((mlmcLevelLaw m : Measure _).prod μ) ∧
      (∫ w, Z w ∂((mlmcLevelLaw m : Measure _).prod μ)) = a (m + 1) := by
  dsimp only
  let Z := fun w : Fin (m + 1) × Ω => base w.2 +
    (mlmcWeight m w.1)⁻¹ • (upper w.1 w.2 - lower w.1 w.2)
  have hZm : Measurable Z := by
    apply measurable_from_prod_countable_right
    intro j
    exact hb.add (((hu j).sub (hl j)).const_smul (mlmcWeight m j)⁻¹)
  have hZi (j : Fin (m + 1)) : Integrable (fun ω => Z (j, ω)) μ :=
    hbi.add (((hui j).sub (hli j)).smul (mlmcWeight m j)⁻¹)
  have hi : Integrable Z ((mlmcLevelLaw m : Measure _).prod μ) := by
    apply (integrable_prod_iff hZm.aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall hZi, Integrable.of_finite⟩
  refine ⟨hi, ?_⟩
  change (∫ w, Z w ∂((mlmcLevelLaw m : Measure _).prod μ)) = _
  rw [integral_prod _ hi]
  have he (j : Fin (m + 1)) : (∫ ω, Z (j, ω) ∂μ) =
      a 0 + (mlmcWeight m j)⁻¹ • (a (j.val + 1) - a j.val) := by
    dsimp [Z]
    have hadd := integral_add hbi (((hui j).sub (hli j)).smul (mlmcWeight m j)⁻¹)
    simp only [Pi.smul_apply, Pi.sub_apply] at hadd
    rw [hadd, integral_smul,
      integral_sub (hui j) (hli j), hbm, hum, hlm]
  simp_rw [he]
  exact mlmc_finite_telescope m a

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
lemma mlmc_fixed_second (base upper lower : Ω → E) (v : E) (w : ℝ)
    (hb : Measurable base) (hu : Measurable upper) (hl : Measurable lower)
    (hbi : Integrable (fun ω => ‖base ω - v‖ ^ 2) μ)
    (hui : Integrable (fun ω => ‖upper ω - v‖ ^ 2) μ)
    (hli : Integrable (fun ω => ‖lower ω - v‖ ^ 2) μ) :
    Integrable (fun ω => ‖base ω + w⁻¹ • (upper ω - lower ω) - v‖ ^ 2) μ ∧
      (∫ ω, ‖base ω + w⁻¹ • (upper ω - lower ω) - v‖ ^ 2 ∂μ) ≤
        2 * (∫ ω, ‖base ω - v‖ ^ 2 ∂μ) + 4 * (w⁻¹) ^ 2 *
          ((∫ ω, ‖upper ω - v‖ ^ 2 ∂μ) + (∫ ω, ‖lower ω - v‖ ^ 2 ∂μ)) := by
  let Z := fun ω => ‖base ω + w⁻¹ • (upper ω - lower ω) - v‖ ^ 2
  let B := fun ω => 2 * ‖base ω - v‖ ^ 2 +
    4 * (w⁻¹) ^ 2 * (‖upper ω - v‖ ^ 2 + ‖lower ω - v‖ ^ 2)
  have hZm : Measurable Z :=
    ((hb.add ((hu.sub hl).const_smul w⁻¹)).sub measurable_const).norm.pow_const 2
  have hBi : Integrable B μ := (hbi.const_mul 2).add ((hui.add hli).const_mul (4 * (w⁻¹) ^ 2))
  have hpt (ω : Ω) : Z ω ≤ B ω := mlmc_value_squared _ _ _ _ _
  have hZi : Integrable Z μ := by
    apply hBi.mono' hZm.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hZi, ?_⟩
  have hh := integral_mono hZi hBi hpt
  have hadd := integral_add (hbi.const_mul 2) ((hui.add hli).const_mul (4 * (w⁻¹) ^ 2))
  have hsum := integral_add hui hli
  simp only [Pi.add_apply] at hadd hsum
  dsimp [B] at hh
  rw [hadd, integral_const_mul, integral_const_mul, hsum] at hh
  exact hh

omit [CompleteSpace E] in
lemma mlmc_random_second (m : ℕ) (r : ℝ) (v : E) (base : Ω → E)
    (upper lower : Fin (m + 1) → Ω → E)
    (hb : Measurable base) (hu : ∀ j, Measurable (upper j)) (hl : ∀ j, Measurable (lower j))
    (hbi : Integrable (fun ω => ‖base ω - v‖ ^ 2) μ)
    (hui : ∀ j, Integrable (fun ω => ‖upper j ω - v‖ ^ 2) μ)
    (hli : ∀ j, Integrable (fun ω => ‖lower j ω - v‖ ^ 2) μ)
    (hbb : (∫ ω, ‖base ω - v‖ ^ 2 ∂μ) ≤ r ^ 2)
    (hub : ∀ j, (∫ ω, ‖upper j ω - v‖ ^ 2 ∂μ) ≤ r ^ 2 * (1 / 4 : ℝ) ^ (j.val + 1))
    (hlb : ∀ j, (∫ ω, ‖lower j ω - v‖ ^ 2 ∂μ) ≤ r ^ 2 * (1 / 4 : ℝ) ^ j.val) :
    let Z := fun w : Fin (m + 1) × Ω => base w.2 +
      (mlmcWeight m w.1)⁻¹ • (upper w.1 w.2 - lower w.1 w.2)
    Integrable (fun w => ‖Z w - v‖ ^ 2) ((mlmcLevelLaw m : Measure _).prod μ) ∧
      (∫ w, ‖Z w - v‖ ^ 2 ∂((mlmcLevelLaw m : Measure _).prod μ)) ≤ 10 * (m + 1 : ℝ) * r ^ 2 := by
  dsimp only
  let Z := fun w : Fin (m + 1) × Ω => base w.2 +
    (mlmcWeight m w.1)⁻¹ • (upper w.1 w.2 - lower w.1 w.2)
  have hZm : Measurable Z := by
    apply measurable_from_prod_countable_right
    intro j
    exact hb.add (((hu j).sub (hl j)).const_smul (mlmcWeight m j)⁻¹)
  have hf (j : Fin (m + 1)) := mlmc_fixed_second base (upper j) (lower j) v (mlmcWeight m j)
    hb (hu j) (hl j) hbi (hui j) (hli j)
  have hZi (j : Fin (m + 1)) : Integrable (fun ω => ‖Z (j, ω) - v‖ ^ 2) μ := (hf j).1
  have hi : Integrable (fun w => ‖Z w - v‖ ^ 2) ((mlmcLevelLaw m : Measure _).prod μ) := by
    apply (integrable_prod_iff ((hZm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall hZi, Integrable.of_finite⟩
  have hc (j : Fin (m + 1)) : (∫ ω, ‖Z (j, ω) - v‖ ^ 2 ∂μ) ≤
      2 * r ^ 2 + 20 * ((mlmcWeight m j)⁻¹) ^ 2 * r ^ 2 * (1 / 4 : ℝ) ^ (j.val + 1) := by
    have hh := (hf j).2.trans (add_le_add (mul_le_mul_of_nonneg_left hbb (by norm_num))
      (mul_le_mul_of_nonneg_left (add_le_add (hub j) (hlb j)) (by positivity)))
    have he : (1 / 4 : ℝ) ^ j.val = 4 * (1 / 4 : ℝ) ^ (j.val + 1) := by rw [pow_succ]; ring
    convert hh using 1
    rw [he]
    ring
  refine ⟨hi, ?_⟩
  change (∫ w, ‖Z w - v‖ ^ 2 ∂((mlmcLevelLaw m : Measure _).prod μ)) ≤ _
  rw [integral_prod _ hi]
  change (∫ j, (∫ ω, ‖Z (j, ω) - v‖ ^ 2 ∂μ) ∂(mlmcLevelPMF m).toMeasure) ≤ _
  rw [PMF.integral_eq_sum]
  simp only [mlmc_level_probability, smul_eq_mul]
  exact (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hc j) (mlmc_weight_pos m j).le)).trans
    (mlmc_second_weight_bound m r)

end OracleTemplate.StochasticQuasar
