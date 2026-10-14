import LongTails.Proofs.GapStrongGrowthMoments
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma exp_integral_le_one {U : Ω → ℝ} (hU : Measurable U)
    (hi : Integrable U P) (h2 : Integrable (fun ω => (U ω) ^ 2) P)
    {t : ℝ} (hbound : ∀ ω, |t * U ω| ≤ 1)
    (hmean : t * (∫ ω, U ω ∂P) + t ^ 2 * (∫ ω, (U ω) ^ 2 ∂P) ≤ 0) :
    Integrable (fun ω => Real.exp (t * U ω)) P ∧
      (∫ ω, Real.exp (t * U ω) ∂P) ≤ 1 := by
  have ht (ω) : Real.exp (t * U ω) ≤ 1 + t * U ω + t ^ 2 * (U ω) ^ 2 := by
    have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hbound ω))).2
    nlinarith only [hh]
  have hr : Integrable (fun ω => 1 + t * U ω + t ^ 2 * (U ω) ^ 2) P :=
    ((integrable_const 1).add (hi.const_mul t)).add (h2.const_mul (t ^ 2))
  have he : Integrable (fun ω => Real.exp (t * U ω)) P := hr.mono'
    (Real.measurable_exp.comp (hU.const_mul t)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact ht ω)
  refine ⟨he, ?_⟩
  have hh := integral_mono he hr ht
  have hlin : Integrable (fun ω => 1 + t * U ω) P := (integrable_const 1).add (hi.const_mul t)
  rw [integral_add hlin (h2.const_mul _),
    integral_add (integrable_const 1) (hi.const_mul t)] at hh
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul] at hh
  linarith

lemma exponential_drift_arithmetic {q a G R : ℝ} (hq : 1 ≤ q) (hR : 0 < R)
    {m v : ℝ} (hm : m ≤ -11 * q * a ^ 2 * G ^ 2)
    (hv : v ≤ 320 * a ^ 2 * R ^ 2 * G ^ 2) :
    (q / (64 * R ^ 2)) * m + (q / (64 * R ^ 2)) ^ 2 * v ≤ 0 := by
  have hq0 : 0 ≤ q := by linarith
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hm' := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ q / (64 * R ^ 2) by positivity)
  have hv' := mul_le_mul_of_nonneg_left hv (sq_nonneg (q / (64 * R ^ 2)))
  have hs : (q / (64 * R ^ 2)) * (-11 * q * a ^ 2 * G ^ 2) +
      (q / (64 * R ^ 2)) ^ 2 * (320 * a ^ 2 * R ^ 2 * G ^ 2) ≤ 0 := by
    field_simp
    nlinarith only [sq_nonneg (a * G * q)]
  linarith

lemma exponential_drift {U : Ω → ℝ} (hU : Measurable U)
    (hi : Integrable U P) (h2 : Integrable (fun ω => (U ω) ^ 2) P)
    {q a G R : ℝ} (hq : 1 ≤ q) (hR : 0 < R)
    (hbound : ∀ ω, |U ω| ≤ 7 * R ^ 2 / q)
    (hmean : (∫ ω, U ω ∂P) ≤ -11 * q * a ^ 2 * G ^ 2)
    (hmoment : (∫ ω, (U ω) ^ 2 ∂P) ≤ 320 * a ^ 2 * R ^ 2 * G ^ 2) :
    Integrable (fun ω => Real.exp (q / (64 * R ^ 2) * U ω)) P ∧
      (∫ ω, Real.exp (q / (64 * R ^ 2) * U ω) ∂P) ≤ 1 := by
  have hq0 : 0 < q := by linarith
  apply exp_integral_le_one hU hi h2
  · intro ω
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ q / (64 * R ^ 2))]
    calc
      _ ≤ q / (64 * R ^ 2) * (7 * R ^ 2 / q) :=
        mul_le_mul_of_nonneg_left (hbound ω) (by positivity)
      _ ≤ 1 := by field_simp; norm_num
  · exact exponential_drift_arithmetic hq hR hmean hmoment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma confidence_bias_absorbed {a R q : ℝ} (ha : 0 ≤ a) (hR : 0 < R)
    (hq : 1 ≤ q) (g e z : E) (hz : ‖z‖ ≤ 4 * R)
    (he : ‖e‖ ≤ 4 * q * a * ‖g‖ ^ 2 / R)
    (hsmall : 512 * q * a * ‖g‖ ≤ 3 * R) :
    -32 * q * a ^ 2 * ⟪g, g + e⟫ + a ^ 2 * (4 * ‖g‖ ^ 2) + a * ⟪-e, z⟫ ≤
      -11 * q * a ^ 2 * ‖g‖ ^ 2 := by
  have hq0 : 0 ≤ q := by linarith
  have he' := (le_div_iff₀ hR).mp he
  have hi := real_inner_le_norm g (-e)
  simp only [inner_neg_right, norm_neg] at hi
  have hz' := (real_inner_le_norm (-e) z).trans
    (mul_le_mul_of_nonneg_left hz (norm_nonneg (-e)))
  simp only [norm_neg] at hz'
  have hi' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 32 * q * a ^ 2 by positivity)
  have hz'' := mul_le_mul_of_nonneg_left hz' ha
  have hsm := mul_le_mul_of_nonneg_right hsmall (norm_nonneg e)
  have hh : 32 * q * a * ‖g‖ * ‖e‖ + 4 * R * ‖e‖ ≤ 17 * q * a * ‖g‖ ^ 2 := by
    nlinarith only [he', hsm, mul_nonneg (mul_nonneg hq0 ha) (sq_nonneg ‖g‖)]
  have hh' := mul_le_mul_of_nonneg_left hh ha
  have hq' := mul_le_mul_of_nonneg_right hq (mul_nonneg (sq_nonneg a) (sq_nonneg ‖g‖))
  rw [inner_add_right, real_inner_self_eq_norm_sq]
  nlinarith only [hi', hz'', hh', hq']

lemma confidence_increment_abs {a R q : ℝ} (ha : 0 ≤ a)
    (hq : 1 ≤ q) (g h z : E) (hz : ‖z‖ ≤ 4 * R)
    (hh : q * a * ‖h‖ ≤ R) (hg : 32 * q * a * ‖g‖ ≤ R) :
    |-32 * q * a ^ 2 * ⟪g, h⟫ + a ^ 2 * ‖h‖ ^ 2 + a * ⟪g - h, z⟫| ≤
      4 * a * R * ‖g‖ + 6 * a * R * ‖h‖ := by
  have hq0 : 0 ≤ q := by linarith
  have hbase : a * ‖h‖ ≤ R := by
    have := mul_le_mul_of_nonneg_right hq (mul_nonneg ha (norm_nonneg h))
    nlinarith only [this, hh]
  have hg' := mul_le_mul_of_nonneg_right hg (mul_nonneg ha (norm_nonneg h))
  have hh' := mul_le_mul_of_nonneg_right hbase (mul_nonneg ha (norm_nonneg h))
  have hgh : ‖g - h‖ ≤ ‖g‖ + ‖h‖ := norm_sub_le _ _
  have hi := abs_real_inner_le_norm g h
  have hz' := (abs_real_inner_le_norm (g - h) z).trans
    (mul_le_mul hgh hz (norm_nonneg _) (by positivity))
  have hi' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 32 * q * a ^ 2 by positivity)
  have hz'' := mul_le_mul_of_nonneg_left hz' ha
  calc
    _ ≤ |-32 * q * a ^ 2 * ⟪g, h⟫| + |a ^ 2 * ‖h‖ ^ 2| + |a * ⟪g - h, z⟫| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = 32 * q * a ^ 2 * |⟪g, h⟫| + a ^ 2 * ‖h‖ ^ 2 + a * |⟪g - h, z⟫| := by
      norm_num [abs_mul, abs_of_nonneg ha, abs_of_nonneg (sq_nonneg a),
        abs_of_nonneg (sq_nonneg ‖h‖), abs_of_nonneg hq0]
    _ ≤ _ := by nlinarith only [hi', hz'', hg', hh']

lemma confidence_increment_square {a R G H U : ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hU : |U| ≤ 4 * a * R * G + 6 * a * R * H) :
    U ^ 2 ≤ 32 * a ^ 2 * R ^ 2 * G ^ 2 + 72 * a ^ 2 * R ^ 2 * H ^ 2 := by
  have hs := sq_le_sq₀ (abs_nonneg U) (by positivity : 0 ≤ 4 * a * R * G + 6 * a * R * H)
  have ht := hs.mpr hU
  rw [sq_abs] at ht
  nlinarith only [ht, sq_nonneg (4 * a * R * G - 6 * a * R * H)]

noncomputable def energyIncrement (q a : ℝ) (g z h : E) : ℝ :=
  -32 * q * a ^ 2 * ⟪g, h⟫ + a ^ 2 * ‖h‖ ^ 2 + a * ⟪g - h, z⟫

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
lemma clipped_exponential_step {h : Ω → E} (hm : Measurable h)
    (hi : Integrable h P) (h2 : Integrable (fun ω => ‖h ω‖ ^ 2) P)
    {g z : E} {a R q : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (hq : 1 ≤ q)
    (hz : ‖z‖ ≤ 4 * R)
    (hbias : ‖(∫ ω, h ω ∂P) - g‖ ≤ 4 * q * a * ‖g‖ ^ 2 / R)
    (hmoment : (∫ ω, ‖h ω‖ ^ 2 ∂P) ≤ 4 * ‖g‖ ^ 2)
    (hsmall : 512 * q * a * ‖g‖ ≤ 3 * R)
    (hclip : ∀ ω, q * a * ‖h ω‖ ≤ R) :
    Integrable (fun ω => Real.exp (q / (64 * R ^ 2) * energyIncrement q a g z (h ω))) P ∧
      (∫ ω, Real.exp (q / (64 * R ^ 2) * energyIncrement q a g z (h ω)) ∂P) ≤ 1 := by
  let U := fun ω => energyIncrement q a g z (h ω)
  have hq0 : 0 < q := by linarith
  have hsmall' : 32 * q * a * ‖g‖ ≤ R := by linarith
  have hUm : Measurable U := by
    dsimp [U, energyIncrement]
    fun_prop
  have hdes : Integrable (fun ω => -32 * q * a ^ 2 * ⟪g, h ω⟫) P :=
    (hi.const_inner g).const_mul _
  have hvar : Integrable (fun ω => a ^ 2 * ‖h ω‖ ^ 2) P := h2.const_mul _
  have hdiff : Integrable (fun ω => g - h ω) P := (integrable_const g).sub hi
  have hnoise : Integrable (fun ω => a * ⟪g - h ω, z⟫) P := (hdiff.inner_const z).const_mul _
  have hbase : Integrable (fun ω => -32 * q * a ^ 2 * ⟪g, h ω⟫ + a ^ 2 * ‖h ω‖ ^ 2) P :=
    hdes.add hvar
  have hUi : Integrable U P := hbase.add hnoise
  have hn : (∫ ω, ⟪g - h ω, z⟫ ∂P) = ⟪g - (∫ ω, h ω ∂P), z⟫ := by
    calc
      _ = ∫ ω, ⟪z, g - h ω⟫ ∂P := integral_congr_ae
        (Filter.Eventually.of_forall fun ω => real_inner_comm _ _)
      _ = ⟪z, g - (∫ ω, h ω ∂P)⟫ := by
        rw [integral_inner hdiff z, integral_sub (integrable_const g) hi]
        simp
      _ = _ := real_inner_comm _ _
  have hmean : (∫ ω, U ω ∂P) ≤ -11 * q * a ^ 2 * ‖g‖ ^ 2 := by
    dsimp [U, energyIncrement]
    rw [integral_add hbase hnoise, integral_add hdes hvar]
    simp only [integral_const_mul]
    rw [integral_inner hi g, hn]
    have he := confidence_bias_absorbed ha hR hq g ((∫ ω, h ω ∂P) - g) z hz hbias hsmall
    have he1 : g + ((∫ ω, h ω ∂P) - g) = ∫ ω, h ω ∂P := by module
    have he2 : -((∫ ω, h ω ∂P) - g) = g - (∫ ω, h ω ∂P) := by module
    rw [he1, he2] at he
    have hv := mul_le_mul_of_nonneg_left hmoment (sq_nonneg a)
    linarith
  have hUa (ω) : |U ω| ≤ 4 * a * R * ‖g‖ + 6 * a * R * ‖h ω‖ :=
    confidence_increment_abs ha hq g (h ω) z hz (hclip ω) hsmall'
  have hUb (ω) : |U ω| ≤ 7 * R ^ 2 / q := by
    apply (le_div_iff₀ hq0).mpr
    have hu := mul_le_mul_of_nonneg_right (hUa ω) hq0.le
    have hc := mul_le_mul_of_nonneg_right (hclip ω) (show 0 ≤ 6 * R by positivity)
    have hg := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ R by positivity)
    nlinarith only [hu, hc, hg, sq_nonneg R]
  have hUs (ω) : (U ω) ^ 2 ≤ 32 * a ^ 2 * R ^ 2 * ‖g‖ ^ 2 +
      72 * a ^ 2 * R ^ 2 * ‖h ω‖ ^ 2 :=
    confidence_increment_square ha hR.le (norm_nonneg _) (norm_nonneg _) (hUa ω)
  have hsint : Integrable (fun ω => 32 * a ^ 2 * R ^ 2 * ‖g‖ ^ 2 +
      72 * a ^ 2 * R ^ 2 * ‖h ω‖ ^ 2) P :=
    (integrable_const _).add (h2.const_mul _)
  have hU2 : Integrable (fun ω => (U ω) ^ 2) P := hsint.mono'
    (hUm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hUs ω)
  have hsecond : (∫ ω, (U ω) ^ 2 ∂P) ≤ 320 * a ^ 2 * R ^ 2 * ‖g‖ ^ 2 := by
    have hh := integral_mono hU2 hsint hUs
    rw [integral_add (integrable_const _) (h2.const_mul _)] at hh
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul] at hh
    have hv := mul_le_mul_of_nonneg_left hmoment (show 0 ≤ 72 * a ^ 2 * R ^ 2 by positivity)
    nlinarith only [hh, hv]
  exact exponential_drift hUm hUi hU2 hq hR hUb hmean hsecond

end OracleTemplate.GapStrongGrowth
