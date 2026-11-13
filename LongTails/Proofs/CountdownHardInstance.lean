import LongTails.Proofs.CountdownCalibration
import LongTails.Proofs.QuantileOracleLowerBound
import LongTails.Setups.StretchedExponentialMarkovConvex

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.CountdownHardInstance

open CountdownMarkov LongTails.Proofs.QuantileOracleLowerBound

lemma common_mass (H : ℕ) (q : ℝ) (hH : 0 < H) (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    1 / (1 + H * (calibratedJump H q hH hq hq1 : ℝ)) = 1 - q := by
  have hm := calibratedJump_mass H q hH hq hq1
  have hp := (calibratedJump H q hH hq hq1).property.1
  have hd : 1 + H * (calibratedJump H q hH hq hq1 : ℝ) ≠ 0 := by positivity
  have he : 1 / (1 + H * (calibratedJump H q hH hq hq1 : ℝ)) +
      H * (calibratedJump H q hH hq hq1 : ℝ) /
        (1 + H * (calibratedJump H q hH hq hq1 : ℝ)) = 1 := by field_simp
  linarith

lemma integral_common_rare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (H : ℕ) (q : ℝ) (hH : 0 < H) (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (a b : E) :
    (∫ z : ℝ, (if z = 0 then a else b)
      ∂stationaryMeasure H (calibratedJump H q hH hq hq1)) = (1 - q) • a + q • b := by
  rw [integral_stationary_split]
  have hn (i : Fin H) : (i.val : ℝ) + 1 ≠ 0 := by positivity
  simp only [↓reduceIte, hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [common_mass]
  have he : (calibratedJump H q hH hq hq1 : ℝ) /
      (1 + H * (calibratedJump H q hH hq hq1 : ℝ)) * H = q := by
    rw [calibratedJump_entry]
    exact div_mul_cancel₀ _ (by positivity)
  rw [he]

lemma rare_moment_weight (q α : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hα : 1 ≤ α) :
    q * (q⁻¹ - 1) ^ α + (1 - q) ≤ 2 * q ^ (1 - α) := by
  have hinv : 1 ≤ q⁻¹ := (one_le_inv₀ hq).2 hq1
  have hb := Real.rpow_le_rpow (by linarith : 0 ≤ q⁻¹ - 1)
    (by linarith : q⁻¹ - 1 ≤ q⁻¹) (by linarith : 0 ≤ α)
  have he : q * (q⁻¹) ^ α = q ^ (1 - α) := by
    rw [Real.inv_rpow hq.le, ← Real.rpow_neg hq.le]
    calc
      q * q ^ (-α) = q ^ (1 : ℝ) * q ^ (-α) := by rw [Real.rpow_one]
      _ = q ^ (1 - α) := by rw [← Real.rpow_add hq]; congr 1
  have ho := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq hq1
    (by linarith : 1 - α ≤ 0)
  have hm := mul_le_mul_of_nonneg_left hb hq.le
  rw [he] at hm
  linarith

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def objective (μ : ℝ) (x0 c : E) : E → ℝ :=
  centeredQuadratic μ (x0 + c)

noncomputable def reply (μ q : ℝ) (x0 c x : E) (z : ℝ) : E :=
  μ • (x - x0) - if z = 0 then 0 else q⁻¹ • (μ • c)

lemma objective_gradient (μ : ℝ) (x0 c x : E) :
    HasGradientAt (objective μ x0 c) (μ • (x - x0) - μ • c) x := by
  have h := centeredQuadratic_gradient μ (x0 + c) x
  simpa only [objective, sub_add_eq_sub_sub, smul_sub] using h

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma objective_min {μ : ℝ} (hμ : 0 ≤ μ) (x0 c : E) :
    IsMinOn (objective μ x0 c) Set.univ (x0 + c) := centeredQuadratic_min hμ _

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma objective_at_center (μ : ℝ) (x0 c : E) : objective μ x0 c (x0 + c) = 0 := by
  simp [objective, centeredQuadratic]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma objective_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (x0 c x : E) : 0 ≤ objective μ x0 c x := by
  exact mul_nonneg (div_nonneg hμ (by norm_num)) (sq_nonneg _)

omit [CompleteSpace E] in
lemma objective_pair_lower {μ : ℝ} (hμ : 0 ≤ μ) (x0 c x : E) :
    μ * ‖c‖ ^ 2 ≤ objective μ x0 c x + objective μ x0 (-c) x := by
  unfold objective centeredQuadratic
  have he : x - (x0 + c) = (x - x0) - c := by abel
  have he' : x - (x0 + -c) = (x - x0) + c := by abel
  rw [he, he', norm_sub_sq_real, norm_add_sq_real]
  nlinarith [mul_nonneg hμ (sq_nonneg ‖x - x0‖)]

omit [CompleteSpace E] in
lemma reply_common (μ q : ℝ) (x0 c x : E) : reply μ q x0 c x 0 = μ • (x - x0) := by
  simp [reply]

lemma reply_mean (μ q : ℝ) (x0 c x : E) (H : ℕ) (hH : 0 < H)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) :
    (∫ z, reply μ q x0 c x z ∂stationaryMeasure H (calibratedJump H q hH hq.le hq1)) =
      gradient (objective μ x0 c) x := by
  have he : reply μ q x0 c x = fun z =>
      if z = 0 then μ • (x - x0) else μ • (x - x0) - q⁻¹ • (μ • c) := by
    funext z
    simp only [reply]
    split_ifs <;> simp
  rw [he, integral_common_rare, (objective_gradient μ x0 c x).gradient]
  have hi : q • (q⁻¹ • (μ • c)) = μ • c := by
    rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
  calc
    _ = μ • (x - x0) - q • (q⁻¹ • (μ • c)) := by module
    _ = _ := by rw [hi]

lemma reply_error (μ q : ℝ) (x0 c x : E) (z : ℝ) :
    reply μ q x0 c x z - gradient (objective μ x0 c) x =
      if z = 0 then μ • c else (1 - q⁻¹) • (μ • c) := by
  rw [(objective_gradient μ x0 c x).gradient]
  unfold reply
  split_ifs
  · abel
  · rw [sub_smul, one_smul]
    abel

omit [CompleteSpace E] in
lemma reply_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (μ q : ℝ) (x0 c : E) :
    Measurable (Function.uncurry (reply μ q x0 c)) := by
  have hi : Measurable (fun z : ℝ => if z = 0 then (0 : E) else q⁻¹ • (μ • c)) :=
    Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const
  change Measurable (fun a : E × ℝ => μ • (a.1 - x0) -
    (if a.2 = 0 then 0 else q⁻¹ • (μ • c)))
  exact (measurable_const.smul (measurable_fst.sub_const x0)).sub (hi.comp measurable_snd)

lemma reply_moment (μ q α : ℝ) (x0 c x : E) (H : ℕ) (hH : 0 < H)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) (hα : 1 ≤ α) :
    (∫ z, ‖reply μ q x0 c x z - gradient (objective μ x0 c) x‖ ^ α
      ∂stationaryMeasure H (calibratedJump H q hH hq.le hq1)) ≤
      2 * q ^ (1 - α) * ‖μ • c‖ ^ α := by
  have he : (fun z => ‖reply μ q x0 c x z - gradient (objective μ x0 c) x‖ ^ α) =
      fun z => if z = 0 then ‖μ • c‖ ^ α else ‖(1 - q⁻¹) • (μ • c)‖ ^ α := by
    funext z
    rw [reply_error]
    split_ifs <;> rfl
  have hinv : 1 ≤ q⁻¹ := (one_le_inv₀ hq).2 (by linarith)
  have habs : |1 - q⁻¹| = q⁻¹ - 1 := by rw [abs_of_nonpos (by linarith)]; ring
  rw [he, integral_common_rare]
  simp only [smul_eq_mul]
  rw [norm_smul (1 - q⁻¹) (μ • c), Real.norm_eq_abs, habs,
    Real.mul_rpow (by linarith : 0 ≤ q⁻¹ - 1) (norm_nonneg _)]
  calc
    _ = (q * (q⁻¹ - 1) ^ α + (1 - q)) * ‖μ • c‖ ^ α := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (rare_moment_weight q α hq (by linarith) hα)
      (Real.rpow_nonneg (norm_nonneg _) _)

end Geometry

end OracleTemplate.CountdownHardInstance
