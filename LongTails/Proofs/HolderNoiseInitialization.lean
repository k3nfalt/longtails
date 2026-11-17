import LongTails.Proofs.FullGeneralizedSmoothZeroQuery
import LongTails.Proofs.HolderNoiseHardOracle
import LongTails.Proofs.HolderNoiseHardAdmissible

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseInitialization

open HolderNoiseHardOracle QuasarCoinLaw

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def objective (L : ℝ) (u x0 x : E) : ℝ :=
  FullGeneralizedSmoothZeroQuery.quadratic L (x0 + u) x

noncomputable def field (L : ℝ) (u x0 x : E) : E := L • (x - x0 - u)

noncomputable def noise (L : ℝ) (u : E) (_x : E) : E := -(L • u)

lemma objective_gradient (L : ℝ) (u x0 x : E) : HasGradientAt (objective L u x0) (field L u x0 x) x := by
  have h := FullGeneralizedSmoothZeroQuery.quadratic_gradient L (x0 + u) x
  change HasGradientAt (FullGeneralizedSmoothZeroQuery.quadratic L (x0 + u)) (field L u x0 x) x
  simpa only [field, FullGeneralizedSmoothZeroQuery.field, sub_add_eq_sub_sub] using h

omit [CompleteSpace E] in
lemma field_lipschitz {L : ℝ} (hL : 0 ≤ L) (u x0 x y : E) :
    ‖field L u x0 x - field L u x0 y‖ ≤ L * ‖x - y‖ := by
  have he : field L u x0 x - field L u x0 y = L • (x - y) := by unfold field; module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma objective_gap {L : ℝ} (hL : 0 ≤ L) (u x0 x : E) :
    objective L u x0 x0 - objective L u x0 x ≤ L / 2 * ‖u‖ ^ 2 := by
  have hn := FullGeneralizedSmoothZeroQuery.quadratic_nonneg L hL (x0 + u) x
  have he : objective L u x0 x0 = L / 2 * ‖u‖ ^ 2 := by
    simp [objective, FullGeneralizedSmoothZeroQuery.quadratic]
  rw [he]
  change 0 ≤ objective L u x0 x at hn
  linarith

omit [CompleteSpace E] in
lemma oracle_silent (L p : ℝ) (u x0 x : E) :
    oracleValue p (field L u x0) (noise L u) x false = L • (x - x0) := by
  simp only [oracleValue, coinError, Bool.false_eq_true, ite_false, neg_one_smul, noise, neg_neg, field]
  module

omit [CompleteSpace E] in
lemma noise_norm {L : ℝ} (hL : 0 ≤ L) (u x : E) : ‖noise L u x‖ = L * ‖u‖ := by
  simp [noise, norm_smul, abs_of_nonneg hL]

omit [CompleteSpace E] in
lemma field_pair {L : ℝ} (hL : 0 ≤ L) (u x0 x : E) :
    2 * L * ‖u‖ ≤ ‖field L u x0 x‖ + ‖field L (-u) x0 x‖ := by
  have he : field L u x0 x - field L (-u) x0 x = (-2 * L) • u := by unfold field; module
  have hn := norm_sub_le (field L u x0 x) (field L (-u) x0 x)
  rw [he, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL] at hn
  norm_num at hn
  exact hn

omit [CompleteSpace E] in
lemma oracle_variance_le {L p : ℝ} (hL : 0 ≤ L) (hp : 0 < p) (hp1 : p ≤ 1) (u x0 x : E) :
    (∫ b, ‖oracleValue p (field L u x0) (noise L u) x b - field L u x0 x‖ ^ 2
      ∂(coinLaw p hp.le hp1 : Measure Bool)) ≤ L ^ 2 * ‖u‖ ^ 2 / p := by
  have h := HolderNoiseHardOracle.oracle_variance_le hp hp1 (field L u x0) (noise L u) x
    (noise_norm hL u x).le
  simpa only [mul_pow] using h

omit [CompleteSpace E] in
lemma oracle_increment_zero {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (L : ℝ) (u x0 x y : E) :
    (∫ b, ‖(oracleValue p (field L u x0) (noise L u) x b -
      oracleValue p (field L u x0) (noise L u) y b) - (field L u x0 x - field L u x0 y)‖ ^ 2
      ∂(coinLaw p hp.le hp1 : Measure Bool)) = 0 := by
  rw [oracle_increment hp hp1]
  simp [noise]

end LongTails.Proofs.HolderNoiseInitialization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseInitializationAdmissible

open HolderNoiseInitialization HolderNoiseHardOracle HolderNoiseHardAdmissible QuasarCoinLaw
open LongTails.Setups.HolderNoiseNonconvexLower

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma oracle_measurable {d : ℕ} (L p : ℝ) (u x0 : EuclideanSpace ℝ (Fin d)) :
    Measurable (Function.uncurry (oracleValue p (field L u x0) (noise L u))) := by
  have hf : Measurable (field L u x0) := by
    apply Continuous.measurable
    unfold field
    fun_prop
  have hn : Measurable (noise L u) := measurable_const
  exact (hf.comp measurable_fst).add
    (((measurable_of_countable (coinError p)).comp measurable_snd).smul (hn.comp measurable_fst))

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma admissible (q : LowerParams) (hL : 0 ≤ q.L) (hM : 0 ≤ q.M)
    (u : EuclideanSpace ℝ (Fin q.d)) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hΔ : q.L / 2 * ‖u‖ ^ 2 ≤ q.Δ)
    (hσ : p = 1 ∨ q.L ^ 2 * ‖u‖ ^ 2 / p ≤ q.σ ^ 2) :
    spec.admissible q (objective q.L u q.x0)
      (pairOracle q hp.le hp1 (oracleValue p (field q.L u q.x0) (noise q.L u))) := by
  dsimp only [spec, LongTails.Setups.HolderNoiseNonconvex.spec, LowerParams.toParams]
  have hg (x : EuclideanSpace ℝ (Fin q.d)) : gradient (objective q.L u q.x0) x = field q.L u q.x0 x :=
    (objective_gradient q.L u q.x0 x).gradient
  refine ⟨oracleValue p (field q.L u q.x0) (noise q.L u), coinLaw p hp.le hp1,
    coinPath p hp.le hp1, coinPath_iid hp.le hp1, rfl, ?_, ?_, ?_, oracle_measurable q.L p u q.x0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hg]
    exact objective_gradient q.L u q.x0 x
  · intro x y
    rw [hg, hg]
    exact field_lipschitz hL u q.x0 x y
  · intro x
    exact (objective_gap hL u q.x0 x).trans hΔ
  · intro x
    exact Integrable.of_finite
  · intro x
    rw [hg]
    exact oracle_unbiased hp hp1 _ _ x
  · intro x
    exact Integrable.of_finite
  · intro x
    rw [hg]
    rcases hσ with rfl | hσ
    · rw [HolderNoiseHardOracle.oracle_variance hp hp1]
      simp only [sub_self, zero_div, zero_mul]
      positivity
    · exact (HolderNoiseInitialization.oracle_variance_le hL hp hp1 u q.x0 x).trans hσ
  · intro x y
    exact Integrable.of_finite
  · intro x y
    rw [hg, hg, oracle_increment_zero hp hp1]
    exact mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _)

end LongTails.Proofs.HolderNoiseInitializationAdmissible
