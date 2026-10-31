import LongTails.Proofs.GdConvex
import LongTails.Proofs.AcceleratedMarkovRun
import LongTails.Setups.AffineMomentConvex

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineMomentNormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def objective (L R : ℝ) (x0 : E) (f : E → ℝ) (x : E) : ℝ :=
  f (x0 + R • x) / (L * R ^ 2)

noncomputable def derivative (L R : ℝ) (x0 : E) (f : E → ℝ) (x : E) : E :=
  (1 / (L * R)) • gradient f (x0 + R • x)

noncomputable def minimizer (R : ℝ) (x0 u : E) : E := (1 / R) • (u - x0)

omit [CompleteSpace E] in
lemma physical_minimizer {R : ℝ} (hR : 0 < R) (x0 u : E) :
    x0 + R • minimizer R x0 u = u := by
  unfold minimizer
  rw [smul_smul, mul_one_div_cancel hR.ne', one_smul]
  abel

omit [CompleteSpace E] in
lemma minimizer_norm {R : ℝ} (hR : 0 < R) (x0 u : E) (hu : ‖x0 - u‖ ≤ R) :
    ‖minimizer R x0 u‖ ≤ 1 := by
  unfold minimizer
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hR), norm_sub_rev]
  calc
    _ ≤ (1 / R) * R := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = 1 := one_div_mul_cancel hR.ne'

lemma derivative_lipschitz {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (x0 : E) (f : E → ℝ)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖derivative L R x0 f x - derivative L R x0 f y‖ ≤ ‖x - y‖ := by
  have h := hlip (x0 + R • x) (x0 + R • y)
  have he : (x0 + R • x) - (x0 + R • y) = R • (x - y) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h
  unfold derivative
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (mul_pos hL hR))]
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 / (L * R) by positivity)
  exact hm.trans_eq (by field_simp)

lemma support {L R : ℝ} (hL : 0 < L) (hR : 0 < R) (x0 : E) (f : E → ℝ)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x) (x y : E) :
    objective L R x0 f x + inner ℝ (derivative L R x0 f x) (y - x) ≤ objective L R x0 f y := by
  have h := OracleTemplate.Gradient.convex_support hc hg (x0 + R • x) (x0 + R • y)
  have he : (x0 + R • y) - (x0 + R • x) = R • (y - x) := by module
  rw [he, inner_smul_right] at h
  have hm := div_le_div_of_nonneg_right h (show 0 ≤ L * R ^ 2 by positivity)
  unfold objective derivative
  rw [real_inner_smul_left]
  have he' : R * inner ℝ (gradient f (x0 + R • x)) (y - x) / (L * R ^ 2) =
      (1 / (L * R)) * inner ℝ (gradient f (x0 + R • x)) (y - x) := by field_simp
  rw [he', sub_div] at hm
  linarith

lemma smooth_model {L R : ℝ} (hL : 0 < L) (hR : 0 < R) (x0 : E) (f : E → ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    objective L R x0 f y ≤ objective L R x0 f x +
      inner ℝ (derivative L R x0 f x) (y - x) + (1 / 2) * ‖y - x‖ ^ 2 := by
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hlip (x0 + R • x) (x0 + R • y)
  have he : (x0 + R • y) - (x0 + R • x) = R • (y - x) := by module
  rw [he, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_pow] at h
  have hm := div_le_div_of_nonneg_right h (show 0 ≤ L * R ^ 2 by positivity)
  unfold objective derivative
  rw [real_inner_smul_left]
  convert hm using 1
  field_simp

omit [CompleteSpace E] in
lemma minimized {L R : ℝ} (hL : 0 < L) (hR : 0 < R) (x0 : E) (f : E → ℝ) (u : E)
    (hu : IsMinOn f Set.univ u) (x : E) :
    objective L R x0 f (minimizer R x0 u) ≤ objective L R x0 f x := by
  unfold objective
  rw [physical_minimizer hR]
  exact div_le_div_of_nonneg_right (hu (Set.mem_univ _)) (by positivity)

lemma derivative_at_minimizer {L R : ℝ} (hL : 0 < L) (hR : 0 < R) (x0 : E) (f : E → ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (u : E)
    (hu : IsMinOn f Set.univ u) : derivative L R x0 f (minimizer R x0 u) = 0 := by
  unfold derivative
  rw [physical_minimizer hR, OracleTemplate.HeavyTailedMarkovGradient.gradient_minimizer_zero hL hg hlip hu,
    smul_zero]

lemma objective_continuous (L R : ℝ) (x0 : E) (f : E → ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x) : Continuous (objective L R x0 f) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  unfold objective
  fun_prop

lemma derivative_continuous {L R : ℝ} (hL : 0 < L) (hR : 0 < R) (x0 : E) (f : E → ℝ)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    Continuous (derivative L R x0 f) := by
  have hl : LipschitzWith 1 (derivative L R x0 f) := LipschitzWith.of_dist_le_mul (by
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using derivative_lipschitz hL hR x0 f hlip x y)
  exact hl.continuous

noncomputable def oracle {Ω : Type*} (L R : ℝ) (x0 : E) (g : E → Ω → E)
    (x : E) (ω : Ω) : E := (1 / (L * R)) • g (x0 + R • x) ω

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma oracle_measurable {L R : ℝ} (x0 : E) (g : E → Ω → E)
    (hg : Measurable (fun z : E × Ω => g z.1 z.2)) :
    Measurable (fun z : E × Ω => oracle L R x0 g z.1 z.2) := by
  unfold oracle
  exact (hg.comp ((measurable_const.add (measurable_const.smul measurable_fst)).prodMk
    measurable_snd)).const_smul _

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [IsProbabilityMeasure P] in
lemma oracle_integrable {L R : ℝ} (x0 : E) (g : E → Ω → E)
    (hg : ∀ x, Integrable (g x) P) (x : E) : Integrable (oracle L R x0 g x) P :=
  (hg _).smul _

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma oracle_mean {L R : ℝ} (x0 : E) (f : E → ℝ) (g : E → Ω → E)
    (hg : ∀ x, (∫ ω, g x ω ∂P) = gradient f x) (x : E) :
    (∫ ω, oracle L R x0 g x ω ∂P) = derivative L R x0 f x := by
  simp only [oracle, derivative, integral_smul, hg]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma oracle_error_power {L R p : ℝ} (hL : 0 < L) (hR : 0 < R)
    (x0 : E) (f : E → ℝ) (g : E → Ω → E) (x : E) (ω : Ω) :
    ‖oracle L R x0 g x ω - derivative L R x0 f x‖ ^ p =
      (1 / (L * R)) ^ p * ‖g (x0 + R • x) ω - gradient f (x0 + R • x)‖ ^ p := by
  unfold oracle derivative
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (L * R)),
    Real.mul_rpow (by positivity) (norm_nonneg _)]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma oracle_moment_integrable {L R p : ℝ} (hL : 0 < L) (hR : 0 < R)
    (x0 : E) (f : E → ℝ) (g : E → Ω → E)
    (hg : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ p) P) (x : E) :
    Integrable (fun ω => ‖oracle L R x0 g x ω - derivative L R x0 f x‖ ^ p) P := by
  simp_rw [oracle_error_power hL hR]
  exact (hg _).const_mul _

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma oracle_moment {L R p σ σ0 : ℝ} (hL : 0 < L) (hR : 0 < R) (hσ0 : 0 ≤ σ0)
    (x0 : E) (f : E → ℝ) (g : E → Ω → E)
    (hg : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ p ∂P) ≤ σ0 ^ p + σ ^ p * ‖gradient f x‖ ^ p)
    (x : E) :
    (∫ ω, ‖oracle L R x0 g x ω - derivative L R x0 f x‖ ^ p ∂P) ≤
      (σ0 / (L * R)) ^ p + σ ^ p * ‖derivative L R x0 f x‖ ^ p := by
  simp_rw [oracle_error_power hL hR]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (hg (x0 + R • x))
    (Real.rpow_nonneg (show 0 ≤ 1 / (L * R) by positivity) p)
  unfold derivative
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (L * R)),
    Real.mul_rpow (by positivity) (norm_nonneg _)]
  have hσ : (σ0 / (L * R)) ^ p = (1 / (L * R)) ^ p * σ0 ^ p := by
    rw [show σ0 / (L * R) = (1 / (L * R)) * σ0 by ring,
      Real.mul_rpow (by positivity) hσ0]
  rw [hσ]
  nlinarith only [h]

end LongTails.Proofs.AffineMomentNormalization
