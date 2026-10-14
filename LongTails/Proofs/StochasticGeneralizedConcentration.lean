import LongTails.Proofs.NormSubGaussianBatch

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticGeneralized

open LightTail

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
lemma noise_exp_control {X : Ω → E} {Y : Ω × Ξ → E} {b : Ω → ℝ} {σ t a : ℝ}
    (hσ : 0 < σ) (ht : 0 ≤ t) (hsmall : 12*t*a^2*σ^2 ≤ 1)
    (hX : Measurable X) (hY : Measurable Y) (hb : Measurable b)
    (hba : ∀ ω, (b ω)^2 ≤ a^2)
    (hiX : Integrable (fun ω => Real.exp (‖X ω‖^2/σ^2)) P)
    (heX : (∫ ω, Real.exp (‖X ω‖^2/σ^2) ∂P) ≤ Real.exp 1)
    (hiY : ∀ ω, Integrable (fun ξ => Y (ω, ξ)) Q)
    (hzY : ∀ ω, (∫ ξ, Y (ω, ξ) ∂Q) = 0)
    (hiYexp : ∀ ω, Integrable (fun ξ => Real.exp (‖Y (ω, ξ)‖^2/σ^2)) Q)
    (heY : ∀ ω, (∫ ξ, Real.exp (‖Y (ω, ξ)‖^2/σ^2) ∂Q) ≤ Real.exp 1) (z : E) :
    Integrable (fun w : Ω × Ξ => Real.exp (t*(-b w.1*⟪Y w, z⟫+
      8*a^2*‖X w.1‖^2+6*a^2*‖Y w‖^2))) (P.prod Q) ∧
      (∫ w : Ω × Ξ, Real.exp (t*(-b w.1*⟪Y w, z⟫+
        8*a^2*‖X w.1‖^2+6*a^2*‖Y w‖^2)) ∂P.prod Q) ≤
        Real.exp (14*t*a^2*σ^2+4*t^2*a^2*σ^2*‖z‖^2) := by
  let C := 6*t*a^2*σ^2+4*t^2*a^2*σ^2*‖z‖^2
  have h8 : 8*t*a^2*σ^2 ≤ 1 := by nlinarith [mul_nonneg ht (sq_nonneg a), sq_nonneg σ]
  have hsingle (ω : Ω) := quadratic_linear_exp_control hσ
    (show 0 ≤ 6*t*a^2 by positivity)
    (show 2*(6*t*a^2)*σ^2 ≤ 1 by nlinarith)
    (hY.comp measurable_prodMk_left) (hiY ω) (hzY ω) (hiYexp ω) (heY ω)
    ((-t*b ω) • z)
  have hC (ω : Ω) : 4*σ^2*‖(-t*b ω) • z‖^2+(6*t*a^2)*σ^2 ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hm := mul_le_mul_of_nonneg_left (hba ω) (show 0 ≤ 4*t^2*σ^2*‖z‖^2 by positivity)
    dsimp [C]
    nlinarith only [hm]
  have he (ω : Ω) :
      (fun ξ => Real.exp (t*(-b ω*⟪Y (ω, ξ), z⟫+8*a^2*‖X ω‖^2+6*a^2*‖Y (ω, ξ)‖^2))) =
      fun ξ => Real.exp (8*t*a^2*‖X ω‖^2)*
        Real.exp (⟪(-t*b ω) • z, Y (ω, ξ)⟫+(6*t*a^2)*‖Y (ω, ξ)‖^2) := by
    ext ξ
    rw [← Real.exp_add, real_inner_smul_left, real_inner_comm z]
    congr 1
    ring
  have hi (ω : Ω) : Integrable (fun ξ => Real.exp (t*(-b ω*⟪Y (ω, ξ), z⟫+
      8*a^2*‖X ω‖^2+6*a^2*‖Y (ω, ξ)‖^2))) Q := by
    rw [he]
    exact (hsingle ω).1.const_mul _
  have hcond (ω : Ω) : (∫ ξ, Real.exp (t*(-b ω*⟪Y (ω, ξ), z⟫+
      8*a^2*‖X ω‖^2+6*a^2*‖Y (ω, ξ)‖^2)) ∂Q) ≤
        Real.exp (8*t*a^2*‖X ω‖^2+C) := by
    rw [he, integral_const_mul, Real.exp_add]
    exact mul_le_mul_of_nonneg_left
      ((hsingle ω).2.trans (Real.exp_le_exp.mpr (hC ω))) (Real.exp_nonneg _)
  have hs := integral_exp_scale_le hiX heX
    (show 0 ≤ 8*t*a^2*σ^2 by positivity) h8
  have his : Integrable (fun ω => Real.exp ((8*t*a^2*σ^2)*(‖X ω‖^2/σ^2))) P :=
    integrable_exp_mul_of_nonneg_of_le (u := 1) (by simpa using hiX) (by positivity) h8
  have hsimp : (fun ω => Real.exp (8*t*a^2*‖X ω‖^2+C)) =
      fun ω => Real.exp C*Real.exp ((8*t*a^2*σ^2)*(‖X ω‖^2/σ^2)) := by
    ext ω
    rw [← Real.exp_add]
    congr 1
    field_simp; ring
  have hiG : Integrable (fun ω => Real.exp (8*t*a^2*‖X ω‖^2+C)) P := by
    rw [hsimp]
    exact his.const_mul _
  have hbG : (∫ ω, Real.exp (8*t*a^2*‖X ω‖^2+C) ∂P) ≤
      Real.exp (14*t*a^2*σ^2+4*t^2*a^2*σ^2*‖z‖^2) := by
    rw [hsimp, integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hs (Real.exp_nonneg C)
    rw [← Real.exp_add] at hh
    convert hh using 1
    congr 1
    dsimp [C]
    ring
  have hm : Measurable (fun w => ⟪Y w, z⟫) :=
    (continuous_id.inner continuous_const).measurable.comp hY
  exact integral_prod_exp_control (by fun_prop) hi hcond hiG hbG

omit [IsProbabilityMeasure P] in
lemma remove_compensator {Z Y : Ω → ℝ} {t C : ℝ}
    (hZ : Measurable Z) (hi : Integrable (fun ω => Real.exp (Y ω)) P)
    (hb : (∫ ω, Real.exp (Y ω) ∂P) ≤ 1)
    (hdom : ∀ ω, t*Z ω ≤ C+Y ω) :
    Integrable (fun ω => Real.exp (t*Z ω)) P ∧
      (∫ ω, Real.exp (t*Z ω) ∂P) ≤ Real.exp C := by
  have hpoint (ω : Ω) : Real.exp (t*Z ω) ≤ Real.exp C*Real.exp (Y ω) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (hdom ω)
  have hi' : Integrable (fun ω => Real.exp (t*Z ω)) P := by
    apply (hi.const_mul (Real.exp C)).mono' (by fun_prop)
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hpoint ω
  refine ⟨hi', ?_⟩
  have h := integral_mono hi' (hi.const_mul (Real.exp C)) hpoint
  rw [integral_const_mul] at h
  exact h.trans (mul_le_of_le_one_right (Real.exp_nonneg _) hb)

lemma exponential_tail {Z : Ω → ℝ} {t C r : ℝ} (ht : 0 ≤ t)
    (hi : Integrable (fun ω => Real.exp (t*Z ω)) P)
    (hb : (∫ ω, Real.exp (t*Z ω) ∂P) ≤ Real.exp C) :
    P {ω | r < Z ω} ≤ ENNReal.ofReal (Real.exp (C-t*r)) := by
  have h := measure_ge_le_exp_mul_mgf (μ := P) (X := Z) r ht hi
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-t*r))
  rw [← Real.exp_add] at hm
  have hreal : P.real {ω | r ≤ Z ω} ≤ Real.exp (C-t*r) := by
    simpa only [mgf, sub_eq_add_neg, neg_mul, add_comm] using h.trans hm
  calc
    P {ω | r < Z ω} ≤ P {ω | r ≤ Z ω} := measure_mono (by
      intro ω hω
      change r ≤ Z ω
      exact (show r < Z ω from hω).le)
    _ = ENNReal.ofReal (P.real {ω | r ≤ Z ω}) :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (C-t*r)) := ENNReal.ofReal_le_ofReal hreal

end OracleTemplate.StochasticGeneralized
