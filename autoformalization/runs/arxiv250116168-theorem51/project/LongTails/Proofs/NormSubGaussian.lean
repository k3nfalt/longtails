import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.LightTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_exp_scale_le {X : Ω → ℝ} {B θ : ℝ}
    (hi : Integrable (fun ω => Real.exp (X ω)) P)
    (hB : (∫ ω, Real.exp (X ω) ∂P) ≤ Real.exp B)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∫ ω, Real.exp (θ * X ω) ∂P) ≤ Real.exp (θ * B) := by
  have hs : Integrable (fun ω => Real.exp (θ * X ω)) P :=
    integrable_exp_mul_of_nonneg_of_le (u := 1) (by simpa using hi) hθ hθ1
  have hpow : Integrable ((fun x : ℝ => x ^ θ) ∘ (fun ω => Real.exp (X ω))) P := by
    simpa only [Function.comp_def, ← Real.exp_mul, mul_comm] using hs
  have hj := (Real.concaveOn_rpow hθ hθ1).le_map_integral
    (Real.continuous_rpow_const hθ).continuousOn isClosed_Ici
    (ae_of_all _ (fun ω => (Real.exp_nonneg (X ω)))) hi hpow
  have hb := Real.rpow_le_rpow (integral_nonneg (fun ω => Real.exp_nonneg (X ω))) hB hθ
  have h := hj.trans hb
  simpa only [← Real.exp_mul, mul_comm] using h

omit [IsProbabilityMeasure P] in
lemma exp_linear_integrable_of_square {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun ω => Real.exp ((X ω) ^ 2)) P) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) P := by
  refine (hi.const_mul (Real.exp (t ^ 2 / 4))).mono'
    (hX.const_mul t |>.exp.aestronglyMeasurable) (ae_of_all _ (fun ω => ?_))
  simp only [Real.norm_eq_abs, Real.abs_exp]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (X ω - t / 2)]

lemma one_le_integral_exp_of_centered {X : Ω → ℝ}
    (hX : Integrable X P) (hzero : (∫ ω, X ω ∂P) = 0)
    (hexp : Integrable (fun ω => Real.exp (X ω)) P) :
    1 ≤ ∫ ω, Real.exp (X ω) ∂P := by
  have h := integral_mono (hX.add (integrable_const 1)) hexp
    (fun ω => Real.add_one_le_exp (X ω))
  simpa [integral_add hX (integrable_const 1), hzero] using h

lemma symmetric_exp_bound (t x y : ℝ) :
    (Real.exp (t*x) * Real.exp ((-t)*y) + Real.exp ((-t)*x) * Real.exp (t*y)) / 2 ≤
      Real.exp (t^2*x^2) * Real.exp (t^2*y^2) := by
  have he : (Real.exp (t*x) * Real.exp ((-t)*y) +
      Real.exp ((-t)*x) * Real.exp (t*y)) / 2 = Real.cosh (t*(x-y)) := by
    rw [Real.cosh_eq, ← Real.exp_add, ← Real.exp_add]
    congr 2 <;> congr 1 <;> ring
  rw [he, ← Real.exp_add]
  refine (Real.cosh_le_exp_half_sq _).trans (Real.exp_le_exp.mpr ?_)
  nlinarith [sq_nonneg (t*(x+y))]

lemma symmetric_integral_exp_bound {X : Ω → ℝ} {t : ℝ}
    (ht : Integrable (fun ω => Real.exp (t * X ω)) P)
    (hnt : Integrable (fun ω => Real.exp ((-t) * X ω)) P)
    (hsq : Integrable (fun ω => Real.exp (t^2 * (X ω)^2)) P) :
    (∫ ω, Real.exp (t * X ω) ∂P) * (∫ ω, Real.exp ((-t) * X ω) ∂P) ≤
      (∫ ω, Real.exp (t^2 * (X ω)^2) ∂P)^2 := by
  have hp := integral_mono ((ht.mul_prod hnt).add (hnt.mul_prod ht) |>.div_const 2)
    (hsq.mul_prod hsq) (fun ω : Ω × Ω => symmetric_exp_bound t (X ω.1) (X ω.2))
  simp only [Pi.add_apply] at hp
  rw [integral_div, integral_add (ht.mul_prod hnt) (hnt.mul_prod ht),
    integral_prod_mul (fun ω => Real.exp (t * X ω)) (fun ω => Real.exp ((-t) * X ω)),
    integral_prod_mul (fun ω => Real.exp ((-t) * X ω)) (fun ω => Real.exp (t * X ω)),
    integral_prod_mul (fun ω => Real.exp (t^2 * (X ω)^2))
      (fun ω => Real.exp (t^2 * (X ω)^2))] at hp
  nlinarith only [hp]

lemma scalar_mgf_le {X : Ω → ℝ} (hX : Measurable X) (hXi : Integrable X P)
    (hzero : (∫ ω, X ω ∂P) = 0)
    (hi : Integrable (fun ω => Real.exp ((X ω)^2)) P)
    (hbound : (∫ ω, Real.exp ((X ω)^2) ∂P) ≤ Real.exp 1) (t : ℝ) :
    (∫ ω, Real.exp (t * X ω) ∂P) ≤ Real.exp (2 * t^2) := by
  have ht := exp_linear_integrable_of_square hX hi t
  by_cases hsmall : t^2 ≤ 1
  · have hnt := exp_linear_integrable_of_square hX hi (-t)
    have hsq : Integrable (fun ω => Real.exp (t^2 * (X ω)^2)) P :=
      integrable_exp_mul_of_nonneg_of_le (u := 1) (by simpa using hi) (sq_nonneg t) hsmall
    have hj : (∫ ω, Real.exp (t^2 * (X ω)^2) ∂P) ≤ Real.exp (t^2) := by
      simpa only [mul_one] using integral_exp_scale_le hi hbound (sq_nonneg t) hsmall
    have hneg : 1 ≤ ∫ ω, Real.exp ((-t) * X ω) ∂P :=
      one_le_integral_exp_of_centered (hXi.const_mul (-t))
        (by rw [integral_const_mul, hzero, mul_zero]) hnt
    have hn : 0 ≤ ∫ ω, Real.exp (t^2 * (X ω)^2) ∂P :=
      integral_nonneg (fun _ => Real.exp_nonneg _)
    calc
      _ ≤ (∫ ω, Real.exp (t * X ω) ∂P) * (∫ ω, Real.exp ((-t) * X ω) ∂P) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hneg
          (integral_nonneg (fun _ => Real.exp_nonneg _))
      _ ≤ (∫ ω, Real.exp (t^2 * (X ω)^2) ∂P)^2 := symmetric_integral_exp_bound ht hnt hsq
      _ ≤ (Real.exp (t^2))^2 := pow_le_pow_left₀ hn hj 2
      _ = Real.exp (2 * t^2) := by rw [sq, ← Real.exp_add]; congr 1; ring
  · have hp : (∫ ω, Real.exp (t * X ω) ∂P) ≤
        Real.exp (t^2/4) * (∫ ω, Real.exp ((X ω)^2) ∂P) := by
      rw [← integral_const_mul]
      apply integral_mono ht (hi.const_mul _) (fun ω => ?_)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (X ω-t/2)]
    calc
      _ ≤ Real.exp (t^2/4) * (∫ ω, Real.exp ((X ω)^2) ∂P) := hp
      _ ≤ Real.exp (t^2/4) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
      _ ≤ Real.exp (2 * t^2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith

lemma scalar_hasSubgaussianMGF {X : Ω → ℝ} (hX : Measurable X) (hXi : Integrable X P)
    (hzero : (∫ ω, X ω ∂P) = 0)
    (hi : Integrable (fun ω => Real.exp ((X ω)^2)) P)
    (hbound : (∫ ω, Real.exp ((X ω)^2) ∂P) ≤ Real.exp 1) :
    HasSubgaussianMGF X 4 P where
  integrable_exp_mul := exp_linear_integrable_of_square hX hi
  mgf_le t := by
    convert scalar_mgf_le hX hXi hzero hi hbound t using 1 <;> norm_num [mgf]; ring

omit [IsProbabilityMeasure P] in
lemma scalar_exp_integrable_scaled {X : Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hX : Measurable X) (hi : Integrable (fun ω => Real.exp ((X ω)^2 / σ^2)) P)
    (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) P := by
  have h := exp_linear_integrable_of_square (hX.div_const σ)
    (show Integrable (fun ω => Real.exp ((X ω/σ)^2)) P by simpa only [div_pow] using hi)
    (t*σ)
  convert h using 1
  ext ω
  congr 1
  field_simp

lemma scalar_mgf_le_scaled {X : Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hX : Measurable X) (hXi : Integrable X P) (hzero : (∫ ω, X ω ∂P) = 0)
    (hi : Integrable (fun ω => Real.exp ((X ω)^2 / σ^2)) P)
    (hbound : (∫ ω, Real.exp ((X ω)^2 / σ^2) ∂P) ≤ Real.exp 1) (t : ℝ) :
    (∫ ω, Real.exp (t * X ω) ∂P) ≤ Real.exp (2 * σ^2 * t^2) := by
  have h := scalar_mgf_le (hX.div_const σ) (hXi.div_const σ)
    (show (∫ ω, X ω/σ ∂P) = 0 by rw [integral_div, hzero, zero_div])
    (show Integrable (fun ω => Real.exp ((X ω/σ)^2)) P by simpa only [div_pow] using hi)
    (show (∫ ω, Real.exp ((X ω/σ)^2) ∂P) ≤ Real.exp 1 by simpa only [div_pow] using hbound)
    (t*σ)
  have he : (fun ω => Real.exp (t*σ*(X ω/σ))) = (fun ω => Real.exp (t*X ω)) := by
    ext ω
    congr 1
    field_simp
  rw [he] at h
  convert h using 1; congr 1; ring

omit [IsProbabilityMeasure P] in
lemma exp_add_integral_control {U V : Ω → ℝ} {A B : ℝ}
    (hU : Measurable U) (hV : Measurable V)
    (hiU : Integrable (fun ω => Real.exp (2 * U ω)) P)
    (hiV : Integrable (fun ω => Real.exp (2 * V ω)) P)
    (hbU : (∫ ω, Real.exp (2 * U ω) ∂P) ≤ Real.exp (2*A))
    (hbV : (∫ ω, Real.exp (2 * V ω) ∂P) ≤ Real.exp (2*B)) :
    Integrable (fun ω => Real.exp (U ω+V ω)) P ∧
      (∫ ω, Real.exp (U ω+V ω) ∂P) ≤ Real.exp (A+B) := by
  let F : Ω → ℝ := fun ω => Real.exp (U ω-A)
  let G : Ω → ℝ := fun ω => Real.exp (V ω-B)
  have hF : (fun ω => (F ω)^2) = fun ω => Real.exp (-(2*A))*Real.exp (2*U ω) := by
    ext ω
    simp only [F, sq, ← Real.exp_add]
    congr 1
    ring
  have hG : (fun ω => (G ω)^2) = fun ω => Real.exp (-(2*B))*Real.exp (2*V ω) := by
    ext ω
    simp only [G, sq, ← Real.exp_add]
    congr 1
    ring
  have hiF : Integrable (fun ω => (F ω)^2) P := by rw [hF]; exact hiU.const_mul _
  have hiG : Integrable (fun ω => (G ω)^2) P := by rw [hG]; exact hiV.const_mul _
  have hbF : (∫ ω, (F ω)^2 ∂P) ≤ 1 := by
    rw [hF, integral_const_mul]
    have h := mul_le_mul_of_nonneg_left hbU (Real.exp_nonneg (-(2*A)))
    simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using h
  have hbG : (∫ ω, (G ω)^2 ∂P) ≤ 1 := by
    rw [hG, integral_const_mul]
    have h := mul_le_mul_of_nonneg_left hbV (Real.exp_nonneg (-(2*B)))
    simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using h
  have hpt (ω : Ω) : F ω * G ω ≤ ((F ω)^2+(G ω)^2)/2 := by
    nlinarith [sq_nonneg (F ω-G ω)]
  have hiFG : Integrable (fun ω => F ω*G ω) P := by
    apply ((hiF.add hiG).div_const 2).mono'
      (((hU.sub_const A).exp.mul (hV.sub_const B).exp).aestronglyMeasurable)
    filter_upwards [] with ω
    change ‖F ω*G ω‖ ≤ ((F ω)^2+(G ω)^2)/2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
    exact hpt ω
  have hbFG : (∫ ω, F ω*G ω ∂P) ≤ 1 := by
    have h := integral_mono hiFG ((hiF.add hiG).div_const 2) hpt
    simp only [Pi.add_apply] at h
    rw [integral_div, integral_add hiF hiG] at h
    linarith
  have he : (fun ω => Real.exp (U ω+V ω)) =
      fun ω => Real.exp (A+B)*(F ω*G ω) := by
    ext ω
    simp only [F, G, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  refine ⟨hiFG.const_mul _, ?_⟩
  rw [integral_const_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hbFG (Real.exp_nonneg (A+B))

lemma integral_prod_exp_control {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Measure Ξ} [SFinite Q] {F : Ω × Ξ → ℝ} {G : Ω → ℝ} {C : ℝ}
    (hF : Measurable F) (hiF : ∀ ω, Integrable (fun ξ => Real.exp (F (ω, ξ))) Q)
    (hbF : ∀ ω, (∫ ξ, Real.exp (F (ω, ξ)) ∂Q) ≤ Real.exp (G ω))
    (hiG : Integrable (fun ω => Real.exp (G ω)) P)
    (hbG : (∫ ω, Real.exp (G ω) ∂P) ≤ C) :
    Integrable (fun z => Real.exp (F z)) (P.prod Q) ∧
      (∫ z, Real.exp (F z) ∂P.prod Q) ≤ C := by
  have hm := hF.exp.stronglyMeasurable.integral_prod_right' (ν := Q)
  have hi : Integrable (fun ω => ∫ ξ, Real.exp (F (ω, ξ)) ∂Q) P := by
    apply hiG.mono' hm.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ξ => Real.exp_nonneg _))]
    exact hbF ω
  have hp : Integrable (fun z => Real.exp (F z)) (P.prod Q) := by
    apply (integrable_prod_iff hF.exp.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hiF, ?_⟩
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hi
  refine ⟨hp, ?_⟩
  rw [integral_prod _ hp]
  exact (integral_mono hi hiG hbF).trans hbG

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
lemma inner_mgf_control {X : Ω → E} {σ : ℝ} (hσ : 0 < σ)
    (hX : Measurable X) (hXi : Integrable X P) (hzero : (∫ ω, X ω ∂P) = 0)
    (hi : Integrable (fun ω => Real.exp (‖X ω‖^2 / σ^2)) P)
    (hbound : (∫ ω, Real.exp (‖X ω‖^2 / σ^2) ∂P) ≤ Real.exp 1) (v : E) :
    Integrable (fun ω => Real.exp ⟪v, X ω⟫) P ∧
      (∫ ω, Real.exp ⟪v, X ω⟫ ∂P) ≤ Real.exp (2 * σ^2 * ‖v‖^2) := by
  by_cases hv : v = 0
  · subst v
    simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hY : Measurable (fun ω => ⟪v, X ω⟫) :=
    (continuous_const.inner continuous_id).measurable.comp hX
  have hb (ω : Ω) : ⟪v, X ω⟫^2 / (σ*‖v‖)^2 ≤ ‖X ω‖^2 / σ^2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm v (X ω)) 2
    rw [sq_abs, mul_pow] at hs
    apply (div_le_div_iff₀ (by positivity : 0 < (σ*‖v‖)^2) (by positivity : 0 < σ^2)).mpr
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg σ)
    nlinarith only [hm]
  have hYexp : Integrable (fun ω => Real.exp (⟪v, X ω⟫^2 / (σ*‖v‖)^2)) P := by
    apply hi.mono' ((hY.pow_const 2 |>.div_const _).exp.aestronglyMeasurable)
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, Real.abs_exp] using Real.exp_le_exp.mpr (hb ω)
  have hYbound : (∫ ω, Real.exp (⟪v, X ω⟫^2 / (σ*‖v‖)^2) ∂P) ≤ Real.exp 1 :=
    (integral_mono hYexp hi (fun ω => Real.exp_le_exp.mpr (hb ω))).trans hbound
  have hz : (∫ ω, ⟪v, X ω⟫ ∂P) = 0 := by rw [integral_inner hXi, hzero, inner_zero_right]
  refine ⟨?_, ?_⟩
  · simpa only [one_mul] using scalar_exp_integrable_scaled (mul_pos hσ hnv) hY hYexp 1
  · have h := scalar_mgf_le_scaled (mul_pos hσ hnv) hY (hXi.const_inner v) hz hYexp hYbound 1
    simpa only [one_mul, one_pow, mul_one, mul_pow, mul_assoc] using h

omit [SecondCountableTopology E] in
lemma shifted_norm_exp_control {X : Ω → E} {σ a : ℝ} (hσ : 0 < σ)
    (ha : 0 ≤ a) (has : 2*a*σ^2 ≤ 1)
    (hX : Measurable X) (hXi : Integrable X P) (hzero : (∫ ω, X ω ∂P) = 0)
    (hi : Integrable (fun ω => Real.exp (‖X ω‖^2 / σ^2)) P)
    (hbound : (∫ ω, Real.exp (‖X ω‖^2 / σ^2) ∂P) ≤ Real.exp 1) (s : E) :
    Integrable (fun ω => Real.exp (a*‖s+X ω‖^2)) P ∧
      (∫ ω, Real.exp (a*‖s+X ω‖^2) ∂P) ≤
        Real.exp ((a+16*a^2*σ^2)*‖s‖^2+a*σ^2) := by
  have hin := inner_mgf_control hσ hX hXi hzero hi hbound ((4*a) • s)
  have heU : (fun ω => Real.exp ⟪(4*a) • s, X ω⟫) =
      fun ω => Real.exp (2*(2*a*⟪s, X ω⟫)) := by
    ext ω
    rw [real_inner_smul_left]
    congr 1
    ring
  rw [heU] at hin
  have hbU : (∫ ω, Real.exp (2*(2*a*⟪s, X ω⟫)) ∂P) ≤
      Real.exp (2*(16*a^2*σ^2*‖s‖^2)) := by
    convert hin.2 using 1
    congr 1
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have heV : (fun ω => Real.exp ((2*a*σ^2)*(‖X ω‖^2/σ^2))) =
      fun ω => Real.exp (2*(a*‖X ω‖^2)) := by
    ext ω
    congr 1
    field_simp

  have hiV : Integrable (fun ω => Real.exp (2*(a*‖X ω‖^2))) P := by
    rw [← heV]
    exact integrable_exp_mul_of_nonneg_of_le (u := 1) (by simpa using hi)
      (by positivity) has
  have hbV : (∫ ω, Real.exp (2*(a*‖X ω‖^2)) ∂P) ≤ Real.exp (2*(a*σ^2)) := by
    have h := integral_exp_scale_le hi hbound (show 0 ≤ 2*a*σ^2 by positivity) has
    rw [heV] at h
    simpa only [mul_one, mul_assoc] using h
  have hm : Measurable (fun ω => ⟪s, X ω⟫) :=
    (continuous_const.inner continuous_id).measurable.comp hX
  have hc := exp_add_integral_control (hm.const_mul (2*a))
    ((hX.norm.pow_const 2).const_mul a) hin.1 hiV hbU hbV
  have he : (fun ω => Real.exp (a*‖s+X ω‖^2)) =
      fun ω => Real.exp (a*‖s‖^2)*Real.exp (2*a*⟪s, X ω⟫+a*‖X ω‖^2) := by
    ext ω
    rw [← Real.exp_add, norm_add_sq_real]
    congr 1
    ring
  rw [he]
  refine ⟨hc.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hc.2 (Real.exp_nonneg (a*‖s‖^2))
  rw [← Real.exp_add] at h
  convert h using 1
  congr 1
  ring

lemma norm_add_exp_control {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Measure Ξ} [IsProbabilityMeasure Q] {S : Ω → E} {X : Ξ → E}
    {σ v a : ℝ} (hσ : 0 < σ) (hv : 0 < v) (ha : 0 ≤ a)
    (has : 2*a*σ^2 ≤ 1) (hcoef : (a+16*a^2*σ^2)*v+a*σ^2 ≤ 1)
    (hS : Measurable S) (hX : Measurable X)
    (hXi : Integrable X Q) (hzero : (∫ ξ, X ξ ∂Q) = 0)
    (hiX : Integrable (fun ξ => Real.exp (‖X ξ‖^2/σ^2)) Q)
    (hbX : (∫ ξ, Real.exp (‖X ξ‖^2/σ^2) ∂Q) ≤ Real.exp 1)
    (hiS : Integrable (fun ω => Real.exp (‖S ω‖^2/v)) P)
    (hbS : (∫ ω, Real.exp (‖S ω‖^2/v) ∂P) ≤ Real.exp 1) :
    Integrable (fun z : Ω × Ξ => Real.exp (a*‖S z.1+X z.2‖^2)) (P.prod Q) ∧
      (∫ z : Ω × Ξ, Real.exp (a*‖S z.1+X z.2‖^2) ∂P.prod Q) ≤ Real.exp 1 := by
  let θ := (a+16*a^2*σ^2)*v
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := by dsimp [θ]; nlinarith [sq_nonneg σ]
  have hs := integral_exp_scale_le hiS hbS hθ hθ1
  have hiθ : Integrable (fun ω => Real.exp (θ*(‖S ω‖^2/v))) P :=
    integrable_exp_mul_of_nonneg_of_le (u := 1) (by simpa using hiS) hθ hθ1
  have he : (fun ω => Real.exp ((a+16*a^2*σ^2)*‖S ω‖^2+a*σ^2)) =
      fun ω => Real.exp (a*σ^2)*Real.exp (θ*(‖S ω‖^2/v)) := by
    ext ω
    rw [← Real.exp_add]
    congr 1
    dsimp [θ]
    field_simp; ring
  have hiG : Integrable (fun ω => Real.exp ((a+16*a^2*σ^2)*‖S ω‖^2+a*σ^2)) P := by
    rw [he]
    exact hiθ.const_mul _
  have hbG : (∫ ω, Real.exp ((a+16*a^2*σ^2)*‖S ω‖^2+a*σ^2) ∂P) ≤ Real.exp 1 := by
    rw [he, integral_const_mul]
    have h := mul_le_mul_of_nonneg_left hs (Real.exp_nonneg (a*σ^2))
    simp only [mul_one, ← Real.exp_add] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    dsimp [θ]
    linarith
  exact integral_prod_exp_control
    (((hS.comp measurable_fst).add (hX.comp measurable_snd)).norm.pow_const 2 |>.const_mul a)
    (fun ω => (shifted_norm_exp_control hσ ha has hX hXi hzero hiX hbX (S ω)).1)
    (fun ω => (shifted_norm_exp_control hσ ha has hX hXi hzero hiX hbX (S ω)).2)
    hiG hbG

omit [SecondCountableTopology E] in
lemma quadratic_linear_exp_control {X : Ω → E} {σ c : ℝ} (hσ : 0 < σ)
    (hc : 0 ≤ c) (hcs : 2*c*σ^2 ≤ 1)
    (hX : Measurable X) (hXi : Integrable X P) (hzero : (∫ ω, X ω ∂P) = 0)
    (hi : Integrable (fun ω => Real.exp (‖X ω‖^2/σ^2)) P)
    (hbound : (∫ ω, Real.exp (‖X ω‖^2/σ^2) ∂P) ≤ Real.exp 1) (v : E) :
    Integrable (fun ω => Real.exp (⟪v, X ω⟫+c*‖X ω‖^2)) P ∧
      (∫ ω, Real.exp (⟪v, X ω⟫+c*‖X ω‖^2) ∂P) ≤
        Real.exp (4*σ^2*‖v‖^2+c*σ^2) := by
  have hin := inner_mgf_control hσ hX hXi hzero hi hbound ((2 : ℝ) • v)
  simp only [real_inner_smul_left] at hin
  have hbU : (∫ ω, Real.exp (2*⟪v, X ω⟫) ∂P) ≤ Real.exp (2*(4*σ^2*‖v‖^2)) := by
    convert hin.2 using 1
    congr 1
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    ring
  have he : (fun ω => Real.exp ((2*c*σ^2)*(‖X ω‖^2/σ^2))) =
      fun ω => Real.exp (2*(c*‖X ω‖^2)) := by
    ext ω
    congr 1
    field_simp

  have hiV : Integrable (fun ω => Real.exp (2*(c*‖X ω‖^2))) P := by
    rw [← he]
    exact integrable_exp_mul_of_nonneg_of_le (u := 1) (by simpa using hi)
      (by positivity) hcs
  have hbV : (∫ ω, Real.exp (2*(c*‖X ω‖^2)) ∂P) ≤ Real.exp (2*(c*σ^2)) := by
    have h := integral_exp_scale_le hi hbound (show 0 ≤ 2*c*σ^2 by positivity) hcs
    rw [he] at h
    simpa only [mul_one, mul_assoc] using h
  exact exp_add_integral_control
    ((continuous_const.inner continuous_id).measurable.comp hX)
    ((hX.norm.pow_const 2).const_mul c) hin.1 hiV hbU hbV

end Hilbert

end OracleTemplate.LightTail
