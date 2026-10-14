import LongTails.Proofs.RobustCenteredClipping
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import LongTails.Proofs.NormSubGaussian

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RobustGradient

lemma exp_le_quadratic {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.exp_bound (n := 2) hx (by norm_num)
  norm_num [Finset.sum_range_succ, sq_abs] at h
  have hu := (abs_le.mp h).2
  nlinarith [sq_nonneg x]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma bounded_increment_mgf {Z : Ω → ℝ} (hZ : Measurable Z)
    (hbound : ∀ ω, |Z ω| ≤ 1) {m v : ℝ}
    (hmean : (∫ ω, Z ω ∂P) ≤ m)
    (hsecond : (∫ ω, (Z ω) ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => Real.exp (Z ω)) P ∧
    (∫ ω, Real.exp (Z ω) ∂P) ≤ Real.exp (m + v) := by
  have hZi : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hbound ω))
  have hZ2i : Integrable (fun ω => (Z ω) ^ 2) P := by
    apply Integrable.of_bound (hZ.pow_const 2).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [(abs_le.mp (hbound ω)).1, (abs_le.mp (hbound ω)).2])
  have hei : Integrable (fun ω => Real.exp (Z ω)) P := by
    apply Integrable.of_bound hZ.exp.aestronglyMeasurable (Real.exp 1)
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact Real.exp_le_exp.mpr (abs_le.mp (hbound ω)).2)
  refine ⟨hei, ?_⟩
  have h := integral_mono hei (((integrable_const 1).add hZi).add hZ2i)
    (fun ω => exp_le_quadratic (hbound ω))
  simp only [Pi.add_apply] at h
  have hsum : Integrable (fun ω => 1 + Z ω) P := (integrable_const 1).add hZi
  rw [integral_add hsum hZ2i,
    integral_add (integrable_const 1) hZi, integral_const] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  calc
    _ ≤ 1 + (∫ ω, Z ω ∂P) + (∫ ω, (Z ω)^2 ∂P) := h
    _ ≤ 1 + (m + v) := by linarith
    _ ≤ Real.exp (m + v) := by simpa only [add_comm] using Real.add_one_le_exp (m + v)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma energy_increment_abs {a b c M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hba : b ≤ a) (hc : 0 ≤ c) (y z : E) (hy : ‖y‖ ≤ M) :
    |-b * ⟪z, y⟫ + c * a^2 * ‖y‖^2| ≤ a*M*‖z‖ + c*a^2*M^2 := by
  have hi : |⟪z, y⟫| ≤ ‖z‖*M :=
    (abs_real_inner_le_norm z y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg z))
  calc
    _ ≤ |-b*⟪z, y⟫| + |c*a^2*‖y‖^2| := abs_add_le _ _
    _ = b*|⟪z, y⟫| + c*a^2*‖y‖^2 := by
      rw [abs_mul, abs_neg, abs_of_nonneg hb,
        abs_of_nonneg (show 0 ≤ c*a^2*‖y‖^2 by positivity)]
    _ ≤ a*(‖z‖*M) + c*a^2*M^2 := by gcongr
    _ = _ := by ring

lemma energy_increment_sq {a b c M : ℝ} (hb : 0 ≤ b)
    (hba : b ≤ a) (y z : E) (hy : ‖y‖ ≤ M) :
    (-b*⟪z, y⟫+c*a^2*‖y‖^2)^2 ≤
      2*(a^2*‖z‖^2+c^2*a^4*M^2)*‖y‖^2 := by
  have hi : |-b*⟪z, y⟫| ≤ a*‖z‖*‖y‖ := by
    rw [abs_mul, abs_neg, abs_of_nonneg hb]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z y) hb).trans
      ((mul_le_mul_of_nonneg_right hba (by positivity)).trans_eq (by ring))
  have hisq := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [sq_abs] at hisq
  have hysq := pow_le_pow_left₀ (norm_nonneg y) hy 2
  have hq := mul_le_mul_of_nonneg_left hysq
    (show 0 ≤ c^2*a^4*‖y‖^2 by positivity)
  nlinarith only [hisq, hq, sq_nonneg (-b*⟪z, y⟫-c*a^2*‖y‖^2)]

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
lemma energy_increment_mgf {Y : Ω → E} (hY : Measurable Y) (hYi : Integrable Y P)
    (hY2i : Integrable (fun ω => ‖Y ω‖^2) P) {a b c M t d v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) (hc : 0 ≤ c)
     (ht : 0 ≤ t) (z : E)
    (hbound : ∀ ω, ‖Y ω‖ ≤ M) (hmean : ‖∫ ω, Y ω ∂P‖ ≤ d)
    (hsecond : (∫ ω, ‖Y ω‖^2 ∂P) ≤ v)
    (hsmall : t*(a*M*‖z‖+c*a^2*M^2) ≤ 1) :
    Integrable (fun ω => Real.exp (t*(-b*⟪z, Y ω⟫+c*a^2*‖Y ω‖^2))) P ∧
    (∫ ω, Real.exp (t*(-b*⟪z, Y ω⟫+c*a^2*‖Y ω‖^2)) ∂P) ≤
      Real.exp (t*(a*‖z‖*d+c*a^2*v)+2*t^2*(a^2*‖z‖^2+c^2*a^4*M^2)*v) := by
  let Z := fun ω => -b*⟪z, Y ω⟫+c*a^2*‖Y ω‖^2
  let K := 2*(a^2*‖z‖^2+c^2*a^4*M^2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  have hZi : Integrable Z P := ((hYi.const_inner z).const_mul (-b)).add
    (hY2i.const_mul (c*a^2))
  have hs (ω : Ω) : (Z ω)^2 ≤ K*‖Y ω‖^2 :=
    energy_increment_sq hb hba (Y ω) z (hbound ω)
  have hZ2i : Integrable (fun ω => (Z ω)^2) P := by
    apply (hY2i.const_mul K).mono' (hZ.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hs ω)
  have hZmean : (∫ ω, Z ω ∂P) ≤ a*‖z‖*d+c*a^2*v := by
    rw [show Z = fun ω => (-b)*⟪z, Y ω⟫+(c*a^2)*‖Y ω‖^2 from rfl,
      integral_add ((hYi.const_inner z).const_mul (-b)) (hY2i.const_mul (c*a^2)),
      integral_const_mul, integral_const_mul, integral_inner hYi z]
    have hd : 0 ≤ d := (norm_nonneg _).trans hmean
    have hi := abs_real_inner_le_norm z (∫ ω, Y ω ∂P)
    have hj : -b*⟪z, ∫ ω, Y ω ∂P⟫ ≤ a*‖z‖*d := by
      calc
        _ ≤ b*|⟪z, ∫ ω, Y ω ∂P⟫| :=
          by nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs ⟪z, ∫ ω, Y ω ∂P⟫) hb]
        _ ≤ a*(‖z‖*d) := mul_le_mul hba
          (hi.trans (mul_le_mul_of_nonneg_left hmean (norm_nonneg z)))
          (abs_nonneg _) ha
        _ = _ := by ring
    exact add_le_add hj (mul_le_mul_of_nonneg_left hsecond (by positivity))
  have hZsecond : (∫ ω, (Z ω)^2 ∂P) ≤ K*v := by
    have h := integral_mono hZ2i (hY2i.const_mul K) hs
    rw [integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hsecond hK)
  have hscaled (ω : Ω) : |t*Z ω| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left
      (energy_increment_abs ha hb hba hc (Y ω) z (hbound ω)) ht).trans hsmall
  have hmean' : (∫ ω, t*Z ω ∂P) ≤ t*(a*‖z‖*d+c*a^2*v) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hZmean ht
  have hsecond' : (∫ ω, (t*Z ω)^2 ∂P) ≤ t^2*K*v := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hZsecond (sq_nonneg t)).trans_eq (by ring)
  have h := bounded_increment_mgf (hZ.const_mul t) hscaled hmean' hsecond'
  convert h using 1; dsimp [Z, K]; ring

omit [SecondCountableTopology E] in
lemma two_stage_energy_mgf {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Measure Ξ} [IsProbabilityMeasure Q] {X : Ω → E} {Y : Ω × Ξ → E}
    {b : Ω → ℝ} {a M t d v : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hX : Measurable X) (hY : Measurable Y) (hb : Measurable b)
    (hba : ∀ ω, 0 ≤ b ω ∧ b ω ≤ a)
    (hXi : Integrable X P) (hX2i : Integrable (fun ω => ‖X ω‖^2) P)
    (hXbound : ∀ ω, ‖X ω‖ ≤ M) (hXsecond : (∫ ω, ‖X ω‖^2 ∂P) ≤ v)
    (hYi : ∀ ω, Integrable (fun ξ => Y (ω, ξ)) Q)
    (hY2i : ∀ ω, Integrable (fun ξ => ‖Y (ω, ξ)‖^2) Q)
    (hYbound : ∀ ω ξ, ‖Y (ω, ξ)‖ ≤ M)
    (hYmean : ∀ ω, ‖∫ ξ, Y (ω, ξ) ∂Q‖ ≤ d)
    (hYsecond : ∀ ω, (∫ ξ, ‖Y (ω, ξ)‖^2 ∂Q) ≤ v)
    (z : E) (hsmall : t*(a*M*‖z‖+8*a^2*M^2) ≤ 1) :
    Integrable (fun w : Ω × Ξ => Real.exp (t*(-b w.1*⟪z, Y w⟫+
      8*a^2*‖X w.1‖^2+6*a^2*‖Y w‖^2))) (P.prod Q) ∧
    (∫ w : Ω × Ξ, Real.exp (t*(-b w.1*⟪z, Y w⟫+
      8*a^2*‖X w.1‖^2+6*a^2*‖Y w‖^2)) ∂P.prod Q) ≤
      Real.exp (t*(a*‖z‖*d+14*a^2*v)+2*t^2*(a^2*‖z‖^2+100*a^4*M^2)*v) := by
  let C := t*(a*‖z‖*d+6*a^2*v)+2*t^2*(a^2*‖z‖^2+36*a^4*M^2)*v
  have h6 : t*(a*M*‖z‖+6*a^2*M^2) ≤ 1 := by
    have hm : 0 ≤ t*a^2*M^2 := by positivity
    nlinarith
  have hy (ω : Ω) := energy_increment_mgf
    (hY.comp measurable_prodMk_left) (hYi ω) (hY2i ω) ha (hba ω).1 (hba ω).2
    (by norm_num : (0 : ℝ) ≤ 6) ht z (hYbound ω) (hYmean ω) (hYsecond ω) h6
  have hy' (ω : Ω) : (∫ ξ, Real.exp (t*(-b ω*⟪z, Y (ω, ξ)⟫+
      6*a^2*‖Y (ω, ξ)‖^2)) ∂Q) ≤ Real.exp C := by
    simpa only [Function.comp_apply, C, show (6 : ℝ)^2 = 36 by norm_num] using (hy ω).2
  have h8 : t*(a*M*‖(0 : E)‖+8*a^2*M^2) ≤ 1 := by
    simp only [norm_zero, mul_zero, zero_add]
    have hm : 0 ≤ t*a*M*‖z‖ := by positivity
    nlinarith
  have hx := energy_increment_mgf hX hXi hX2i ha (le_refl (0 : ℝ)) ha
    (by norm_num : (0 : ℝ) ≤ 8) ht (0 : E) hXbound
    (le_refl ‖∫ ω, X ω ∂P‖) hXsecond h8
  simp only [neg_zero, zero_mul, zero_add, norm_zero, mul_zero, sq] at hx
  have he (ω : Ω) :
      (fun ξ => Real.exp (t*(-b ω*⟪z, Y (ω, ξ)⟫+8*a^2*‖X ω‖^2+
        6*a^2*‖Y (ω, ξ)‖^2))) =
      fun ξ => Real.exp (8*t*a^2*‖X ω‖^2)*Real.exp (t*(-b ω*⟪z, Y (ω, ξ)⟫+
        6*a^2*‖Y (ω, ξ)‖^2)) := by
    ext ξ
    rw [← Real.exp_add]
    congr 1
    ring
  have hi (ω : Ω) : Integrable (fun ξ => Real.exp (t*(-b ω*⟪z, Y (ω, ξ)⟫+
      8*a^2*‖X ω‖^2+6*a^2*‖Y (ω, ξ)‖^2))) Q := by
    rw [he]
    exact (hy ω).1.const_mul _
  have hcond (ω : Ω) : (∫ ξ, Real.exp (t*(-b ω*⟪z, Y (ω, ξ)⟫+
      8*a^2*‖X ω‖^2+6*a^2*‖Y (ω, ξ)‖^2)) ∂Q) ≤
      Real.exp (8*t*a^2*‖X ω‖^2+C) := by
    rw [he, integral_const_mul, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (hy' ω) (Real.exp_nonneg _)
  have hx' : Integrable (fun ω => Real.exp (8*t*a^2*‖X ω‖^2)) P ∧
      (∫ ω, Real.exp (8*t*a^2*‖X ω‖^2) ∂P) ≤
        Real.exp (8*t*a^2*v+128*t^2*a^4*M^2*v) := by
    convert hx using 1 <;> ring
  have hiG : Integrable (fun ω => Real.exp (8*t*a^2*‖X ω‖^2+C)) P := by
    simp_rw [Real.exp_add]
    exact hx'.1.mul_const _
  have hbG : (∫ ω, Real.exp (8*t*a^2*‖X ω‖^2+C) ∂P) ≤
      Real.exp (t*(a*‖z‖*d+14*a^2*v)+2*t^2*(a^2*‖z‖^2+100*a^4*M^2)*v) := by
    rw [show (fun ω => Real.exp (8*t*a^2*‖X ω‖^2+C)) =
      (fun ω => Real.exp (8*t*a^2*‖X ω‖^2)*Real.exp C) from
        funext (fun ω => Real.exp_add _ _), integral_mul_const]
    have h := mul_le_mul_of_nonneg_right hx'.2 (Real.exp_nonneg C)
    rw [← Real.exp_add] at h
    convert h using 1
    all_goals congr 1; dsimp [C]; ring
  exact LightTail.integral_prod_exp_control (by fun_prop) hi hcond hiG hbG

end OracleTemplate.RobustGradient
