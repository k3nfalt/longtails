import LongTails.Proofs.FrankWolfeSetGeometry
import LongTails.Proofs.FrankWolfeGeometry

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.FrankWolfe.HardInstance

open LongTails.Setups.UniformlyConvexHolder

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def coefficient (r : ℝ) : ℝ := 2 / (r * (r - 1) * 2 ^ (r - 2))

noncomputable def objective (r : ℝ) (x : Plane) : ℝ :=
  coefficient r * (1 - x 0) ^ r + x 1 ^ 2

noncomputable def grad (r : ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![-coefficient r * r * (1 - x 0) ^ (r - 1), 2 * x 1]

lemma coefficient_pos {r : ℝ} (hr : 2 < r) : 0 < coefficient r := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  unfold coefficient
  positivity

lemma hasGradient {r : ℝ} (hr : 2 < r) (x : Plane) :
    HasGradientAt (objective r) (grad r x) x := by
  let π0 : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  let π1 : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have h0 := π0.hasFDerivAt (x := x)
  have h1 := π1.hasFDerivAt (x := x)
  have hp := ((hasFDerivAt_const (1 : ℝ) x).sub h0).rpow_const
    (p := r) (Or.inr (by linarith))
  have h := (hp.const_mul (coefficient r)).add (h1.pow 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · funext y
    rfl
  · ext y
    simp [grad, π0, π1, toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_two]
    ring

lemma objective_convex {q r : ℝ} (hq : 2 ≤ q) (hr : 2 < r) :
    ConvexOn ℝ (twoBall q) (objective r) := by
  refine ⟨(twoBall_uniformly_convex hq).convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hqpos : 0 < q := by linarith
  have hx0 : 0 ≤ 1 - x 0 := by
    have := (abs_le.mp (twoBall_coordinates hqpos hx).1).2
    linarith
  have hy0 : 0 ≤ 1 - y 0 := by
    have := (abs_le.mp (twoBall_coordinates hqpos hy).1).2
    linarith
  have hp := (convexOn_rpow (by linarith : 1 ≤ r)).2 hx0 hy0 ha hb hab
  have hs := (show Even (2 : ℕ) by decide).convexOn_pow (𝕜 := ℝ)
  have hsq := hs.2 (Set.mem_univ (x 1)) (Set.mem_univ (y 1)) ha hb hab
  have hmul := mul_le_mul_of_nonneg_left hp (coefficient_pos hr).le
  have heq : 1 - (a * x 0 + b * y 0) = a * (1 - x 0) + b * (1 - y 0) := by
    nlinarith [hab]
  simp only [objective, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [heq]
  simp only [smul_eq_mul] at hmul hsq
  nlinarith

noncomputable def optimum : Plane := WithLp.toLp 2 ![1, 0]

lemma optimum_mem {q : ℝ} (hq : 0 < q) : optimum ∈ twoBall q := by
  rw [mem_twoBall_iff hq]
  simp [optimum, Real.zero_rpow hq.ne']

lemma objective_optimum {r : ℝ} (hr : 2 < r) : objective r optimum = 0 := by
  simp [objective, optimum, Real.zero_rpow (by linarith : r ≠ 0)]

lemma objective_nonneg {q r : ℝ} (hq : 0 < q) (hr : 2 < r) {x : Plane}
    (hx : x ∈ twoBall q) : 0 ≤ objective r x := by
  have hx0 : 0 ≤ 1 - x 0 := by
    have := (abs_le.mp (twoBall_coordinates hq hx).1).2
    linarith
  exact add_nonneg (mul_nonneg (coefficient_pos hr).le (Real.rpow_nonneg hx0 _)) (sq_nonneg _)

lemma optimum_minimizes {q r : ℝ} (hq : 0 < q) (hr : 2 < r) :
    IsMinOn (objective r) (twoBall q) optimum := by
  intro x hx
  rw [objective_optimum hr]
  exact objective_nonneg hq hr hx

noncomputable def normalGradient (r t : ℝ) : ℝ :=
  -coefficient r * r * (1 - t) ^ (r - 1)

lemma normalGradient_derivative {r : ℝ} (hr : 2 < r) (t : ℝ) :
    HasDerivAt (normalGradient r)
      (coefficient r * r * (r - 1) * (1 - t) ^ (r - 2)) t := by
  convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).rpow_const
    (p := r - 1) (Or.inr (by linarith))).const_mul (-coefficient r * r) using 1
  · rfl
  · dsimp
    rw [show r - 1 - 1 = r - 2 by ring]
    ring

lemma normalGradient_derivative_bound {r t : ℝ} (hr : 2 < r) (ht : t ∈ Icc (-1 : ℝ) 1) :
    |coefficient r * r * (r - 1) * (1 - t) ^ (r - 2)| ≤ 2 := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have ht0 : 0 ≤ 1 - t := by linarith [ht.2]
  have ht2 : 1 - t ≤ 2 := by linarith [ht.1]
  have hc := coefficient_pos hr
  have hp := Real.rpow_le_rpow ht0 ht2 (by linarith : 0 ≤ r - 2)
  have hmult := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg hc.le hr0.le) hr1.le)
  have heq : coefficient r * r * (r - 1) * 2 ^ (r - 2) = 2 := by
    unfold coefficient
    field_simp
  rw [abs_of_nonneg (by positivity)]
  exact hmult.trans_eq heq

lemma normalGradient_lipschitz {r a b : ℝ} (hr : 2 < r)
    (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) :
    |normalGradient r a - normalGradient r b| ≤ 2 * |a - b| := by
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (normalGradient_derivative hr t).differentiableAt)
    (fun t ht => by
      rw [(normalGradient_derivative hr t).deriv, Real.norm_eq_abs]
      exact normalGradient_derivative_bound hr ht) hb ha
  simpa only [Real.norm_eq_abs] using h

lemma grad_lipschitz {q r : ℝ} (hq : 0 < q) (hr : 2 < r) {x y : Plane}
    (hx : x ∈ twoBall q) (hy : y ∈ twoBall q) : ‖grad r x - grad r y‖ ≤ 2 * ‖x - y‖ := by
  have hx0 := abs_le.mp (twoBall_coordinates hq hx).1
  have hy0 := abs_le.mp (twoBall_coordinates hq hy).1
  have h := normalGradient_lipschitz hr hx0 hy0
  have hs := mul_self_le_mul_self (abs_nonneg (normalGradient r (x 0) - normalGradient r (y 0))) h
  have hs' : (normalGradient r (x 0) - normalGradient r (y 0)) ^ 2 ≤ 4 * (x 0 - y 0) ^ 2 := by
    nlinarith [sq_abs (normalGradient r (x 0) - normalGradient r (y 0)), sq_abs (x 0 - y 0)]
  have hn : ‖grad r x - grad r y‖ ^ 2 =
      (normalGradient r (x 0) - normalGradient r (y 0)) ^ 2 + 4 * (x 1 - y 1) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, grad, normalGradient, Real.norm_eq_abs, sq_abs]
    ring
  have hd : ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg (grad r x - grad r y), norm_nonneg (x - y)]

noncomputable def errorConstant (r : ℝ) : ℝ :=
  (2 ^ (r / 2 - 1) * (1 + 1 / coefficient r)) ^ (1 / r)

lemma errorConstant_pos {r : ℝ} (hr : 2 < r) : 0 < errorConstant r := by
  have hc := coefficient_pos hr
  unfold errorConstant
  positivity

lemma holder_bound {q r : ℝ} (hq : 0 < q) (hr : 2 < r) {x : Plane}
    (hx : x ∈ twoBall q) : ‖x - optimum‖ ≤ errorConstant r * (objective r x) ^ (1 / r) := by
  have hrpos : 0 < r := by linarith
  have hc := coefficient_pos hr
  have hx0 := (abs_le.mp (twoBall_coordinates hq hx).1).2
  have hy := (twoBall_coordinates hq hx).2
  have hu : 0 ≤ 1 - x 0 := by linarith
  have hh := objective_nonneg hq hr hx
  have hp := (twoGauge_euclidean_bounds (by linarith : 2 ≤ r) (x - optimum)).2
  rw [twoGauge_power hrpos] at hp
  have hnormal : |x 0 - 1| = 1 - x 0 := by rw [abs_of_nonpos (by linarith)]; ring
  simp only [PiLp.sub_apply, optimum, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero, hnormal] at hp
  have htail : |x 1| ^ r ≤ x 1 ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg (x 1)) hy
      (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ r)
    simpa [Real.rpow_two, sq_abs] using h
  have hfirst : (1 - x 0) ^ r ≤ objective r x / coefficient r := by
    apply (le_div_iff₀ hc).mpr
    dsimp [objective]
    nlinarith [sq_nonneg (x 1)]
  have hsecond : |x 1| ^ r ≤ objective r x := by
    dsimp [objective]
    nlinarith [mul_nonneg hc.le (Real.rpow_nonneg hu r)]
  let K := 2 ^ (r / 2 - 1) * (1 + 1 / coefficient r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpower : ‖x - optimum‖ ^ r ≤ K * objective r x := by
    calc
      _ ≤ 2 ^ (r / 2 - 1) * ((1 - x 0) ^ r + |x 1| ^ r) := hp
      _ ≤ 2 ^ (r / 2 - 1) * (objective r x / coefficient r + objective r x) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by positivity)
      _ = K * objective r x := by dsimp [K]; ring
  have ht := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hpower
    (div_nonneg zero_le_one hrpos.le)
  rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hrpos.ne', Real.rpow_one,
    Real.mul_rpow hK hh] at ht
  exact ht

end OracleTemplate.FrankWolfe.HardInstance
