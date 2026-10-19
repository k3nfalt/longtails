import LongTails.Proofs.SymmetricReverseFisherDynamics
open scoped RealInnerProductSpace
namespace LongTails.Proofs.SymmetricReverseFisherTrajectory
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherCoefficients
open LongTails.Proofs.SymmetricReverseFisherDynamics
noncomputable def transverse {p : Params} (e x : Space p) : Space p := x - ⟪x, e⟫ • e
lemma transverse_orthogonal {p : Params} (e x : Space p) (he : ‖e‖ = 1) :
    ⟪transverse e x, e⟫ = 0 := by
  rw [transverse, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
  ring
lemma coordinate_decomposition {p : Params} (e x : Space p) : ⟪x, e⟫ • e + transverse e x = x := by
  unfold transverse
  module
lemma inner_step {p : Params} (e x : Space p) {a η : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a) :
    ⟪gdStep (a • e) η x, e⟫ =
      (1 - η * alpha ‖x‖ + η * beta a (a * ⟪x, e⟫) * a ^ 2) * ⟪x, e⟫ := by
  have h := gdStep_coordinates e (transverse e x) a ⟪x, e⟫ η ha he (transverse_orthogonal e x he)
  rw [coordinate_decomposition] at h
  rw [h, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    transverse_orthogonal e x he, real_inner_self_eq_norm_sq, he]
  ring
lemma transverse_step {p : Params} (e x : Space p) {a η : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a) :
    transverse e (gdStep (a • e) η x) = (1 - η * alpha ‖x‖) • transverse e x := by
  have h := gdStep_coordinates e (transverse e x) a ⟪x, e⟫ η ha he (transverse_orthogonal e x he)
  rw [coordinate_decomposition] at h
  unfold transverse at ⊢
  rw [inner_step e x he ha, h]
  unfold transverse
  module
lemma inner_iterate_pos {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48)
    (hx : 0 < ⟪x, e⟫) (k : ℕ) : 0 < ⟪(gdStep (a • e) η)^[k] x, e⟫ := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply', inner_step e _ he ha]
    have hl := (lambda_bounds (r := ‖(gdStep (a • e) η)^[k] x‖) hη hη48).1
    have hb := beta_nonneg a (a * ⟪(gdStep (a • e) η)^[k] x, e⟫)
    apply mul_pos _ ih
    have hp := mul_nonneg (mul_nonneg hη hb) (sq_nonneg a)
    linarith
lemma coordinate_norm {p : Params} (e x : Space p) (he : ‖e‖ = 1) :
    ‖x‖ ^ 2 = ⟪x, e⟫ ^ 2 + ‖transverse e x‖ ^ 2 := by
  have h := orthogonal_norm_sq e (transverse e x) ⟪x, e⟫ he (transverse_orthogonal e x he)
  rw [coordinate_decomposition] at h
  exact h
lemma transverse_step_norm {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48) :
    ‖transverse e (gdStep (a • e) η x)‖ = (1 - η * alpha ‖x‖) * ‖transverse e x‖ := by
  rw [transverse_step e x he ha, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by have h := (lambda_bounds (r := ‖x‖) hη hη48).1; linarith)]
lemma iterate_cone_sq {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48)
    (hx : 0 < ⟪x, e⟫) (hx1 : ‖x‖ = 1) (k : ℕ) :
    ‖transverse e ((gdStep (a • e) η)^[k] x)‖ ^ 2 * ⟪x, e⟫ ^ 2 ≤
      ⟪(gdStep (a • e) η)^[k] x, e⟫ ^ 2 * (1 - ⟪x, e⟫ ^ 2) := by
  have hζ : ⟪x, e⟫ ^ 2 ≤ 1 := by
    have hi := abs_real_inner_le_norm x e
    rw [hx1, he, mul_one, abs_of_pos hx] at hi
    nlinarith
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    have hn := coordinate_norm e x he
    rw [hx1] at hn
    nlinarith [congrArg (fun t : ℝ => t * ⟪x, e⟫ ^ 2) hn]
  | succ k ih =>
    rw [Function.iterate_succ_apply', transverse_step_norm e _ he ha hη hη48,
      inner_step e _ he ha]
    have hl := (lambda_bounds (r := ‖(gdStep (a • e) η)^[k] x‖) hη hη48).1
    have hb : 0 ≤ beta a (a * ⟪(gdStep (a • e) η)^[k] x, e⟫) * a ^ 2 :=
      mul_nonneg (beta_nonneg _ _) (sq_nonneg _)
    have hc := cone_preserved (inner_iterate_pos e x he ha hη hη48 hx k).le
      (norm_nonneg (transverse e ((gdStep (a • e) η)^[k] x)))
      (show 0 ≤ 1 - η * alpha ‖(gdStep (a • e) η)^[k] x‖ by linarith)
      hb hη hζ ih
    simpa only [mul_assoc] using hc
lemma iterate_cone {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48)
    (hx : 0 < ⟪x, e⟫) (hx1 : ‖x‖ = 1) (k : ℕ) :
    ⟪x, e⟫ * ‖(gdStep (a • e) η)^[k] x‖ ≤ ⟪(gdStep (a • e) η)^[k] x, e⟫ := by
  exact cone_radius (inner_iterate_pos e x he ha hη hη48 hx k).le (norm_nonneg _) hx.le
    (coordinate_norm e _ he) (iterate_cone_sq e x he ha hη hη48 hx hx1 k)
noncomputable def signalStrength (a : ℝ) : ℝ := a ^ 2 / (100000 * (1 + a ^ 2))
noncomputable def angleRatio {p : Params} (e x : Space p) : ℝ := ‖transverse e x‖ / ⟪x, e⟫
lemma angleRatio_step {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 < η) (hη48 : η ≤ 1 / 48)
    (hu : 0 < ⟪x, e⟫) (hr : ‖x‖ ≤ 1 + 600 * a) :
    angleRatio e (gdStep (a • e) η x) ≤ angleRatio e x / (1 + η * signalStrength a) := by
  have hm : 0 < signalStrength a := (strength_bounds ha).1
  have hc : a * ⟪x, e⟫ ≤ a * (1 + 600 * a) := by
    have hi := (real_inner_le_norm x e)
    rw [he, mul_one] at hi
    exact mul_le_mul_of_nonneg_left (hi.trans hr) ha.le
  have hb : signalStrength a ≤ beta a (a * ⟪x, e⟫) * a ^ 2 :=
    strength_lower ha.le (mul_nonneg ha.le hu.le) hc
  have hl := lambda_bounds (r := ‖x‖) hη.le hη48
  have hd : 0 < 1 - η * alpha ‖x‖ + η * (beta a (a * ⟪x, e⟫) * a ^ 2) := by
    nlinarith [mul_pos hη (hm.trans_le hb)]
  have hq : 0 ≤ angleRatio e x := div_nonneg (norm_nonneg _) hu.le
  have hh := LongTails.Proofs.SymmetricReverseFisherGeometry.angular_ratio_contraction
    (angleRatio e x) (1 - η * alpha ‖x‖) η (signalStrength a)
    (beta a (a * ⟪x, e⟫) * a ^ 2) hq (by linarith) hl.2 hη hm hb
  unfold angleRatio at ⊢ hh
  rw [transverse_step_norm e x he ha.le hη.le hη48, inner_step e x he ha.le]
  convert hh using 1
  field_simp
lemma angleRatio_iterate {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 < η) (hη48 : η ≤ 1 / 48)
    (hu : 0 < ⟪x, e⟫) (hx : ‖x‖ = 1) (k : ℕ) :
    angleRatio e ((gdStep (a • e) η)^[k] x) ≤
      (1 / (1 + η * signalStrength a)) ^ k * angleRatio e x := by
  have hm : 0 < signalStrength a := (strength_bounds ha).1
  have hh (j : ℕ) : angleRatio e ((gdStep (a • e) η)^[j + 1] x) ≤
      (1 / (1 + η * signalStrength a)) * angleRatio e ((gdStep (a • e) η)^[j] x) := by
    rw [Function.iterate_succ_apply']
    have hr := iterate_radius (a • e) x hη.le hη48 (by rw [hx]; linarith [norm_nonneg (a • e)]) j
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, he, mul_one] at hr
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      angleRatio_step e _ he ha hη hη48 (inner_iterate_pos e x he ha.le hη.le hη48 hu j) hr
  simpa using LongTails.Proofs.SymmetricReverseFisherGeometry.geometric_recurrence
    (fun j => angleRatio e ((gdStep (a • e) η)^[j] x)) (by positivity) hh k
lemma strength_on_ball {p : Params} (e x : Space p) {a : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hu : 0 ≤ ⟪x, e⟫) (hr : ‖x‖ ≤ 1 + 600 * a) :
    signalStrength a ≤ beta a (a * ⟪x, e⟫) * a ^ 2 := by
  have hi := real_inner_le_norm x e
  rw [he, mul_one] at hi
  exact strength_lower ha (mul_nonneg ha hu) (mul_le_mul_of_nonneg_left (hi.trans hr) ha)
lemma inner_step_half {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48)
    (hu : 0 ≤ ⟪x, e⟫) : ⟪x, e⟫ / 2 ≤ ⟪gdStep (a • e) η x, e⟫ := by
  rw [inner_step e x he ha]
  have hl := (lambda_bounds (r := ‖x‖) hη hη48).1
  have hb : 0 ≤ η * beta a (a * ⟪x, e⟫) * a ^ 2 :=
    mul_nonneg (mul_nonneg hη (beta_nonneg _ _)) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hl hu, mul_nonneg hb hu]
lemma inner_step_growth {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hη : 0 ≤ η) (hu : 0 ≤ ⟪x, e⟫)
    (hr : ‖x‖ ≤ 1 + 600 * a) (hsmall : ‖x‖ ^ 2 ≤ signalStrength a / 8) :
    (1 + η * signalStrength a / 2) * ⟪x, e⟫ ≤ ⟪gdStep (a • e) η x, e⟫ := by
  rw [inner_step e x he ha]
  have hb := strength_on_ball e x he ha hu hr
  have hα := (alpha_le_four_min ‖x‖).trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0:ℝ) ≤ 4))
  have hα' : alpha ‖x‖ ≤ signalStrength a / 2 := by linarith
  have hb' := mul_le_mul_of_nonneg_left hb hη
  have hα'' := mul_le_mul_of_nonneg_left hα' hη
  have hc : 1 + η * signalStrength a / 2 ≤
      1 - η * alpha ‖x‖ + η * beta a (a * ⟪x, e⟫) * a ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right hc hu
lemma iterate_inner_floor {p : Params} (e x : Space p) {a η q : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48)
    (hu : 0 < ⟪x, e⟫) (hx : ‖x‖ = 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hqm : q ^ 2 = signalStrength a) (k : ℕ) :
    q / 8 * ⟪x, e⟫ ≤ ⟪(gdStep (a • e) η)^[k] x, e⟫ := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    nlinarith [mul_le_mul_of_nonneg_right hq1 hu.le]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hi := inner_iterate_pos e x he ha.le hη hη48 hu k
    have hh := inner_step_half e ((gdStep (a • e) η)^[k] x) he ha.le hη hη48 hi.le
    by_cases hr : ‖(gdStep (a • e) η)^[k] x‖ ≤ q / 4
    · have hR := iterate_radius (a • e) x hη hη48 (by rw [hx]; linarith [norm_nonneg (a • e)]) k
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, he, mul_one] at hR
      have hs : ‖(gdStep (a • e) η)^[k] x‖ ^ 2 ≤ signalStrength a / 8 := by
        nlinarith [norm_nonneg ((gdStep (a • e) η)^[k] x), sq_nonneg q]
      have hg := inner_step_growth e _ he ha.le hη hi.le hR hs
      have hm : 0 ≤ signalStrength a := (strength_bounds ha).1.le
      have hp := mul_nonneg (mul_nonneg hη hm) hi.le
      nlinarith
    · have hc := iterate_cone e x he ha.le hη hη48 hu hx k
      have hm := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hr)) hu.le
      nlinarith
end LongTails.Proofs.SymmetricReverseFisherTrajectory
