import LongTails.Proofs.SymmetricReverseFisherAlignment
import LongTails.Proofs.SymmetricReverseFisherTrajectory
import LongTails.Proofs.SymmetricReverseFisherEscape
open scoped RealInnerProductSpace
namespace LongTails.Proofs.SymmetricReverseFisherContraction
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherAlignment
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherTrajectory
lemma projected_step_contraction {p : Params} (e x : Space p) {a η q : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hη : 0 ≤ η) (hηL : η * (48 + 20 * a) ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqa : q ≤ a) (hu : q / 8 ≤ ⟪x, e⟫) :
    |⟪gdStep (a • e) η x, e⟫ - a| ≤
      (1 - η * (q ^ 2 / 960)) * |⟪x, e⟫ - a| + 48 * η * ‖transverse e x‖ := by
  have hu0 : 0 < ⟪x,e⟫ := by linarith
  have hp := projected_gradient_perturbation e (transverse e x) he ha hu0.le (transverse_orthogonal e x he)
  rw [coordinate_decomposition] at hp
  have hs := aligned_secant e he ha hu0 hq.le hq1 hqa hu
  have h := perturbed_aligned_contraction (by positivity) hη hηL hs hp
  rw [gdStep, inner_sub_left, real_inner_smul_left]
  convert h using 1
  ring
lemma transverse_le_radius_ratio {p : Params} (e x : Space p) {R : ℝ}
    (he : ‖e‖ = 1) (hu : 0 < ⟪x,e⟫) (hr : ‖x‖ ≤ R) :
    ‖transverse e x‖ ≤ R * angleRatio e x := by
  have hi := real_inner_le_norm x e
  rw [he, mul_one] at hi
  have hq : 0 ≤ angleRatio e x := div_nonneg (norm_nonneg _) hu.le
  have hh := mul_le_mul_of_nonneg_right (hi.trans hr) hq
  have hid : ⟪x,e⟫ * angleRatio e x = ‖transverse e x‖ := by
    unfold angleRatio
    field_simp
  rwa [hid] at hh
lemma norm_error_coordinates {p : Params} (e x : Space p) (a : ℝ) (he : ‖e‖ = 1) :
    ‖x - a • e‖ ≤ |⟪x,e⟫ - a| + ‖transverse e x‖ := by
  have hid : x - a • e = (⟪x,e⟫ - a) • e + transverse e x := by unfold transverse; module
  rw [hid]
  calc
    _ ≤ ‖(⟪x,e⟫ - a) • e‖ + ‖transverse e x‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, he, mul_one]
lemma geometric_gap {η m : ℝ} (hη : 0 < η) (hm : 0 < m) (hηm : η * m ≤ 1) :
    η * m / 3 ≤ (1 - η * m / 960) - 1 / (1 + η * m) := by
  have hd : 0 < 1 + η * m := by positivity
  have hi : 1 / (1 + η * m) ≤ 1 - η * m / 960 - η * m / 3 := by
    apply (div_le_iff₀ hd).mpr
    have ht : 0 < η * m := mul_pos hη hm
    nlinarith [sq_nonneg (η * m), mul_nonneg ht.le (sub_nonneg.mpr hηm)]
  linarith
lemma geometric_tail_envelope (err off : ℕ → ℝ) {η m R a : ℝ}
    (hη : 0 < η) (hm : 0 < m) (hm1 : m ≤ 1) (hηm : η * m ≤ 1)
    (hR : 0 ≤ R) (haR : a ≤ R) (hinit : err 0 ≤ R + a)
    (herr : ∀ k, err (k+1) ≤ (1 - η*m/960) * err k + 48*η*R*(1/(1+η*m))^k)
    (hoff : ∀ k, off k ≤ R*(1/(1+η*m))^k) (k : ℕ) :
    err k + off k ≤ 148 * R / m * Real.exp (-η * m * k / 960) := by
  let A := 1 - η*m/960
  let b := 1/(1+η*m)
  have hA : 0 ≤ A := by dsimp [A]; nlinarith [mul_pos hη hm]
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hgap : η*m/3 ≤ A - b := geometric_gap hη hm hηm
  have hgap0 : 0 < A - b := lt_of_lt_of_le (by positivity) hgap
  have hbA : b < A := sub_pos.mp hgap0
  have hD : 48*η*R/(A-b) ≤ 144*R/m := by
    apply (div_le_iff₀ hgap0).mpr
    have hh := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 144*R/m by positivity)
    have he : (144*R/m)*(η*m/3) = 48*η*R := by field_simp; ring
    rw [he] at hh
    nlinarith
  have hh := LongTails.Proofs.SymmetricReverseFisherGeometry.perturbed_geometric_recurrence
    err hA hb hbA (show 0 ≤ 48*η*R by positivity) herr k
  have hpow := pow_le_pow_left₀ hb hbA.le k
  have ho := (hoff k).trans (mul_le_mul_of_nonneg_left hpow hR)
  have hi : err 0 + 48*η*R/(A-b) ≤ R+a+144*R/m := by linarith
  have he := hh.trans (mul_le_mul_of_nonneg_left hi (pow_nonneg hA k))
  have hRm : R ≤ R/m := (le_div_iff₀ hm).mpr (mul_le_of_le_one_right hR hm1)
  have hc : R+a+144*R/m+R ≤ 148*R/m := by
    have hrm : 0 ≤ R/m := div_nonneg hR hm.le
    simp only [mul_div_assoc]
    linarith
  have hh' : err k + off k ≤ 148*R/m * A^k := by
    have hc' := mul_le_mul_of_nonneg_right hc (pow_nonneg hA k)
    nlinarith
  have hp := LongTails.Proofs.SymmetricReverseFisherGeometry.one_sub_pow_le_exp
    (show 0 ≤ η*m/960 by positivity) (show η*m/960 ≤ 1 by nlinarith [mul_pos hη hm]) k
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 148*R/m by positivity)
  have he : -(η*m/960)*(k:ℝ) = -η*m*k/960 := by ring
  rw [he] at hmul
  exact hh'.trans hmul
lemma convergence_after_escape {p : Params} (e : Space p) (y : ℕ → Space p) {a η q : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 < η) (hη48 : η ≤ 1/48)
    (hηL : η * (48 + 20*a) ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hqa : q ≤ a)
    (hqm : q^2 = signalStrength a)
    (hstep : ∀ k, y (k+1) = gdStep (a • e) η (y k))
    (hr : ∀ k, ‖y k‖ ≤ 1+600*a) (hu : ∀ k, q/8 ≤ ⟪y k,e⟫)
    (hangle : angleRatio e (y 0) ≤ 1) (k : ℕ) :
    ‖y k - a • e‖ ≤ 148*(1+600*a)/signalStrength a *
      Real.exp (-η*signalStrength a*k/960) := by
  have hm := strength_bounds ha
  have hm0 : 0 < signalStrength a := hm.1
  have hm1 : signalStrength a ≤ 1 := hm.2.trans (min_le_right _ _)
  have hηm : η * signalStrength a ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hm1 hη.le]
  have hu0 (j : ℕ) : 0 < ⟪y j,e⟫ := by have h := hu j; linarith
  have hR : 0 ≤ 1+600*a := by positivity
  have hrec (j : ℕ) : angleRatio e (y (j+1)) ≤
      (1/(1+η*signalStrength a)) * angleRatio e (y j) := by
    rw [hstep]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      angleRatio_step e (y j) he ha hη hη48 (hu0 j) (hr j)
  have hang (j : ℕ) : angleRatio e (y j) ≤ (1/(1+η*signalStrength a))^j := by
    have h := LongTails.Proofs.SymmetricReverseFisherGeometry.geometric_recurrence
      (fun i => angleRatio e (y i)) (by positivity) hrec j
    have hh := mul_le_mul_of_nonneg_left hangle (show 0 ≤ (1/(1+η*signalStrength a))^j by positivity)
    exact h.trans (by simpa only [mul_one] using hh)
  have hoff (j : ℕ) : ‖transverse e (y j)‖ ≤ (1+600*a)*(1/(1+η*signalStrength a))^j :=
    (transverse_le_radius_ratio e (y j) he (hu0 j) (hr j)).trans
      (mul_le_mul_of_nonneg_left (hang j) hR)
  have herr (j : ℕ) : |⟪y (j+1),e⟫ - a| ≤
      (1-η*signalStrength a/960)*|⟪y j,e⟫-a| +
        48*η*(1+600*a)*(1/(1+η*signalStrength a))^j := by
    rw [hstep]
    have h := projected_step_contraction e (y j) he ha.le hη.le hηL hq hq1 hqa (hu j)
    rw [hqm] at h
    have hv := mul_le_mul_of_nonneg_left (hoff j) (show 0 ≤ 48*η by positivity)
    nlinarith
  have hinit : |⟪y 0,e⟫-a| ≤ (1+600*a)+a := by
    have hi := real_inner_le_norm (y 0) e
    rw [he, mul_one] at hi
    have hb := abs_sub ⟪y 0,e⟫ a
    rw [abs_of_pos (hu0 0), abs_of_pos ha] at hb
    linarith [hr 0]
  have ht := geometric_tail_envelope (fun j => |⟪y j,e⟫-a|) (fun j => ‖transverse e (y j)‖)
    hη hm0 hm1 hηm hR (show a ≤ 1+600*a by linarith) hinit herr hoff k
  exact (norm_error_coordinates e (y k) a he).trans ht
open LongTails.Proofs.SymmetricReverseFisherEscape

lemma positive_signal_bound {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 < η) (hη48 : η ≤ 1/48)
    (hηL : η * (48 + 20*a) ≤ 1) (hu : 0 < ⟪x,e⟫) (hx : ‖x‖ = 1)
    {n₁ n₂ : ℕ}
    (hn₁ : 2/(η*signalStrength a)*Real.log (1/⟪x,e⟫) ≤ n₁)
    (hn₂ : 4/(η*signalStrength a)*Real.log (1/⟪x,e⟫) ≤ n₂) (k : ℕ) :
    ‖(gdStep (a • e) η)^[n₁+n₂+k] x - a • e‖ ≤
      148*(1+600*a)/signalStrength a * Real.exp (-η*signalStrength a*k/960) := by
  have hm := strength_bounds ha
  have hm0 : 0 < signalStrength a := hm.1
  have hm1 : signalStrength a ≤ 1 := hm.2.trans (min_le_right _ _)
  have hma : signalStrength a ≤ a^2 := hm.2.trans (min_le_left _ _)
  let q := Real.sqrt (signalStrength a)
  have hq : 0 < q := Real.sqrt_pos.mpr hm0
  have hqm : q^2 = signalStrength a := Real.sq_sqrt hm0.le
  have hq1 : q ≤ 1 := by nlinarith
  have hqa : q ≤ a := by nlinarith
  let y := fun j => (gdStep (a • e) η)^[n₁+n₂+j] x
  have hs (j : ℕ) : y (j+1) = gdStep (a • e) η (y j) := by
    dsimp [y]
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
  have hr (j : ℕ) : ‖y j‖ ≤ 1+600*a := by
    have h := iterate_radius (a • e) x hη.le hη48 (by rw [hx]; linarith [norm_nonneg (a • e)]) (n₁+n₂+j)
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, he, mul_one] using h
  have hang := angleRatio_small e x he ha hη hη48 hu hx hn₁
  have hfloor (j : ℕ) : q/8 ≤ ⟪y j,e⟫ := by
    have hn₂' : 4/(η*signalStrength a)*Real.log (1/⟪x,e⟫) ≤ (n₂+j : ℕ) := by
      exact hn₂.trans (by exact_mod_cast Nat.le_add_right n₂ j)
    have h := phase_two_escape e x he ha hη hη48 hu hx hq.le hq1 hqm hang hn₂'
    simpa only [y, Nat.add_assoc] using h
  have hang' : angleRatio e (y 0) ≤ 1 := by
    have h := (angleRatio_antitone e x he ha hη hη48 hu hx (Nat.le_add_right n₁ n₂)).trans hang
    simpa only [y, Nat.add_zero] using h
  exact convergence_after_escape e y he ha hη hη48 hηL hq hq1 hqa hqm hs hr hfloor hang' k

end LongTails.Proofs.SymmetricReverseFisherContraction
