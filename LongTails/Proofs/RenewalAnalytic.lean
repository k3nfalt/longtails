import LongTails.Proofs.MarkovRenewalBounds
import LongTails.Proofs.BanachPowerSeries
import Mathlib.Analysis.Complex.Liouville

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace OracleTemplate.MarkovProduct

open Complex

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

lemma renewalKernel_analyticAt (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (α q : ℝ) {z : ℂ} (hz : ‖(q : ℂ) * z‖ < 1) :
    AnalyticAt ℂ (renewalKernel Φ α q) z := by
  have hs := (coeffSeries_analytic (fun k => Φ (k + 1)) (fun k => hΦ (k + 1))) ((q : ℂ) * z)
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have hh := hs.comp (analyticAt_const.mul analyticAt_id)
  exact (analyticAt_const.mul analyticAt_id).smul hh

lemma renewalKernel_differentiableAt (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (α q : ℝ) {z : ℂ} (hz : ‖(q : ℂ) * z‖ < 1) :
    DifferentiableAt ℂ (renewalKernel Φ α q) z :=
  (renewalKernel_analyticAt Φ hΦ α q hz).differentiableAt

lemma renewal_source_analyticAt (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (α q : ℝ) {z : ℂ} (hz : ‖(q : ℂ) * z‖ < 1)
    (hu : IsUnit (1 - renewalKernel Φ α q z)) (A : B →L[ℂ] B) :
    AnalyticAt ℂ (fun w => Ring.inverse (1 - renewalKernel Φ α q w) * A) z := by
  have hK := renewalKernel_analyticAt Φ hΦ α q hz
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) (A := B →L[ℂ] B)) _ hu
  have hb : AnalyticAt ℂ (fun w => 1 - renewalKernel Φ α q w) z := analyticAt_const.sub hK
  exact (hi.comp (f := fun w : ℂ => 1 - renewalKernel Φ α q w) (x := z) hb).mul analyticAt_const

lemma renewalScalar_hasDerivAt (α q : ℝ) {z : ℂ} (hz : 1 - (q : ℂ) * z ≠ 0) :
    HasDerivAt (renewalScalar α q) ((α : ℂ) / (1 - (q : ℂ) * z) ^ 2) z := by
  have hh := (((hasDerivAt_id z).const_mul (α : ℂ)).div
    ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (q : ℂ))) hz)
  convert hh using 1
  · rfl
  · dsimp only [Pi.sub_apply, id_eq]
    congr 1
    ring

lemma norm_renewalKernel_weighted_error (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hfirst : ‖Φ 1 - 1‖ ≤ α / 5000)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2)
    (z : ℂ) (hz : ‖z‖ ≤ 1 + α / 8) :
    ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 *
      ‖renewalKernel Φ α (1 - α) z - renewalScalar α (1 - α) z • 1‖ ≤ α ^ 2 / 100 := by
  obtain ⟨he, hd, ht⟩ := renewal_disk_geometry hα1 z hz
  have hq : 0 ≤ 1 - α := by linarith
  have hq1 : 1 - α ≤ 1 := by linarith
  have he0 : 0 < 1 - (1 - α) * ‖z‖ := by linarith
  have hn := norm_renewalKernel_abel_difference Φ hΦ hzero hα.le hq hfirst hsecond z (by linarith)
  have hf : α * ‖z‖ * (α / 5000) ≤ α ^ 2 / 200 := by
    have hh := mul_le_mul_of_nonneg_left ht (sq_nonneg α)
    nlinarith
  have hs : α * (1 - α) * ‖z‖ ^ 2 * ((α / 5000) ^ 2 / (1 - (1 - α) * ‖z‖)) ≤ α ^ 2 / 200 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ he0).mpr
    calc
      _ ≤ α * 1 * (9 / 8) ^ 2 * (α / 5000) ^ 2 := by gcongr
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left he (sq_nonneg α)
        nlinarith [pow_pos hα 3]
  linarith

lemma renewal_derivative_disk {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {z w : ℂ} (hz : ‖z‖ ≤ 1 + α / 16) (hw : ‖w - z‖ ≤ α / 32) :
    ‖w‖ ≤ 1 + α / 8 ∧
      15 * α / 16 ≤ ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ∧
      ‖1 - ((1 - α : ℝ) : ℂ) * z‖ / 2 ≤ ‖1 - ((1 - α : ℝ) : ℂ) * w‖ := by
  have hq : 0 ≤ 1 - α := by linarith
  have hq1 : 1 - α ≤ 1 := by linarith
  have hn := norm_sub_norm_le w z
  have hmul := mul_le_mul_of_nonneg_left hz hq
  have hd := norm_sub_norm_le (1 : ℂ) (((1 - α : ℝ) : ℂ) * z)
  have hqn : ‖((1 - α : ℝ) : ℂ)‖ = 1 - α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  rw [norm_one, norm_mul, hqn] at hd
  have hd0 : 15 * α / 16 ≤ ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by nlinarith [sq_nonneg α]
  have hdif : ‖(1 - ((1 - α : ℝ) : ℂ) * z) - (1 - ((1 - α : ℝ) : ℂ) * w)‖ ≤ α / 32 := by
    rw [show (1 - ((1 - α : ℝ) : ℂ) * z) - (1 - ((1 - α : ℝ) : ℂ) * w) =
      ((1 - α : ℝ) : ℂ) * (w - z) by ring, norm_mul, hqn]
    calc
      _ ≤ 1 * (α / 32) := mul_le_mul hq1 hw (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hh := norm_sub_norm_le (1 - ((1 - α : ℝ) : ℂ) * z) (1 - ((1 - α : ℝ) : ℂ) * w)
  exact ⟨by linarith, hd0, by linarith⟩

lemma norm_renewalKernel_error_deriv (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hfirst : ‖Φ 1 - 1‖ ≤ α / 5000)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2)
    (z : ℂ) (hz : ‖z‖ ≤ 1 + α / 16) :
    ‖deriv (fun w => renewalKernel Φ α (1 - α) w - renewalScalar α (1 - α) w • 1) z‖ ≤
      2 * α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 := by
  let f : ℂ → B →L[ℂ] B := fun w => renewalKernel Φ α (1 - α) w - renewalScalar α (1 - α) w • 1
  have hg (w : ℂ) (hw : w ∈ Metric.closedBall z (α / 32)) :=
    renewal_derivative_disk hα hα1 hz (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw)
  have hd : DifferentiableOn ℂ f (Metric.closedBall z (α / 32)) := by
    intro w hw
    obtain ⟨hwb, hdz, hdw⟩ := hg w hw
    obtain ⟨he, he', _⟩ := renewal_disk_geometry hα1 w hwb
    have hqw : ‖((1 - α : ℝ) : ℂ) * w‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - α)]
      linarith
    have hn : 1 - ((1 - α : ℝ) : ℂ) * w ≠ 0 := by
      apply norm_ne_zero_iff.mp
      linarith [norm_nonneg (1 - ((1 - α : ℝ) : ℂ) * w)]
    exact ((renewalKernel_differentiableAt Φ hΦ α (1 - α) hqw).sub
      ((renewalScalar_hasDerivAt α (1 - α) hn).differentiableAt.smul_const 1)).differentiableWithinAt
  have hdz := (renewal_derivative_disk hα hα1 hz (w := z) (by simp; positivity)).2.1
  have hdz0 : 0 < ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by linarith
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < α / 32)
    (hd.diffContOnCl_ball (Set.Subset.refl _)) (C := 4 * α ^ 2 / (100 * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2))
    (fun w hw => show ‖f w‖ ≤ _ from by
      obtain ⟨hwb, _, hdw⟩ := hg w (Metric.sphere_subset_closedBall hw)
      have hn := norm_renewalKernel_weighted_error Φ hΦ hzero hα hα1 hfirst hsecond w hwb
      have hs : ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 / 4 ≤ ‖1 - ((1 - α : ℝ) : ℂ) * w‖ ^ 2 := by
        nlinarith [sq_nonneg (‖1 - ((1 - α : ℝ) : ℂ) * w‖ - ‖1 - ((1 - α : ℝ) : ℂ) * z‖ / 2)]
      have hm := mul_le_mul_of_nonneg_right hs (norm_nonneg (f w))
      apply (le_div_iff₀ (by positivity : 0 < 100 * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2)).mpr
      dsimp [f] at hm ⊢
      nlinarith)
  apply hc.trans
  calc
    _ = (32 / 25) * α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 := by field_simp; ring
    _ ≤ _ := by gcongr; norm_num

lemma norm_renewalKernel_deriv (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hfirst : ‖Φ 1 - 1‖ ≤ α / 5000)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2)
    (z : ℂ) (hz : ‖z‖ ≤ 1 + α / 16) :
    ‖deriv (renewalKernel Φ α (1 - α)) z‖ ≤
      100 * α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 := by
  obtain ⟨he, hd, ht⟩ := renewal_disk_geometry hα1 z (by linarith)
  have hq : 0 ≤ 1 - α := by linarith
  have hqw : ‖((1 - α : ℝ) : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    linarith
  have hn : 1 - ((1 - α : ℝ) : ℂ) * z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    linarith [norm_nonneg (1 - ((1 - α : ℝ) : ℂ) * z)]
  have hK := renewalKernel_differentiableAt Φ hΦ α (1 - α) hqw
  have hr := (renewalScalar_hasDerivAt α (1 - α) hn).smul_const (1 : B →L[ℂ] B)
  have heq := (hK.hasDerivAt.sub hr).deriv
  have herr := norm_renewalKernel_error_deriv Φ hΦ hzero hα hα1 hfirst hsecond z hz
  change deriv (fun w => renewalKernel Φ α (1 - α) w - renewalScalar α (1 - α) w • 1) z = _ at heq
  rw [heq] at herr
  have hrs : ‖((α : ℂ) / (1 - ((1 - α : ℝ) : ℂ) * z) ^ 2) • (1 : B →L[ℂ] B)‖ ≤
      α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 := by
    rw [norm_smul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα.le]
    have hid : ‖(1 : B →L[ℂ] B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hid
      (by positivity : 0 ≤ α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2)
  have hh := norm_sub_norm_le (deriv (renewalKernel Φ α (1 - α)) z)
    (((α : ℂ) / (1 - ((1 - α : ℝ) : ℂ) * z) ^ 2) • (1 : B →L[ℂ] B))
  calc
    _ ≤ 2 * α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 + α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 := by linarith
    _ = 3 * α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 := by ring
    _ ≤ _ := by gcongr; norm_num

lemma scalar_renewal_inverse (K : B →L[ℂ] B) (r : ℂ)
    (hr : 3 / 4099 ≤ ‖1 - r‖) (hK : ‖K - r • 1‖ ≤ 3 / 10000) :
    IsUnit (1 - K) ∧ ‖Ring.inverse (1 - K)‖ ≤ 3000 := by
  have hd : 0 < ‖1 - r‖ := by linarith
  have hr0 : 1 - r ≠ 0 := norm_pos_iff.mp hd
  have hX : IsUnit ((1 - r) • (1 : B →L[ℂ] B)) :=
    IsUnit.smul (Units.mk0 (1 - r) hr0) isUnit_one
  have hinv : Ring.inverse ((1 - r) • (1 : B →L[ℂ] B)) = (1 - r)⁻¹ • 1 := by
    symm
    apply (Ring.eq_mul_inverse_iff_mul_eq _ 1 _ hX).mpr
    simp only [mul_smul_comm, smul_smul, mul_one, mul_inv_cancel₀ hr0, one_smul]
  have hn : ‖Ring.inverse ((1 - r) • (1 : B →L[ℂ] B))‖ ≤ 1 / ‖1 - r‖ := by
    rw [hinv, norm_smul, norm_inv, one_div]
    have hid : ‖(1 : B →L[ℂ] B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hid
      (by positivity : 0 ≤ ‖1 - r‖⁻¹)
  have hsmall : ‖Ring.inverse ((1 - r) • (1 : B →L[ℂ] B)) * (-(K - r • 1))‖ ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ ‖Ring.inverse ((1 - r) • (1 : B →L[ℂ] B))‖ * ‖-(K - r • 1)‖ := norm_mul_le _ _
      _ ≤ (1 / ‖1 - r‖) * (3 / 10000) := by rw [norm_neg]; gcongr
      _ ≤ 1 / 2 := by rw [one_div, mul_comm, ← div_eq_mul_inv, div_le_iff₀ hd]; linarith
  have hp := inverse_add_source_bound ((1 - r) • (1 : B →L[ℂ] B)) (-(K - r • 1)) 1 hX
    (by norm_num : (1 / 2 : ℝ) < 1) hsmall
  have he : (1 - r) • (1 : B →L[ℂ] B) + -(K - r • 1) = 1 - K := by module
  rw [he, mul_one, mul_one] at hp
  norm_num at hp
  exact ⟨hp.1, hp.2.trans (by calc
    _ ≤ 2 * (1 / ‖1 - r‖) := by gcongr
    _ ≤ 3000 := by rw [← mul_div_assoc, mul_one, div_le_iff₀ hd]; linarith)⟩

lemma renewal_source_hasDerivAt (K : ℂ → B →L[ℂ] B) {z : ℂ} {K' : B →L[ℂ] B}
    (hK : HasDerivAt K K' z) (hunit : IsUnit (1 - K z)) (A : B →L[ℂ] B) :
    HasDerivAt (fun w => Ring.inverse (1 - K w) * A)
      (Ring.inverse (1 - K z) * K' * Ring.inverse (1 - K z) * A) z := by
  obtain ⟨u, hu⟩ := hunit
  have hf := hasFDerivAt_ringInverse (𝕜 := ℂ) u
  rw [hu] at hf
  have hi := hf.comp_hasDerivAt z
    (show HasDerivAt (fun w => 1 - K w) (-K') z by simpa using hK.const_sub 1)
  have he : (↑u⁻¹ : B →L[ℂ] B) = Ring.inverse (1 - K z) := by
    rw [← hu, Ring.inverse_unit]
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    he, mul_neg, neg_mul, neg_neg, Function.comp_apply] using! hi.mul_const A

lemma norm_renewal_source_deriv (K : ℂ → B →L[ℂ] B) {z : ℂ}
    (hK : DifferentiableAt ℂ K z) (hunit : IsUnit (1 - K z))
    (A : B →L[ℂ] B) {M D C : ℝ} (hM : ‖Ring.inverse (1 - K z)‖ ≤ M)
    (hD : ‖deriv K z‖ ≤ D) (hC : ‖A‖ ≤ C) :
    ‖deriv (fun w => Ring.inverse (1 - K w) * A) z‖ ≤ M ^ 2 * D * C := by
  rw [(renewal_source_hasDerivAt K hK.hasDerivAt hunit A).deriv]
  have hM0 := (norm_nonneg _).trans hM
  have hD0 := (norm_nonneg _).trans hD
  have hC0 := (norm_nonneg _).trans hC
  calc
    _ ≤ ‖Ring.inverse (1 - K z)‖ * ‖deriv K z‖ * ‖Ring.inverse (1 - K z)‖ * ‖A‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ M * D * M * C := by gcongr
    _ = _ := by ring

lemma local_disk_geometry {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {z w : ℂ} (hz : ‖z‖ < 1) (hs : ‖z - 1‖ ≤ α / 1024)
    (hw : ‖w - z‖ ≤ ‖z - 1‖ / 1024) :
    w ≠ 1 ∧ ‖w - 1‖ ≤ α / 512 ∧
      (w - 1).re + ‖w - 1‖ ^ 2 ≤ |(w - 1).im| / 128 := by
  let s : ℝ := ‖z - 1‖
  have hs0 : 0 < s := by
    apply norm_pos_iff.mpr
    intro he
    have he' : z = 1 := sub_eq_zero.mp he
    simp [he'] at hz
  have hs1 : s ≤ 1 / 1024 := by dsimp [s]; linarith
  have hsq : s ^ 2 ≤ s / 1024 := by nlinarith
  have hnorm : ‖w - 1‖ ≤ s + s / 1024 := by
    calc
      _ = ‖(w - z) + (z - 1)‖ := by congr 1; ring
      _ ≤ ‖w - z‖ + ‖z - 1‖ := norm_add_le _ _
      _ ≤ _ := by dsimp [s] at *; linarith
  have hnormsq : ‖w - 1‖ ^ 2 ≤ 2 * s ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (w - 1)) hnorm 2
    nlinarith [sq_nonneg s]
  have hre : (z - 1).re ≤ 0 := by
    have h := Complex.re_le_norm z
    simp only [sub_re, one_re]
    linarith
  have heRe : |(w - z).re| ≤ s / 1024 := (Complex.abs_re_le_norm _).trans hw
  have heIm : |(w - z).im| ≤ s / 1024 := (Complex.abs_im_le_norm _).trans hw
  have hwRe : (w - 1).re ≤ (z - 1).re + s / 1024 := by
    have h := (le_abs_self (w - z).re).trans heRe
    simp only [sub_re, one_re] at *
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro he
    subst w
    have heq : ‖(1 : ℂ) - z‖ = s := by dsimp [s]; exact norm_sub_rev _ _
    rw [heq] at hw
    linarith
  · dsimp [s] at hnorm
    linarith
  · by_cases hc : (z - 1).re ≤ -s / 4
    · have hi := abs_nonneg (w - 1).im
      nlinarith
    · have habsre : |(z - 1).re| ≤ s / 4 := by rw [abs_of_nonpos hre]; linarith
      have hd := Complex.norm_le_abs_re_add_abs_im (z - 1)
      have him : 3 * s / 4 ≤ |(z - 1).im| := by change s ≤ _ at hd; linarith
      have he : |(z - 1).im| ≤ |(w - 1).im| + |(w - z).im| := by
        have hh := abs_sub_le (w - 1).im 0 (w - z).im
        simp only [sub_zero, zero_sub, abs_neg] at hh
        have hid : (w - 1).im - (w - z).im = (z - 1).im := by simp
        rwa [hid] at hh
      have himw : s / 2 ≤ |(w - 1).im| := by linarith
      nlinarith


lemma refresh_denominator_base {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    α ≤ ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ∧
      ‖z - 1‖ ≤ 2 * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by
  have hq : 0 ≤ 1 - α := by linarith
  have hqnorm : ‖((1 - α : ℝ) : ℂ)‖ = 1 - α := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  have htri : 1 ≤ ‖1 - ((1 - α : ℝ) : ℂ) * z‖ + (1 - α) * ‖z‖ := by
    have h := norm_add_le (1 - ((1 - α : ℝ) : ℂ) * z) (((1 - α : ℝ) : ℂ) * z)
    simpa only [sub_add_cancel, norm_one, norm_mul, hqnorm] using h
  have hl : α ≤ ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by nlinarith
  refine ⟨hl, ?_⟩
  have he : z - 1 = -(1 - ((1 - α : ℝ) : ℂ) * z) + (α : ℂ) * z := by push_cast; ring
  rw [he]
  have hn : ‖(α : ℂ)‖ = α := by simp [abs_of_pos hα]
  calc
    _ ≤ ‖-(1 - ((1 - α : ℝ) : ℂ) * z)‖ + ‖(α : ℂ) * z‖ := norm_add_le _ _
    _ = ‖1 - ((1 - α : ℝ) : ℂ) * z‖ + α * ‖z‖ := by rw [norm_neg, norm_mul, hn]
    _ ≤ _ := by nlinarith

lemma outer_disk_geometry {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hs : α / 1024 ≤ ‖z - 1‖)
    (hw : ‖w - z‖ ≤ α / 4096) :
    ‖w‖ ≤ 1 + α / 8 ∧ 3 * α / 4096 ≤ ‖w - 1‖ ∧
      α ≤ ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ∧
      ‖z - 1‖ ≤ 2 * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ∧
      (4095 / 4096 : ℝ) * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ≤ ‖1 - ((1 - α : ℝ) : ℂ) * w‖ ∧
      ‖1 - ((1 - α : ℝ) : ℂ) * w‖ ≤ (4097 / 4096 : ℝ) * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ∧
      (3 / 4099 : ℝ) ≤ ‖w - 1‖ / ‖1 - ((1 - α : ℝ) : ℂ) * w‖ := by
  have hq : 0 ≤ 1 - α := by linarith
  have hqnorm : ‖((1 - α : ℝ) : ℂ)‖ = 1 - α := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  have hnw : ‖w‖ ≤ 1 + α / 4096 := by
    have h := norm_add_le (w - z) z
    rw [sub_add_cancel] at h
    linarith
  have hsw : 3 * α / 4096 ≤ ‖w - 1‖ := by
    have h := norm_sub_norm_le (z - 1) (w - 1)
    have he : (z - 1) - (w - 1) = -(w - z) := by ring
    rw [he, norm_neg] at h
    linarith
  obtain ⟨hdz, hsz⟩ := refresh_denominator_base hα hα1 hz
  have hdiff : ‖(1 - ((1 - α : ℝ) : ℂ) * w) - (1 - ((1 - α : ℝ) : ℂ) * z)‖ ≤ α / 4096 := by
    have he : (1 - ((1 - α : ℝ) : ℂ) * w) - (1 - ((1 - α : ℝ) : ℂ) * z) =
        -((1 - α : ℝ) : ℂ) * (w - z) := by ring
    rw [he, norm_mul, norm_neg, hqnorm]
    nlinarith [norm_nonneg (w - z)]
  have hdlo : (4095 / 4096 : ℝ) * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ≤ ‖1 - ((1 - α : ℝ) : ℂ) * w‖ := by
    have h := norm_sub_norm_le (1 - ((1 - α : ℝ) : ℂ) * z) (1 - ((1 - α : ℝ) : ℂ) * w)
    rw [norm_sub_rev (1 - ((1 - α : ℝ) : ℂ) * z) (1 - ((1 - α : ℝ) : ℂ) * w)] at h
    linarith
  have hdhi : ‖1 - ((1 - α : ℝ) : ℂ) * w‖ ≤ (4097 / 4096 : ℝ) * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by
    have h := norm_sub_norm_le (1 - ((1 - α : ℝ) : ℂ) * w) (1 - ((1 - α : ℝ) : ℂ) * z)
    linarith
  refine ⟨by linarith, hsw, hdz, hsz, hdlo, hdhi, ?_⟩
  have hdpos : 0 < ‖1 - ((1 - α : ℝ) : ℂ) * w‖ := by linarith
  have hdup : ‖1 - ((1 - α : ℝ) : ℂ) * w‖ ≤ α + ‖w - 1‖ := by
    have he : 1 - ((1 - α : ℝ) : ℂ) * w = (α : ℂ) + ((1 - α : ℝ) : ℂ) * (1 - w) := by push_cast; ring
    rw [he]
    have hn : ‖(α : ℂ)‖ = α := by simp [abs_of_pos hα]
    calc
      _ ≤ ‖(α : ℂ)‖ + ‖((1 - α : ℝ) : ℂ) * (1 - w)‖ := norm_add_le _ _
      _ = α + (1 - α) * ‖w - 1‖ := by rw [hn, norm_mul, hqnorm, norm_sub_rev]
      _ ≤ _ := by nlinarith [norm_nonneg (w - 1)]
  apply (le_div_iff₀ hdpos).mpr
  nlinarith


end OracleTemplate.MarkovProduct
