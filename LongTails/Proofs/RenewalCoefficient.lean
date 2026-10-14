import LongTails.Proofs.RenewalAnalytic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology
open Filter

namespace OracleTemplate.MarkovProduct

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

lemma renewal_source_second_local (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) *
      ‖(1 - renewalKernel Φ α (1 - α) 1) * renewalKernel Φ α (1 - α) 1 ^ n‖ ≤ 5)
    {z : ℂ} (hz : ‖z‖ < 1) (hs : ‖z - 1‖ ≤ α / 1024) :
    ‖deriv (deriv (fun w => Ring.inverse (1 - renewalKernel Φ α (1 - α) w) *
      (1 - renewalKernel Φ α (1 - α) 1))) z‖ ≤ 1000000000 / ‖z - 1‖ ^ 2 := by
  let F : ℂ → B →L[ℂ] B := fun w => Ring.inverse (1 - renewalKernel Φ α (1 - α) w) *
    (1 - renewalKernel Φ α (1 - α) 1)
  have hspos : 0 < ‖z - 1‖ := by
    apply norm_pos_iff.mpr
    intro hh
    have hh' : z = 1 := sub_eq_zero.mp hh
    rw [hh', norm_one] at hz
    linarith
  have hpoint (w : ℂ) (hw : w ∈ Metric.closedBall z (‖z - 1‖ / 1024)) :
      AnalyticAt ℂ F w ∧ ‖F w‖ ≤ 300 := by
    obtain ⟨hw1, hws, hwgeo⟩ := local_disk_geometry hα hα1 hz hs
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw)
    obtain ⟨hu, hn⟩ := renewal_local_resolvent Φ hΦ hzero hα hα1 hd hR w hws hw1 hwgeo
    have hqw := (renewal_local_scalar_bounds hα hα1 w hws).1
    exact ⟨renewal_source_analyticAt Φ hΦ α (1 - α) hqw hu _, hn⟩
  have hdF : DifferentiableOn ℂ F (Metric.closedBall z (‖z - 1‖ / 1024)) :=
    fun w hw => (hpoint w hw).1.differentiableAt.differentiableWithinAt
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
    (by positivity : 0 < ‖z - 1‖ / 1024) (hdF.diffContOnCl_ball (Set.Subset.refl _))
    (fun w hw => (hpoint w (Metric.sphere_subset_closedBall hw)).2)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial, Nat.cast_mul,
    Nat.cast_one, mul_one] at hc
  apply hc.trans
  calc
    _ = 629145600 / ‖z - 1‖ ^ 2 := by ring
    _ ≤ _ := by gcongr; norm_num

lemma renewal_source_outer_point (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hs : α / 1024 ≤ ‖z - 1‖)
    (hw : ‖w - z‖ ≤ α / 4096) :
    AnalyticAt ℂ (fun v => Ring.inverse (1 - renewalKernel Φ α (1 - α) v) *
      (1 - renewalKernel Φ α (1 - α) 1)) w ∧
    ‖deriv (fun v => Ring.inverse (1 - renewalKernel Φ α (1 - α) v) *
      (1 - renewalKernel Φ α (1 - α) 1)) w‖ ≤
        400000 * α / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 := by
  obtain ⟨hwb, hsw, hdz, hsz, hlow, hhi, hratio⟩ := outer_disk_geometry hα hα1 hz hs hw
  have hdw0 : 0 < ‖1 - ((1 - α : ℝ) : ℂ) * w‖ := by linarith
  have hdz0 : 0 < ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by linarith
  have hdw : 1 - ((1 - α : ℝ) : ℂ) * w ≠ 0 := norm_pos_iff.mp hdw0
  have hqw : ‖((1 - α : ℝ) : ℂ) * w‖ < 1 := by
    obtain ⟨he, _, _⟩ := renewal_disk_geometry hα1 w hwb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - α)]
    linarith
  have hfirst : ‖Φ 1 - 1‖ ≤ α / 5000 := by simpa only [zero_add, hzero] using hd 0
  have hscalar : 3 / 4099 ≤ ‖1 - renewalScalar α (1 - α) w‖ := by
    rw [renewalScalar_one_sub w hdw, norm_div, norm_sub_rev (1 : ℂ) w]
    exact hratio
  obtain ⟨hu, hn⟩ := scalar_renewal_inverse (renewalKernel Φ α (1 - α) w)
    (renewalScalar α (1 - α) w) hscalar
    (norm_renewalKernel_global Φ hΦ hzero hα hα1 hfirst hsecond w hwb)
  refine ⟨renewal_source_analyticAt Φ hΦ α (1 - α) hqw hu _, ?_⟩
  have hwb' : ‖w‖ ≤ 1 + α / 16 := by
    have hh := norm_sub_norm_le w z
    linarith
  have hKD := norm_renewalKernel_deriv Φ hΦ hzero hα hα1 hfirst hsecond w hwb'
  have hA : ‖1 - renewalKernel Φ α (1 - α) 1‖ ≤ 1 / 5000 := by
    rw [norm_sub_rev]
    exact norm_renewalKernel_one_sub_one Φ hΦ hzero hα hα1 hd
  have hb := norm_renewal_source_deriv _ (renewalKernel_differentiableAt Φ hΦ α (1 - α) hqw) hu _ hn hKD hA
  have hsquare : ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 ≤ 2 * ‖1 - ((1 - α : ℝ) : ℂ) * w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖1 - ((1 - α : ℝ) : ℂ) * w‖ - (4095 / 4096 : ℝ) * ‖1 - ((1 - α : ℝ) : ℂ) * z‖)]
  apply hb.trans
  calc
    _ = 180000 * α / ‖1 - ((1 - α : ℝ) : ℂ) * w‖ ^ 2 := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hdw0) (sq_pos_of_pos hdz0)).mpr
      have hh := mul_le_mul_of_nonneg_left hsquare hα.le
      nlinarith [mul_nonneg hα.le (sq_nonneg ‖1 - ((1 - α : ℝ) : ℂ) * w‖)]

lemma renewal_source_second_outer (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2)
    {z : ℂ} (hz : ‖z‖ < 1) (hs : α / 1024 ≤ ‖z - 1‖) :
    ‖deriv (deriv (fun w => Ring.inverse (1 - renewalKernel Φ α (1 - α) w) *
      (1 - renewalKernel Φ α (1 - α) 1))) z‖ ≤ 10000000000 / ‖z - 1‖ ^ 2 := by
  let F : ℂ → B →L[ℂ] B := fun w => Ring.inverse (1 - renewalKernel Φ α (1 - α) w) *
    (1 - renewalKernel Φ α (1 - α) 1)
  have hpoint (w : ℂ) (hw : w ∈ Metric.closedBall z (α / 4096)) :=
    renewal_source_outer_point Φ hΦ hzero hα hα1 hd hsecond hz.le hs
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw)
  have hdF : DifferentiableOn ℂ (deriv F) (Metric.closedBall z (α / 4096)) :=
    fun w hw => (hpoint w hw).1.deriv.differentiableAt.differentiableWithinAt
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : 0 < α / 4096) (hdF.diffContOnCl_ball (Set.Subset.refl _))
    (fun w hw => (hpoint w (Metric.sphere_subset_closedBall hw)).2)
  obtain ⟨hdz, hsz⟩ := refresh_denominator_base hα hα1 hz.le
  have hd0 : 0 < ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by linarith
  have hs0 : 0 < ‖z - 1‖ := by linarith
  apply hc.trans
  calc
    _ = 1638400000 / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ^ 2 := by field_simp; ring
    _ ≤ 6553600000 / ‖z - 1‖ ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (sq_pos_of_pos hs0)).mpr
      nlinarith [sq_nonneg (2 * ‖1 - ((1 - α : ℝ) : ℂ) * z‖ - ‖z - 1‖)]
    _ ≤ _ := by gcongr; norm_num

lemma renewal_source_second_bound (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) *
      ‖(1 - renewalKernel Φ α (1 - α) 1) * renewalKernel Φ α (1 - α) 1 ^ n‖ ≤ 5)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖deriv (deriv (fun w => Ring.inverse (1 - renewalKernel Φ α (1 - α) w) *
      (1 - renewalKernel Φ α (1 - α) 1))) z‖ ≤ 10000000000 / ‖1 - z‖ ^ 2 := by
  rw [norm_sub_rev (1 : ℂ) z]
  by_cases hs : ‖z - 1‖ ≤ α / 1024
  · exact (renewal_source_second_local Φ hΦ hzero hα hα1 hd hR hz hs).trans (by gcongr; norm_num)
  · exact renewal_source_second_outer Φ hΦ hzero hα hα1 hd hsecond hz (le_of_not_ge hs)

lemma renewal_source_coefficient_bound (Φ V : ℕ → B →L[ℂ] B)
    (hΦ : ∀ k, ‖Φ k‖ ≤ 1) (hV : ∀ k, ‖V k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) *
      ‖(1 - renewalKernel Φ α (1 - α) 1) * renewalKernel Φ α (1 - α) 1 ^ n‖ ≤ 5)
    (hrec : ∀ n, V (n + 1) = (((1 - α : ℝ) : ℂ)) ^ n • Φ (n + 1) + ∑ k ∈ Finset.range n,
      ((α : ℂ) * (((1 - α : ℝ) : ℂ)) ^ k) • (Φ (k + 1) * V (n - k)))
    (n : ℕ) (hn : 1 ≤ n) :
    ‖renewalScaling (α : ℂ) V n * (1 - renewalKernel Φ α (1 - α) 1)‖ ≤ 100000000000 / n := by
  let A : B →L[ℂ] B := 1 - renewalKernel Φ α (1 - α) 1
  let a : ℕ → B →L[ℂ] B := fun n => renewalScaling (α : ℂ) V n * A
  have hA : ‖A‖ ≤ 1 := by
    have hh := norm_renewalKernel_one_sub_one Φ hΦ hzero hα hα1 hd
    rw [norm_sub_rev] at hh
    exact hh.trans (by norm_num)
  have ha : ∀ n, ‖a n‖ ≤ 1 := by
    intro n
    apply (norm_mul_le _ _).trans
    simpa only [one_mul] using
      (mul_le_mul (norm_renewalScaling_le_one V hV hα.le hα1 n) hA (norm_nonneg _) zero_le_one)
  by_cases hn2 : 2 ≤ n
  · have hb : ∀ z : ℂ, ‖z‖ < 1 →
        ‖deriv (deriv (fun w : ℂ => ∑' k, w ^ k • a k)) z‖ ≤ 10000000000 / ‖1 - z‖ ^ 2 := by
      intro z hz
      have he : (fun w : ℂ => ∑' k, w ^ k • a k) =ᶠ[nhds z]
          (fun w => Ring.inverse (1 - renewalKernel Φ α (1 - α) w) * A) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using hz : z ∈ Metric.ball 0 1)] with w hw
        have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
        simpa only [sub_sub_cancel, operatorSeries, a] using! renewal_source_series Φ V hΦ hV
          (by linarith : 0 ≤ 1 - α) (by linarith : 1 - α < 1)
          (by simpa only [sub_sub_cancel] using hrec) A hw'
      rw [he.deriv.deriv_eq]
      exact renewal_source_second_bound Φ hΦ hzero hα hα1 hd hsecond hR hz
    exact (second_deriv_coefficient_bound a ha hb n hn2).trans (by gcongr; norm_num)
  · have hn1 : n = 1 := by omega
    subst n
    exact (ha 1).trans (by norm_num)

end OracleTemplate.MarkovProduct
