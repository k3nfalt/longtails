import LongTails.Algorithms.CovarianceAcceleratedMixture
import LongTails.Proofs.CovarianceAcceleratedTilt

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace
open LongTails.Algorithms.CovarianceAcceleratedMixture

namespace LongTails.Proofs.CovarianceAcceleratedMixture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n))

lemma mixture_pos (u : E) : 0 < mixture z w u := by
  obtain ⟨i, hi⟩ := w.support_weights_nonempty
  have hip : 0 < w.weights i := lt_of_le_of_ne (w.weights_nonneg i)
    (Ne.symm (Finsupp.mem_support_iff.mp hi))
  exact Finset.sum_pos' (fun j _ => mul_nonneg (w.weights_nonneg j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, mul_pos hip (Real.exp_pos _)⟩

lemma mixture_bounds (u : E) {l h : ℝ}
    (hl : ∀ i, l ≤ density (z i) u) (hh : ∀ i, density (z i) u ≤ h) :
    l ≤ mixture z w u ∧ mixture z w u ≤ h := by
  constructor
  · have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hl i) (w.weights_nonneg i))
    simpa [mixture, ← Finset.sum_mul] using hs
  · have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hh i) (w.weights_nonneg i))
    simpa [mixture, ← Finset.sum_mul] using hs

lemma mixture_log_bound {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) (u : E) :
    |Real.log (mixture z w u)| ≤ M * ‖u‖ + M ^ 2 / 2 := by
  let B := M * ‖u‖ + M ^ 2 / 2
  have hpoint (i : Fin n) : -B ≤ ⟪z i, u⟫ - ‖z i‖ ^ 2 / 2 ∧
      ⟪z i, u⟫ - ‖z i‖ ^ 2 / 2 ≤ B := by
    have hi := abs_le.mp (abs_real_inner_le_norm (z i) u)
    have hp := mul_le_mul_of_nonneg_right (hz i) (norm_nonneg u)
    have hsq : ‖z i‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (z i), hz i]
    dsimp [B]
    constructor <;> nlinarith [sq_nonneg ‖z i‖, sq_nonneg M]
  have hb := mixture_bounds z w u
    (fun i => Real.exp_le_exp.mpr (hpoint i).1)
    (fun i => Real.exp_le_exp.mpr (hpoint i).2)
  have hl := Real.log_le_log (Real.exp_pos (-B)) hb.1
  have hh := Real.log_le_log (mixture_pos z w u) hb.2
  rw [Real.log_exp] at hl hh
  exact abs_le.mpr ⟨hl, hh⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma mixture_integrable : Integrable (mixture z w) (stdGaussian E) := by
  exact integrable_finsetSum _ (fun i _ =>
    (CovarianceAcceleratedTilt.gaussian_density_integrable (z i)).const_mul (w.weights i))

lemma mixture_integral : (∫ u, mixture z w u ∂stdGaussian E) = 1 := by
  unfold mixture density
  rw [integral_finsetSum _ (fun i _ =>
    (CovarianceAcceleratedTilt.gaussian_density_integrable (z i)).const_mul (w.weights i))]
  simp_rw [integral_const_mul, CovarianceAcceleratedTilt.gaussian_density_integral, mul_one]
  exact w.total_of_fintype

lemma mixture_mul_integrable :
    Integrable (fun u => mixture z w u • u) (stdGaussian E) := by
  have h := integrable_finsetSum Finset.univ (fun i _ =>
    (CovarianceAcceleratedTilt.gaussian_density_mul_integrable (z i)).smul (w.weights i))
  apply h.congr
  filter_upwards [] with u
  simp [mixture, density, Finset.sum_smul, mul_smul]

lemma mixture_mean : (∫ u, mixture z w u • u ∂stdGaussian E) = mean z w := by
  simp_rw [mixture, Finset.sum_smul, mul_smul]
  rw [integral_finsetSum _ (fun i _ =>
    show Integrable (fun u => w.weights i • density (z i) u • u) (stdGaussian E) from
      (CovarianceAcceleratedTilt.gaussian_density_mul_integrable (z i)).smul (w.weights i))]
  simp_rw [integral_smul, density, CovarianceAcceleratedTilt.gaussian_density_mean]
  rfl

lemma mixture_norm_integrable :
    Integrable (fun u => mixture z w u * ‖u‖) (stdGaussian E) := by
  have h := (mixture_mul_integrable z w).norm
  apply h.congr
  filter_upwards [] with u
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos (mixture_pos z w u)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixture_log_ratio_bound (v : StdSimplex ℝ (Fin n)) {M : ℝ}
    (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) (u : E) :
    |Real.log (mixture z w u / mixture z v u)| ≤ 2 * (M * ‖u‖ + M ^ 2 / 2) := by
  rw [Real.log_div (mixture_pos z w u).ne' (mixture_pos z v u).ne']
  have h := abs_sub (Real.log (mixture z w u)) (Real.log (mixture z v u))
  have hw := mixture_log_bound z w hM hz u
  have hv := mixture_log_bound z v hM hz u
  linarith

lemma mixture_divergence_integrable (v : StdSimplex ℝ (Fin n)) {M : ℝ}
    (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    Integrable (fun u => mixture z w u * Real.log (mixture z w u / mixture z v u))
      (stdGaussian E) := by
  have hd : Integrable (fun u => mixture z w u * (2 * (M * ‖u‖ + M ^ 2 / 2)))
      (stdGaussian E) := by
    have h := ((mixture_norm_integrable z w).mul_const (2 * M)).add
      ((mixture_integrable z w).mul_const (M ^ 2))
    apply h.congr
    filter_upwards [] with u
    dsimp only [Pi.add_apply]
    ring
  apply hd.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · have hm : Measurable (fun u => mixture z w u *
        Real.log (mixture z w u / mixture z v u)) := by
      unfold mixture density
      fun_prop
    exact hm.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mixture_pos z w u)]
    exact mul_le_mul_of_nonneg_left (mixture_log_ratio_bound z w v hM hz u)
      (mixture_pos z w u).le

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma density_product_ratio (x y v u : E) :
    density x u * density y u / density v u =
      Real.exp (‖x + y - v‖ ^ 2 / 2 - ‖x‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2 + ‖v‖ ^ 2 / 2) *
        density (x + y - v) u := by
  simp only [density, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  rw [inner_sub_left, inner_add_left]
  ring

lemma density_product_ratio_integrable (x y v : E) :
    Integrable (fun u => density x u * density y u / density v u) (stdGaussian E) := by
  simp_rw [density_product_ratio]
  exact (CovarianceAcceleratedTilt.gaussian_density_integrable (x + y - v)).const_mul _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma density_kl_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hy hx)) hx.le
  simp only [Real.log_div hy.ne' hx.ne', mul_sub, mul_div_cancel₀ _ hx.ne', mul_one] at h
  rw [Real.log_div hx.ne' hy.ne', mul_sub]
  linarith

lemma divergence_nonneg (v : StdSimplex ℝ (Fin n)) {M : ℝ}
    (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) : 0 ≤ divergence z w v := by
  have h := integral_mono ((mixture_integrable z w).sub (mixture_integrable z v))
    (mixture_divergence_integrable z w v hM hz)
    (fun u => density_kl_lower (mixture_pos z w u) (mixture_pos z v u))
  simp only [Pi.sub_apply] at h
  rw [integral_sub (mixture_integrable z w) (mixture_integrable z v),
    mixture_integral, mixture_integral, sub_self] at h
  exact h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixture_le_density_sum (u : E) : mixture z w u ≤ ∑ i, density (z i) u := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_of_le_one_left (Real.exp_pos _).le (w.weights_apply_le_one i)

lemma density_norm_integrable (x : E) :
    Integrable (fun u => density x u * ‖u‖) (stdGaussian E) := by
  have h := (CovarianceAcceleratedTilt.gaussian_density_mul_integrable x).norm
  apply h.congr
  filter_upwards [] with u
  simp [density, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma density_sum_envelope_integrable (M : ℝ) :
    Integrable (fun u => (∑ i, density (z i) u) * (2 * (M * ‖u‖ + M ^ 2 / 2)))
      (stdGaussian E) := by
  have h := integrable_finsetSum Finset.univ (fun i _ =>
    ((density_norm_integrable (z i)).mul_const (2 * M)).add
      ((CovarianceAcceleratedTilt.gaussian_density_integrable (z i)).mul_const (M ^ 2)))
  apply h.congr
  filter_upwards [] with u
  simp only [Pi.add_apply, Finset.sum_mul, density]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma divergence_continuous {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    Continuous (fun p : StdSimplex ℝ (Fin n) × StdSimplex ℝ (Fin n) =>
      divergence z p.1 p.2) := by
  have : FirstCountableTopology (StdSimplex ℝ (Fin n)) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin n)).firstCountableTopology
  unfold divergence
  apply continuous_of_dominated (bound := fun u =>
    (∑ i, density (z i) u) * (2 * (M * ‖u‖ + M ^ 2 / 2)))
  · intro p
    exact (mixture_divergence_integrable z p.1 p.2 hM hz).aestronglyMeasurable
  · intro p
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mixture_pos z p.1 u)]
    exact (mul_le_mul_of_nonneg_left (mixture_log_ratio_bound z p.1 p.2 hM hz u)
      (mixture_pos z p.1 u).le).trans
      (mul_le_mul_of_nonneg_right (mixture_le_density_sum z p.1 u) (by positivity))
  · exact density_sum_envelope_integrable z M
  · filter_upwards [] with u
    have hf : Continuous (fun p : StdSimplex ℝ (Fin n) × StdSimplex ℝ (Fin n) =>
        mixture z p.1 u) := by unfold mixture; fun_prop
    have hg : Continuous (fun p : StdSimplex ℝ (Fin n) × StdSimplex ℝ (Fin n) =>
        mixture z p.2 u) := by unfold mixture; fun_prop
    exact hf.mul ((hf.div hg (fun p => (mixture_pos z p.2 u).ne')).log
      (fun p => (div_pos (mixture_pos z p.1 u) (mixture_pos z p.2 u)).ne'))

end LongTails.Proofs.CovarianceAcceleratedMixture
