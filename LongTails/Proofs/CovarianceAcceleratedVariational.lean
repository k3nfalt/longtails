import LongTails.Proofs.CovarianceAcceleratedMixture

open MeasureTheory ProbabilityTheory Convexity
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedMixture

namespace LongTails.Proofs.CovarianceAcceleratedVariational

lemma kl_quadratic_upper {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * Real.log (x / y) - x + y ≤ (x - y) ^ 2 / y := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hx hy)) hx.le
  have he : x * (x / y - 1) - x + y = (x - y) ^ 2 / y := by
    field_simp
    ring
  linarith

lemma kl_three_point {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * Real.log (x / z) - x * Real.log (x / y) - y * Real.log (y / z) =
      (x - y) * Real.log (y / z) := by
  rw [Real.log_div hx.ne' hz.ne', Real.log_div hx.ne' hy.ne',
    Real.log_div hy.ne' hz.ne']
  ring

lemma kl_segment_identity {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) * y + t * x) * Real.log (((1 - t) * y + t * x) / z) -
        y * Real.log (y / z) =
      t * (x - y) * Real.log (y / z) +
        ((1 - t) * y + t * x) * Real.log (((1 - t) * y + t * x) / y) := by
  have hpos : 0 < (1 - t) * y + t * x := by
    by_cases ht0 : t = 0
    · simp [ht0, hy]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hy.le)
        (mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) hx)
  have h := kl_three_point hpos hy hz
  nlinarith

lemma linear_quadratic_nonneg {G C : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * G + C * t ^ 2) : 0 ≤ G := by
  by_contra hn
  have hG : G < 0 := lt_of_not_ge hn
  have hD : 0 < 2 * (|C| + 1) := by positivity
  by_cases hb : 2 * (|C| + 1) ≤ -G
  · have h1 := h 1 (by norm_num) le_rfl
    norm_num at h1
    linarith [le_abs_self C]
  · let t := -G / (2 * (|C| + 1))
    have ht : 0 < t := div_pos (neg_pos.mpr hG) hD
    have ht1 : t ≤ 1 := (div_le_one hD).mpr (le_of_lt (lt_of_not_ge hb))
    have he : t * (2 * (|C| + 1)) = -G := div_mul_cancel₀ _ hD.ne'
    have hc : C * t ≤ (|C| + 1) * t :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) ht.le
    have hnlin : G + C * t < 0 := by nlinarith
    have hm := mul_neg_of_pos_of_neg ht hnlin
    have hh := h t ht ht1
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} (z : Fin n → E) (w v : StdSimplex ℝ (Fin n))

lemma mixture_square_over_density_integrable (x : E) :
    Integrable (fun u => mixture z w u ^ 2 / density x u) (stdGaussian E) := by
  unfold mixture
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have h := (density_product_ratio_integrable (z i) (z j) x).const_mul
    (w.weights i * w.weights j)
  apply h.congr
  filter_upwards [] with u
  ring

lemma mixture_chi_integrable :
    Integrable (fun u => (mixture z w u - mixture z v u) ^ 2 / mixture z v u)
      (stdGaussian E) := by
  obtain ⟨i, hi⟩ := v.support_weights_nonempty
  have hv : 0 < v.weights i := lt_of_le_of_ne (v.weights_nonneg i)
    (Ne.symm (Finsupp.mem_support_iff.mp hi))
  have hd := ((mixture_square_over_density_integrable z w (z i)).const_mul
    (2 / v.weights i)).add ((mixture_integrable z v).const_mul 2)
  apply hd.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · have hm : Measurable (fun u => (mixture z w u - mixture z v u) ^ 2 / mixture z v u) := by
      unfold mixture density
      fun_prop
    exact hm.aestronglyMeasurable
  · have hq := mixture_pos z v u
    have hp : 0 < density (z i) u := Real.exp_pos _
    have hlo : v.weights i * density (z i) u ≤ mixture z v u := by
      unfold mixture density
      exact Finset.single_le_sum (fun j _ =>
        mul_nonneg (v.weights_nonneg j) (Real.exp_pos (inner ℝ (z j) u - ‖z j‖ ^ 2 / 2)).le) (Finset.mem_univ i)
    have hb : (mixture z w u - mixture z v u) ^ 2 ≤
        2 * mixture z w u ^ 2 + 2 * mixture z v u ^ 2 := by
      nlinarith [sq_nonneg (mixture z w u + mixture z v u)]
    have hr := div_le_div_of_nonneg_left (sq_nonneg (mixture z w u)) (mul_pos hv hp) hlo
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hq.le)]
    dsimp only [Pi.add_apply]
    have he : (2 * mixture z w u ^ 2 + 2 * mixture z v u ^ 2) / mixture z v u =
        2 * (mixture z w u ^ 2 / mixture z v u) + 2 * mixture z v u := by
      field_simp
    have he' : 2 * (mixture z w u ^ 2 / (v.weights i * density (z i) u)) =
        (2 / v.weights i) * (mixture z w u ^ 2 / density (z i) u) := by ring
    have hb' := div_le_div_of_nonneg_right hb hq.le
    rw [he] at hb'
    nlinarith

lemma mixture_cross_log_integrable (p : StdSimplex ℝ (Fin n)) {M : ℝ}
    (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    Integrable (fun u => mixture z w u * Real.log (mixture z v u / mixture z p u))
      (stdGaussian E) := by
  have h := (mixture_divergence_integrable z w p hM hz).sub
    (mixture_divergence_integrable z w v hM hz)
  apply h.congr
  filter_upwards [] with u
  simp only [Pi.sub_apply, Real.log_div (mixture_pos z w u).ne' (mixture_pos z p u).ne',
    Real.log_div (mixture_pos z w u).ne' (mixture_pos z v u).ne',
    Real.log_div (mixture_pos z v u).ne' (mixture_pos z p u).ne']
  ring

lemma mixture_direction_log_integrable (p : StdSimplex ℝ (Fin n)) {M : ℝ}
    (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    Integrable (fun u => (mixture z w u - mixture z v u) *
      Real.log (mixture z v u / mixture z p u)) (stdGaussian E) := by
  have h := (mixture_cross_log_integrable z w v p hM hz).sub
    (mixture_cross_log_integrable z v v p hM hz)
  apply h.congr
  filter_upwards [] with u
  dsimp only [Pi.sub_apply]
  ring

lemma mixture_three_point (p : StdSimplex ℝ (Fin n)) {M : ℝ}
    (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    divergence z w p - divergence z w v - divergence z v p =
      ∫ u, (mixture z w u - mixture z v u) *
        Real.log (mixture z v u / mixture z p u) ∂stdGaussian E := by
  have hwp := mixture_divergence_integrable z w p hM hz
  have hwv := mixture_divergence_integrable z w v hM hz
  have hvp := mixture_divergence_integrable z v p hM hz
  unfold divergence
  rw [← integral_sub hwp hwv]
  rw [← integral_sub (show Integrable (fun u =>
    mixture z w u * Real.log (mixture z w u / mixture z p u) -
      mixture z w u * Real.log (mixture z w u / mixture z v u)) (stdGaussian E) from
    hwp.sub hwv) hvp]
  apply integral_congr_ae
  filter_upwards [] with u
  exact kl_three_point (mixture_pos z w u) (mixture_pos z v u) (mixture_pos z p u)

noncomputable def blend (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : StdSimplex ℝ (Fin n) :=
  convexCombPair (1 - t) t (sub_nonneg.mpr ht1) ht (by ring) v w

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixture_blend (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (u : E) :
    mixture z (blend w v t ht ht1) u = (1 - t) * mixture z v u + t * mixture z w u := by
  simp only [blend, mixture, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum]

lemma divergence_blend_upper (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) {M : ℝ}
    (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    divergence z (blend w v t ht ht1) v ≤
      t ^ 2 * ∫ u, (mixture z w u - mixture z v u) ^ 2 / mixture z v u ∂stdGaussian E := by
  let r := blend w v t ht ht1
  have hir := mixture_integrable z r
  have hiv := mixture_integrable z v
  have hiχ := mixture_chi_integrable z w v
  have him : Integrable (fun u => (mixture z r u - mixture z v u) +
      t ^ 2 * ((mixture z w u - mixture z v u) ^ 2 / mixture z v u)) (stdGaussian E) :=
    (hir.sub hiv).add (hiχ.const_mul (t ^ 2))
  have hb := integral_mono (mixture_divergence_integrable z r v hM hz) him
    (fun u => show mixture z r u * Real.log (mixture z r u / mixture z v u) ≤
      (mixture z r u - mixture z v u) +
        t ^ 2 * ((mixture z w u - mixture z v u) ^ 2 / mixture z v u) from by
      have h := kl_quadratic_upper (mixture_pos z r u) (mixture_pos z v u)
      have hd : mixture z r u - mixture z v u = t * (mixture z w u - mixture z v u) := by
        dsimp [r]
        rw [mixture_blend]
        ring
      have he : (mixture z r u - mixture z v u) ^ 2 / mixture z v u =
          t ^ 2 * ((mixture z w u - mixture z v u) ^ 2 / mixture z v u) := by
        rw [hd, mul_pow]
        ring
      rw [he] at h
      linarith)
  rw [integral_add (show Integrable (fun u => mixture z r u - mixture z v u)
    (stdGaussian E) from hir.sub hiv) (hiχ.const_mul (t ^ 2)),
    integral_sub hir hiv, mixture_integral, mixture_integral, sub_self, zero_add,
    integral_const_mul] at hb
  exact hb

lemma divergence_blend_identity (p : StdSimplex ℝ (Fin n)) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    divergence z (blend w v t ht ht1) p - divergence z v p =
      t * (divergence z w p - divergence z w v - divergence z v p) +
        divergence z (blend w v t ht ht1) v := by
  have h := mixture_three_point z (blend w v t ht ht1) v p hM hz
  have he : (∫ u, (mixture z (blend w v t ht ht1) u - mixture z v u) *
      Real.log (mixture z v u / mixture z p u) ∂stdGaussian E) =
      t * (∫ u, (mixture z w u - mixture z v u) *
        Real.log (mixture z v u / mixture z p u) ∂stdGaussian E) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [mixture_blend]
    ring
  rw [he, ← mixture_three_point z w v p hM hz] at h
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mean_blend (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    mean z (blend w v t ht ht1) = (1 - t) • mean z v + t • mean z w := by
  simp only [blend, mean, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib, mul_smul,
    ← Finset.smul_sum]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_segment_identity (x y p : E) (t : ℝ) :
    ‖(1 - t) • y + t • x - p‖ ^ 2 - ‖y - p‖ ^ 2 =
      t * (‖x - p‖ ^ 2 - ‖x - y‖ ^ 2 - ‖y - p‖ ^ 2) + t ^ 2 * ‖x - y‖ ^ 2 := by
  have he : (1 - t) • y + t • x - p = (y - p) + t • (x - y) := by module
  have hx : x - p = (y - p) + (x - y) := by abel
  rw [he, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right]
  have hnorm := norm_add_sq_real (y - p) (x - y)
  rw [← hx] at hnorm
  rw [hnorm]
  ring

lemma weights_blend_square (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ i, ((blend w v t ht ht1).weights i - v.weights i) ^ 2) =
      t ^ 2 * ∑ i, (w.weights i - v.weights i) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [blend, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]
  ring

lemma weights_blend_identity (p : StdSimplex ℝ (Fin n))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ i, ((blend w v t ht ht1).weights i - p.weights i) ^ 2) -
      (∑ i, (v.weights i - p.weights i) ^ 2) =
    t * ((∑ i, (w.weights i - p.weights i) ^ 2) -
      (∑ i, (w.weights i - v.weights i) ^ 2) - (∑ i, (v.weights i - p.weights i) ^ 2)) +
      t ^ 2 * ∑ i, (w.weights i - v.weights i) ^ 2 := by
  simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [blend, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mean_blend_square (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖mean z (blend w v t ht ht1) - mean z v‖ ^ 2 =
      t ^ 2 * ‖mean z w - mean z v‖ ^ 2 := by
  rw [mean_blend]
  have he : (1 - t) • mean z v + t • mean z w - mean z v =
      t • (mean z w - mean z v) := by module
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma potential_blend_identity (p : StdSimplex ℝ (Fin n)) (a β γ t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    potential z a β γ (blend w v t ht ht1) p - potential z a β γ v p =
      t * (potential z a β γ w p - potential z a β γ w v - potential z a β γ v p) +
        potential z a β γ (blend w v t ht ht1) v := by
  have hd := divergence_blend_identity z w v p t ht ht1 hM hz
  have hm := norm_segment_identity (mean z w) (mean z v) (mean z p) t
  have hw := weights_blend_identity w v p t ht ht1
  unfold potential
  rw [mean_blend_square, weights_blend_square, mean_blend]
  linear_combination hd + (β * a ^ 2 / 2) * hm + (γ / 2) * hw

lemma potential_blend_upper (a β γ t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    potential z a β γ (blend w v t ht ht1) v ≤
      t ^ 2 * ((∫ u, (mixture z w u - mixture z v u) ^ 2 / mixture z v u ∂stdGaussian E) +
        β * a ^ 2 / 2 * ‖mean z w - mean z v‖ ^ 2 +
        γ / 2 * ∑ i, (w.weights i - v.weights i) ^ 2) := by
  have h := divergence_blend_upper z w v t ht ht1 hM hz
  unfold potential
  rw [mean_blend_square, weights_blend_square]
  nlinarith

lemma linearLoss_blend (c : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    linearLoss c (blend w v t ht ht1) - linearLoss c v =
      t * (linearLoss c w - linearLoss c v) := by
  simp only [linearLoss, blend, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum]
  ring

lemma minimizer_three_point (p : StdSimplex ℝ (Fin n)) (c : Fin n → ℝ) (a β γ : ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M)
    (hmin : ∀ u, linearLoss c v + potential z a β γ v p ≤
      linearLoss c u + potential z a β γ u p) :
    linearLoss c v - linearLoss c w ≤
      potential z a β γ w p - potential z a β γ w v - potential z a β γ v p := by
  have hg : 0 ≤ linearLoss c w - linearLoss c v +
      (potential z a β γ w p - potential z a β γ w v - potential z a β γ v p) := by
    apply linear_quadratic_nonneg (C :=
      (∫ u, (mixture z w u - mixture z v u) ^ 2 / mixture z v u ∂stdGaussian E) +
        β * a ^ 2 / 2 * ‖mean z w - mean z v‖ ^ 2 +
        γ / 2 * ∑ i, (w.weights i - v.weights i) ^ 2)
    intro t ht ht1
    have hm := hmin (blend w v t ht.le ht1)
    have hl := linearLoss_blend w v c t ht.le ht1
    have hp := potential_blend_identity z w v p a β γ t ht.le ht1 hM hz
    have hb := potential_blend_upper z w v a β γ t ht.le ht1 hM hz
    nlinarith
  linarith

lemma potential_weight_lower (a β γ : ℝ) (hβ : 0 ≤ β)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    γ / 2 * ∑ i, (w.weights i - v.weights i) ^ 2 ≤ potential z a β γ w v := by
  have hd := divergence_nonneg z w v hM hz
  have hm : 0 ≤ β * a ^ 2 / 2 * ‖mean z w - mean z v‖ ^ 2 := by positivity
  unfold potential
  linarith

lemma minimizer_unique (p : StdSimplex ℝ (Fin n)) (c : Fin n → ℝ) (a β γ : ℝ)
    (hβ : 0 ≤ β) (hγ : 0 < γ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M)
    (hw : ∀ u, linearLoss c w + potential z a β γ w p ≤
      linearLoss c u + potential z a β γ u p)
    (hv : ∀ u, linearLoss c v + potential z a β γ v p ≤
      linearLoss c u + potential z a β γ u p) : w = v := by
  have h1 := minimizer_three_point z w v p c a β γ hM hz hv
  have h2 := minimizer_three_point z v w p c a β γ hM hz hw
  have hl1 := potential_weight_lower z w v a β γ hβ hM hz
  have hl2 := potential_weight_lower z v w a β γ hβ hM hz
  have hnn : 0 ≤ ∑ i, (v.weights i - w.weights i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsum : (∑ i, (w.weights i - v.weights i) ^ 2) ≤ 0 := by
    nlinarith
  apply StdSimplex.ext
  ext i
  have hi := Finset.single_le_sum (fun j _ => sq_nonneg (w.weights j - v.weights j))
    (Finset.mem_univ i)
  nlinarith

end LongTails.Proofs.CovarianceAcceleratedVariational
