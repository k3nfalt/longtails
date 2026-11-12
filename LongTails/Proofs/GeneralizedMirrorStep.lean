import LongTails.Algorithms.StochasticGeneralizedMirror
import LongTails.Proofs.GeneralizedMirrorCurvature

open Set LongTails.Algorithms.StochasticGeneralizedMirror

namespace LongTails.Proofs.GeneralizedMirrorStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma mix_mem {Q : Set E} (hQ : Convex ℝ Q) {A a : ℝ} (hA : 0 ≤ A)
    (ha : 0 < a) {x z : E} (hx : x ∈ Q) (hz : z ∈ Q) : mix A a x z ∈ Q := by
  have hB : 0 < A + a := by positivity
  exact hQ hx hz (div_nonneg hA hB.le) (div_nonneg ha.le hB.le)
    (by rw [← add_div, div_self hB.ne'])

lemma mix_displacement {A a : ℝ} (x z p : E) :
    mix A a x p - mix A a x z = (a / (A + a)) • (p - z) := by
  unfold mix
  module

lemma mix_self {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (x : E) :
    mix A a x x = x := by
  have hB : A + a ≠ 0 := ne_of_gt (by positivity)
  simp only [mix, ← add_smul, ← add_div, div_self hB, one_smul]

lemma mix_query_distance {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (x z : E) :
    ‖x - mix A a x z‖ = a / (A + a) * ‖z - x‖ := by
  have h := mix_displacement (A := A) (a := a) x x z
  rw [mix_self hA ha] at h
  rw [norm_sub_rev, h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma mix_radius {A a R : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (x z u : E)
    (hx : ‖x - u‖ ≤ R) (hz : ‖z - u‖ ≤ R) : ‖mix A a x z - u‖ ≤ R := by
  have h := mix_mem (convex_closedBall u R) hA ha
    (show x ∈ Metric.closedBall u R by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)
    (show z ∈ Metric.closedBall u R by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
  simpa only [Metric.mem_closedBall, dist_eq_norm] using h

lemma accelerated_model {f ψ : E → ℝ} {Q : Set E} {A a L : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hf : ConvexOn ℝ Q f) (hψ : ConvexOn ℝ Q ψ)
    (x z p u : E) (hx : x ∈ Q) (hz : z ∈ Q) (hp : p ∈ Q) (hu : u ∈ Q)
    (g : E →L[ℝ] ℝ) (hg : HasFDerivAt f g (mix A a x z))
    (hmodel : f (mix A a x p) ≤ f (mix A a x z) +
      g (mix A a x p - mix A a x z) + L * ‖mix A a x p - mix A a x z‖ ^ 2)
    (hstep : L * a ^ 2 ≤ (A + a) / 4) :
    (A + a) * (f (mix A a x p) + ψ (mix A a x p)) - A * (f x + ψ x) -
      a * (f u + ψ u) ≤ a * (g (p - u) + ψ p - ψ u) + ‖p - z‖ ^ 2 / 4 := by
  have hB : 0 < A + a := by positivity
  have hy := mix_mem hf.1 hA ha hx hz
  have hsx := PowerMirrorGeometry.convex_support hf hy hx hg
  have hsu := PowerMirrorGeometry.convex_support hf hy hu hg
  have hpx := mul_le_mul_of_nonneg_left hsx hA
  have hpu := mul_le_mul_of_nonneg_left hsu ha.le
  have hweights : A / (A + a) + a / (A + a) = 1 := by
    rw [← add_div, div_self hB.ne']
  have hψmix := hψ.2 hx hp (div_nonneg hA hB.le) (div_nonneg ha.le hB.le) hweights
  simp only [smul_eq_mul] at hψmix
  have hψmul := mul_le_mul_of_nonneg_left hψmix hB.le
  have hm := mul_le_mul_of_nonneg_left hmodel hB.le
  rw [mix_displacement, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ha.le hB.le)] at hm
  have hcoef : (A + a) * (L * (a / (A + a) * ‖p - z‖) ^ 2) ≤ ‖p - z‖ ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_right hstep (sq_nonneg ‖p - z‖)
    field_simp
    nlinarith
  simp only [mix, map_sub, map_add, map_smul, smul_eq_mul] at hpx hpu hψmul hm ⊢
  field_simp at hpx hpu hψmul hm
  nlinarith

lemma localized_direction_bound {F : E → E →L[ℝ] ℝ} {L0 L1 A a R : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hA : 0 ≤ A) (ha : 0 < a)
    (hR : 0 ≤ R) (hc : Continuous F)
    (hgl : ∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    (x y u : E) (v : E →L[ℝ] ℝ)
    (hd : ‖x - y‖ ≤ 4 * R * a / (A + a))
    (hlocal : L1 * ‖x - y‖ ≤ 1 / 2)
    (hcurv : 256 * (L0 + L1 * ‖F x‖) * a ^ 2 ≤ A + a)
    (hgrad : a * ‖F x - F u‖ ≤ R / 8)
    (herr : a * ‖v - F y‖ ≤ R / 32) :
    a * ‖v - F u‖ ≤ 3 * R / 16 := by
  have hB : 0 < A + a := by positivity
  have hC : 0 ≤ L0 + L1 * ‖F x‖ := by positivity
  have hl := GeneralizedMirrorSmoothness.local_difference hL0 hL1 hc hgl x y hlocal
  have hm := mul_le_mul_of_nonneg_left hl ha.le
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * a * (L0 + L1 * ‖F x‖) by positivity)
  have hnum := mul_le_mul_of_nonneg_left hcurv hR
  have hsmall : 2 * a * (L0 + L1 * ‖F x‖) * (4 * R * a / (A + a)) ≤ R / 32 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
    field_simp
    nlinarith
  have hi : ‖F y - F u‖ ≤ ‖F y - F x‖ + ‖F x - F u‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (F y - F x) (F x - F u)
  rw [norm_sub_rev (F y) (F x)] at hi
  have hi' := mul_le_mul_of_nonneg_left hi ha.le
  have hv0 : ‖v - F u‖ ≤ ‖v - F y‖ + ‖F y - F u‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (v - F y) (F y - F u)
  have hv := mul_le_mul_of_nonneg_left hv0 ha.le
  nlinarith

open LongTails.Setups.StochasticGeneralizedMirror

lemma energy_step {q : Public} (I : Instance q) {A a : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hL0 : 0 ≤ q.L0) (hL1 : 0 ≤ q.L1)
    (hf : ConvexOn ℝ I.Q I.f) (hψ : ConvexOn ℝ I.Q I.ψ)
    (hd : ∀ w, HasFDerivAt I.f (I.df w) w) (hc : Continuous I.df)
    (hgl : ∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.df (x + θ • (y - x))‖ ≤ M) →
      ‖I.df x - I.df y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖)
    (x z p u : q.E) (hx : x ∈ I.Q) (hz : z ∈ I.Q) (hp : p ∈ I.Q) (hu : u ∈ I.Q)
    (v : Dual q) (hh : HasFDerivAt I.h (I.dh p) p)
    (hprox : IsMinOn (proxObjective I a z v) I.Q p)
    (hstrong : ‖p - z‖ ^ 2 / 2 ≤ divergence I p z)
    (hlocal : q.L1 * ‖mix A a x z - mix A a x p‖ ≤ 1 / 2)
    (hstep : 8 * (q.L0 + q.L1 * ‖I.df (mix A a x z)‖) * a ^ 2 ≤ A + a) :
    (A + a) * (objective I (mix A a x p) - objective I u) + divergence I u p ≤
      A * (objective I x - objective I u) + divergence I u z +
        a * (v - I.df (mix A a x z)) (u - z) +
        a ^ 2 * ‖v - I.df (mix A a x z)‖ ^ 2 := by
  have hdesc := GeneralizedMirrorSmoothness.local_descent hL0 hL1 hc hd hgl
    (mix A a x z) (mix A a x p) hlocal
  have hmodel := accelerated_model hA ha hf hψ x z p u hx hz hp hu
    (I.df (mix A a x z)) (hd _) hdesc (by nlinarith)
  have hthree := GeneralizedMirrorGeometry.prox_three_point I ha hψ hp hu hh hprox
  apply GeneralizedMirrorPotential.potential_step (objective I) I.ψ (divergence I)
    v (v - I.df (mix A a x z)) u x (mix A a x p) z p ha.le
  · simpa only [objective, sub_apply, sub_sub_cancel] using hmodel
  · linarith

end LongTails.Proofs.GeneralizedMirrorStep
