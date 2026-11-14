import LongTails.Proofs.PointwiseHessianLocalization
import LongTails.Proofs.GradientDependentLocal
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.PointwiseHessianGeometry

open OracleTemplate OracleTemplate.NonlinearTemporalDiscrepancy
open LongTails.Proofs.GradientDependentLocal
open LongTails.Proofs.PointwiseHessianLocalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma gradient_monotone {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (x y : E) :
    0 ≤ ⟪gradient f x - gradient f y, x - y⟫ := by
  have hg (z : E) : HasGradientAt f (gradient f z) z :=
    (hf.differentiable (by norm_num) z).hasGradientAt
  have h1 := Gradient.convex_support hc hg x y
  have h2 := Gradient.convex_support hc hg y x
  have he : y - x = -(x - y) := by abel
  rw [he, inner_neg_right] at h1
  rw [inner_sub_left]
  linarith

lemma hessian_psd {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (x v : E) :
    0 ≤ ⟪fderiv ℝ (gradient f) x v, v⟫ := by
  have hg := gradient_contDiff_two hf
  have hgrad (y : E) : HasGradientAt f (gradient f y) y :=
    (hf.differentiable (by norm_num) y).hasGradientAt
  have hs (x y : E) : f x + ⟪gradient f x, y - x⟫ +
      (0 : ℝ) / 2 * ‖y - x‖ ^ 2 ≤ f y := by
    have hh := Gradient.convex_support hc hgrad x y
    simp only [zero_div, zero_mul, add_zero]
    linarith
  simpa using hessian_lower_bound (hg.differentiable (by norm_num)) hs x v

omit [FiniteDimensional ℝ E] in
lemma minimizer_gradient {f : E → ℝ} {s : E} (hs : IsMinOn f Set.univ s) :
    gradient f s = 0 := by
  have hh := (hs.isLocalMin (Filter.univ_mem)).fderiv_eq_zero
  simp [gradient, hh]

lemma segment_gradient_sq {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {s : E} (hs : IsMinOn f Set.univ s)
    (d : E) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (gradient f) (s + t • d)‖ ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖gradient f (s + t • d)‖ ^ 2 ≤ K * ⟪gradient f (s + t • d), d⟫ := by
  have hg := gradient_contDiff_two hf
  have hH : ContDiff ℝ 1 (fderiv ℝ (gradient f)) :=
    (contDiff_succ_iff_fderiv.mp hg).2.2
  have hline (u : ℝ) : HasDerivAt (fun v : ℝ => s + v • d) d u := by
    simpa using ((hasDerivAt_id u).smul_const d).const_add s
  apply ray_gradient_sq (fun u => fderiv ℝ (gradient f) (s + u • d))
    (fun u => gradient f (s + u • d)) d
    (hH.continuous.comp (by fun_prop))
    (fun u => (hg.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt u (hline u))
    (by simpa using minimizer_gradient hs) hK ?_ ?_ hb ht
  · intro u v w
    exact hessian_symmetric (hf.of_le (by norm_num)) (s + u • d) v w
  · intro u v
    exact hessian_psd hf hc (s + u • d) v

omit [FiniteDimensional ℝ E] in
lemma segment_direction_nonneg {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {s : E} (hs : IsMinOn f Set.univ s)
    (d : E) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ⟪gradient f (s + t • d), d⟫ := by
  rcases eq_or_lt_of_le ht with hz | hz
  · subst t
    simp [minimizer_gradient hs]
  · have hgrad (y : E) : HasGradientAt f (gradient f y) y :=
      (hf.differentiable (by norm_num) y).hasGradientAt
    have hh := Gradient.convex_support hc hgrad (s + t • d) s
    have hm : f s ≤ f (s + t • d) := hs (Set.mem_univ (s + t • d))
    have he : s - (s + t • d) = (-t) • d := by module
    rw [he, inner_smul_right] at hh
    nlinarith

lemma segment_hessian_transport {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ M₀ + M₁ * ‖gradient f x‖)
    (s d : E) {a t : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (gradient f) (s + t • d) - fderiv ℝ (gradient f) (s + a • d)‖ ≤
      M₀ * ‖d‖ + (M₁ * ‖d‖) * ∫ u in (0 : ℝ)..1, ‖gradient f (s + u • d)‖ := by
  obtain ⟨_, _, hH⟩ := derivative_chain hf
  have hg := gradient_contDiff_two hf
  have hline (u : ℝ) : HasDerivAt (fun v : ℝ => s + v • d) d u := by
    simpa using ((hasDerivAt_id u).smul_const d).const_add s
  have hd (u : ℝ) := (hH (s + u • d)).comp_hasDerivAt u (hline u)
  have hgc : Continuous (fun u : ℝ => ‖gradient f (s + u • d)‖) := by
    exact (hg.continuous.comp (by fun_prop)).norm
  have hh := unit_interval_transport _ _ hd
    (fun u => M₀ * ‖d‖ + (M₁ * ‖d‖) * ‖gradient f (s + u • d)‖)
    (by fun_prop) (fun u _ => by positivity) (fun u _ => by
      have h1 := (fderiv ℝ (fderiv ℝ (gradient f)) (s + u • d)).le_opNorm d
      have h2 := mul_le_mul_of_nonneg_right (hT (s + u • d)) (norm_nonneg d)
      nlinarith) ha ht
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((hgc.intervalIntegrable 0 1).const_mul (M₁ * ‖d‖)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hh
  simpa using hh

lemma segment_hessian_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {s : E} (hs : IsMinOn f Set.univ s)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ M₀ + M₁ * ‖gradient f x‖)
    (d : E) {a t : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (gradient f) (s + t • d)‖ ≤
      2 * ‖fderiv ℝ (gradient f) (s + a • d)‖ + 2 * M₀ * ‖d‖ +
        M₁ ^ 2 * ‖d‖ ^ 2 * (f (s + d) - f s) := by
  have hg := gradient_contDiff_two hf
  have hH : ContDiff ℝ 1 (fderiv ℝ (gradient f)) :=
    (contDiff_succ_iff_fderiv.mp hg).2.2
  have hHc : Continuous (fun u : ℝ => ‖fderiv ℝ (gradient f) (s + u • d)‖) :=
    (hH.continuous.comp (by fun_prop)).norm
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hHc.continuousOn
  let K := ‖fderiv ℝ (gradient f) (s + u • d)‖
  have hK : 0 ≤ K := norm_nonneg _
  have hb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (gradient f) (s + v • d)‖ ≤ K :=
    fun v hv => hmax hv
  have hgc : Continuous (fun v : ℝ => ‖gradient f (s + v • d)‖) :=
    (hg.continuous.comp (by fun_prop)).norm
  have hvc : Continuous (fun v : ℝ => ⟪gradient f (s + v • d), d⟫) := by
    exact (hg.continuous.comp (by fun_prop)).inner continuous_const
  have htransport : K ≤ ‖fderiv ℝ (gradient f) (s + a • d)‖ + M₀ * ‖d‖ +
      (M₁ * ‖d‖) * ∫ v in (0 : ℝ)..1, ‖gradient f (s + v • d)‖ := by
    have hh := segment_hessian_transport hf hM₀ hM₁ hT s d ha hu
    have hn := norm_add_le
      (fderiv ℝ (gradient f) (s + u • d) - fderiv ℝ (gradient f) (s + a • d))
      (fderiv ℝ (gradient f) (s + a • d))
    rw [sub_add_cancel] at hn
    dsimp [K]
    linarith
  have hh := unit_integral_localization _ _ hgc hvc hK
    (mul_nonneg hM₁ (norm_nonneg d)) (fun _ _ => norm_nonneg _)
    (fun v hv => segment_direction_nonneg hf hc hs d hv.1)
    (fun v hv => segment_gradient_sq hf hc hs d hK hb hv) htransport
  have he : (∫ v in (0 : ℝ)..1, ⟪gradient f (s + v • d), d⟫) = f (s + d) - f s := by
    have hd (v : ℝ) : HasDerivAt (fun w : ℝ => f (s + w • d))
        ⟪gradient f (s + v • d), d⟫ v := by
      have hl : HasDerivAt (fun w : ℝ => s + w • d) d v := by
        simpa using ((hasDerivAt_id v).smul_const d).const_add s
      exact ((derivative_chain hf).1 _).comp_hasDerivAt v hl
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => hd v) (hvc.intervalIntegrable 0 1)
  rw [he] at hh
  have hbt := hb t ht
  nlinarith

lemma minimizer_hessian_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {s : E} (hs : IsMinOn f Set.univ s)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ M₀ + M₁ * ‖gradient f x‖)
    (x : E) :
    ‖fderiv ℝ (gradient f) s‖ ≤ 2 * ‖fderiv ℝ (gradient f) x‖ +
      2 * M₀ * ‖x - s‖ + M₁ ^ 2 * ‖x - s‖ ^ 2 * (f x - f s) := by
  simpa using segment_hessian_bound hf hc hs hM₀ hM₁ hT (x - s)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)

end LongTails.Proofs.PointwiseHessianGeometry
