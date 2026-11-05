import LongTails.Algorithms.TensorFreeModel
import LongTails.Proofs.FiniteSumThirdSmoothGeometry
import LongTails.Proofs.QuarticProximalGeometry
import LongTails.Proofs.GuardedMetricSupport

namespace LongTails.Proofs.TensorFreeModel

open LongTails.Algorithms.TensorFreeModel
open LongTails.Algorithms.TaylorCorrectedNewton
open LongTails.Setups.FiniteSumSmoothAndConvex
open OracleTemplate OracleTemplate.QueryPlan
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma power_bound_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : ℝ → V} {M : ℝ} (k : ℕ)
    (hd : ∀ t, HasDerivAt f (g t) t)
    (hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖g t‖ ≤ M * t ^ k) :
    ‖f 1 - f 0‖ ≤ M / (k + 1 : ℕ) := by
  let B := fun t : ℝ => M / (k + 1 : ℕ) * t ^ (k + 1)
  have hB (t : ℝ) : HasDerivAt B (M * t ^ k) t := by
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    convert (((hasDerivAt_id t).pow (k + 1)).const_mul (M / (k + 1 : ℕ))) using 1
    · funext y
      simp [B]
    · simp only [Nat.add_sub_cancel, id_eq, mul_one]
      field_simp
  have hf : ContinuousOn (fun t => f t - f 0) (Set.Icc (0 : ℝ) 1) :=
    (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn.sub continuousOn_const
  have hh := image_norm_le_of_norm_deriv_right_le_deriv_boundary hf
    (fun t _ => ((hd t).sub_const (f 0)).hasDerivWithinAt)
    (show ‖f 0 - f 0‖ ≤ B 0 by simp [B]) hB hb (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  simpa [B] using hh

lemma hessian_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L : ℝ}
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w s : E) :
    ‖fderiv ℝ (gradient f) (w + s) - fderiv ℝ (gradient f) w -
      fderiv ℝ (fderiv ℝ (gradient f)) w s‖ ≤ L * ‖s‖ ^ 2 / 2 := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let r := fun t : ℝ => H (w + t • s) - H w - t • T w s
  let d := fun t : ℝ => (T (w + t • s) - T w) s
  have hd (t : ℝ) : HasDerivAt r (d t) t := by
    have hp : HasDerivAt (fun t : ℝ => w + t • s) s t := by
      simpa using ((hasDerivAt_id t).smul_const s).const_add w
    have hh := ((GradientDependentLocal.derivative_chain hf).2.2 (w + t • s)).comp_hasDerivAt t hp
    convert (hh.sub_const (H w)).sub ((hasDerivAt_id t).smul_const (T w s)) using 1
    · rfl
    · simp [d, T, H]
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖d t‖ ≤ (L * ‖s‖ ^ 2) * t ^ 1 := by
    have hh := hT (w + t • s) w
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
    calc
      _ ≤ ‖T (w + t • s) - T w‖ * ‖s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * (t * ‖s‖)) * ‖s‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg s)
      _ = _ := by ring
  have hh := power_bound_one 1 hd hb
  simpa [r, H, T] using hh

lemma gradient_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L : ℝ}
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w s : E) :
    ‖gradient f (w + s) - gradient f w - fderiv ℝ (gradient f) w s -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (gradient f)) w s s‖ ≤ L * ‖s‖ ^ 3 / 6 := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let r := fun t : ℝ => gradient f (w + t • s) - gradient f w -
    t • H w s - (t ^ 2 / 2) • T w s s
  let d := fun t : ℝ => H (w + t • s) s - H w s - t • T w s s
  have hd (t : ℝ) : HasDerivAt r (d t) t := by
    have hp : HasDerivAt (fun t : ℝ => w + t • s) s t := by
      simpa using ((hasDerivAt_id t).smul_const s).const_add w
    have hg := ((GradientDependentLocal.derivative_chain hf).2.1 (w + t • s)).comp_hasDerivAt t hp
    convert ((hg.sub_const (gradient f w)).sub ((hasDerivAt_id t).smul_const (H w s))).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).smul_const (T w s s)) using 1
    · rfl
    · dsimp [d, H]
      module
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖d t‖ ≤ (L * ‖s‖ ^ 3 / 2) * t ^ 2 := by
    have he : d t = (H (w + t • s) - H w - T w (t • s)) s := by simp [d, map_smul]
    rw [he]
    have hh := hessian_remainder hf hT w (t • s)
    calc
      _ ≤ ‖H (w + t • s) - H w - T w (t • s)‖ * ‖s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * ‖t • s‖ ^ 2 / 2) * ‖s‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg s)
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]; ring
  have hh := power_bound_one 2 hd hb
  norm_num [r, H, T, div_div] at hh ⊢
  exact hh

lemma third_mixed_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ}
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w s v : E) :
    ⟪fderiv ℝ (fderiv ℝ (gradient f)) w s v, v⟫ ^ 2 ≤
      2 * L * ‖s‖ ^ 2 * ‖v‖ ^ 2 * ⟪fderiv ℝ (gradient f) w v, v⟫ := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let A := ⟪H w v, v⟫
  let B := ⟪T w s v, v⟫
  let C := L * ‖s‖ ^ 2 * ‖v‖ ^ 2
  have hsupp (a b : E) : f a + ⟪gradient f a, b - a⟫ + (0 : ℝ) / 2 * ‖b - a‖ ^ 2 ≤ f b := by
    have hh := OracleTemplate.Gradient.convex_support hc
      (fun x => (hf.differentiable (by norm_num) x).hasGradientAt) a b
    linarith
  have hpos (x : E) : 0 ≤ ⟪H x v, v⟫ := by
    have hh := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound
      ((GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num)) hsupp x v
    simpa [H, real_inner_comm] using hh
  have hpoly (t : ℝ) : 0 ≤ (C / 2) * (t * t) + B * t + A := by
    let R := H (w + t • s) - H w - T w (t • s)
    have hr := hessian_remainder hf hT w (t • s)
    have hi : |⟪R v, v⟫| ≤ (C / 2) * t ^ 2 := by
      calc
        _ ≤ ‖R v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖R‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.le_opNorm R v) (norm_nonneg v)
        _ ≤ ((L * ‖t • s‖ ^ 2 / 2) * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (norm_nonneg v)) (norm_nonneg v)
        _ = _ := by rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]; dsimp [C]; ring
    have he : ⟪R v, v⟫ = ⟪H (w + t • s) v, v⟫ - A - t * B := by
      simp [R, A, B, map_smul, inner_sub_left, real_inner_smul_left]
    rw [he] at hi
    have hh := (abs_le.mp hi).2
    have hz := hpos (w + t • s)
    nlinarith
  have hh := discrim_le_zero hpoly
  dsimp [discrim, A, B, C, H, T] at hh
  nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma kernel_comparison {h b c a : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha : a ^ 2 ≤ 2 * b * h) :
    (1 - 1 / Real.sqrt 2) * (h + b + c) ≤ h + b + c + a ∧
      h + b + c + a ≤ (1 + 1 / Real.sqrt 2) * (h + b + c) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk : 0 ≤ h + b + c := by positivity
  have hsq : 2 * a ^ 2 ≤ (h + b + c) ^ 2 := by
    nlinarith [sq_nonneg (h - b), mul_nonneg hh hc, mul_nonneg hb hc, sq_nonneg c]
  have he : (|a| * Real.sqrt 2) ^ 2 = 2 * a ^ 2 := by rw [mul_pow, sq_abs, hs2]; ring
  have habs : |a| * Real.sqrt 2 ≤ h + b + c :=
    (sq_le_sq₀ (by positivity) hk).mp (by rw [he]; exact hsq)
  have habs' : |a| ≤ (h + b + c) / Real.sqrt 2 := (le_div_iff₀ hs).mpr habs
  have hbounds := abs_le.mp habs'
  simp only [div_eq_mul_inv] at hbounds ⊢
  constructor <;> nlinarith only [hbounds.1, hbounds.2]

lemma kernel_hasGradientAt (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) (L : ℝ) (s : E) :
    HasGradientAt (kernelValue H L) (kernelGradient H L s) s := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hq := ((hasFDerivAt_id (𝕜 := ℝ) s).inner ℝ H.hasFDerivAt).const_mul (1 / 2 : ℝ)
  have hp := (QuarticProximalGeometry.value_hasGradientAt s).hasFDerivAt.const_mul L
  convert hq.add hp using 1
  · funext x
    simp [kernelValue, LongTails.Algorithms.QuarticProximal.value]
    ring
  · ext v
    simp [kernelGradient, LongTails.Algorithms.QuarticProximal.grad,
      InnerProductSpace.toDual_apply_apply, hH]
    rw [← hH v s, real_inner_comm v (H s)]
    ring

lemma model_hasGradientAt (g : E) (H : E →L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫)
    (hT₁ : ∀ a b, T a b = T b a)
    (hT₂ : ∀ a b d, ⟪T a b, d⟫ = ⟪T a d, b⟫) (L : ℝ) (s : E) :
    HasGradientAt (modelValue g H T L) (exactGradient g H T L s) s := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hi := (hasFDerivAt_id (𝕜 := ℝ) s)
  have hl := (hasFDerivAt_const g s).inner ℝ hi
  have hk := (kernel_hasGradientAt H hH L s).hasFDerivAt
  have ht := ((T.hasFDerivAt.clm_apply hi).inner ℝ hi).const_mul (1 / 6 : ℝ)
  convert (hl.add hk).add ht using 1
  · funext x
    dsimp [modelValue]
    ring
  · ext v
    simp [exactGradient, kernelGradient, InnerProductSpace.toDual_apply_apply,
      inner_add_left, hT₁ v s, hT₂ s v s]
    ring

omit [FiniteDimensional ℝ E] in
lemma kernel_contDiff (H : E →L[ℝ] E) (L : ℝ) : ContDiff ℝ ⊤ (kernelValue H L) := by
  have hq : ContDiff ℝ ⊤ (fun s => ⟪s, H s⟫ / 2) :=
    (contDiff_id.inner ℝ H.contDiff).div_const 2
  convert hq.add (contDiff_const.mul QuarticProximalGeometry.value_contDiff) using 1
  funext s
  simp [kernelValue, LongTails.Algorithms.QuarticProximal.value]
  ring

omit [FiniteDimensional ℝ E] in
lemma model_contDiff (g : E) (H : E →L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] E) (L : ℝ) :
    ContDiff ℝ ⊤ (modelValue g H T L) := by
  exact ((contDiff_const.inner ℝ contDiff_id).add (kernel_contDiff H L)).add
    (((T.contDiff.clm_apply contDiff_id).inner ℝ contDiff_id).div_const 6)

omit [FiniteDimensional ℝ E] in
lemma kernelGradient_hasFDerivAt (H : E →L[ℝ] E) (L : ℝ) (s : E) :
    HasFDerivAt (kernelGradient H L)
      (H + L • LongTails.Algorithms.QuarticProximal.hess s) s := by
  convert H.hasFDerivAt.add ((QuarticProximalGeometry.grad_hasFDerivAt s).const_smul L) using 1
  funext x
  simp [kernelGradient, LongTails.Algorithms.QuarticProximal.grad, smul_smul]

omit [FiniteDimensional ℝ E] in
lemma modelGradient_hasFDerivAt (g : E) (H : E →L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] E)
    (hT₁ : ∀ a b, T a b = T b a) (L : ℝ) (s : E) :
    HasFDerivAt (exactGradient g H T L)
      (H + T s + L • LongTails.Algorithms.QuarticProximal.hess s) s := by
  have ht := (T.hasFDerivAt.clm_apply (hasFDerivAt_id (𝕜 := ℝ) s)).const_smul (1 / 2 : ℝ)
  have hq := (QuarticProximalGeometry.grad_hasFDerivAt s).const_smul L
  convert (((hasFDerivAt_const g s).add H.hasFDerivAt).add ht).add hq using 1
  · funext x
    simp [exactGradient, LongTails.Algorithms.QuarticProximal.grad, smul_smul]
  · ext v
    simp [hT₁ v s]
    module

lemma model_kernel_comparison {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w s v : E) :
    let H := fderiv ℝ (gradient f) w
    let T := fderiv ℝ (fderiv ℝ (gradient f)) w
    let K := ⟪(H + L • LongTails.Algorithms.QuarticProximal.hess s) v, v⟫
    (1 - 1 / Real.sqrt 2) * K ≤ ⟪(H + T s + L • LongTails.Algorithms.QuarticProximal.hess s) v, v⟫ ∧
      ⟪(H + T s + L • LongTails.Algorithms.QuarticProximal.hess s) v, v⟫ ≤ (1 + 1 / Real.sqrt 2) * K := by
  let H := fderiv ℝ (gradient f) w
  let T := fderiv ℝ (fderiv ℝ (gradient f)) w
  have hsupp (a b : E) : f a + ⟪gradient f a, b - a⟫ + (0 : ℝ) / 2 * ‖b - a‖ ^ 2 ≤ f b := by
    have hh := OracleTemplate.Gradient.convex_support hc
      (fun x => (hf.differentiable (by norm_num) x).hasGradientAt) a b
    linarith
  have hpos : 0 ≤ ⟪H v, v⟫ := by
    have hh := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound
      ((GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num)) hsupp w v
    simpa [H, real_inner_comm] using hh
  have hmix : ⟪T s v, v⟫ ^ 2 ≤ 2 * (L * ‖s‖ ^ 2 * ‖v‖ ^ 2) * ⟪H v, v⟫ := by
    have hh := third_mixed_bound hf hc hT w s v
    dsimp [H, T]
    nlinarith only [hh]
  have hh := kernel_comparison hpos (by positivity : 0 ≤ L * ‖s‖ ^ 2 * ‖v‖ ^ 2)
    (by positivity : 0 ≤ 2 * L * ⟪s, v⟫ ^ 2) hmix
  have hk : ⟪(H + L • LongTails.Algorithms.QuarticProximal.hess s) v, v⟫ =
      ⟪H v, v⟫ + L * ‖s‖ ^ 2 * ‖v‖ ^ 2 + 2 * L * ⟪s, v⟫ ^ 2 := by
    simp [LongTails.Algorithms.QuarticProximal.hess, inner_add_left, real_inner_smul_left,
      two_smul]
    ring
  have hm : ⟪(H + T s + L • LongTails.Algorithms.QuarticProximal.hess s) v, v⟫ =
      ⟪(H + L • LongTails.Algorithms.QuarticProximal.hess s) v, v⟫ + ⟪T s v, v⟫ := by
    simp [inner_add_left]
    ring
  dsimp only
  change (1 - 1 / Real.sqrt 2) * ⟪(H + L • LongTails.Algorithms.QuarticProximal.hess s) v, v⟫ ≤ _ ∧ _ ≤ _
  rw [hm, hk]
  exact hh

lemma relative_support {F K : E → ℝ} {GF GK : E → E}
    {HF HK : E → E →L[ℝ] E} (hF : ∀ x, HasGradientAt F (GF x) x)
    (hK : ∀ x, HasGradientAt K (GK x) x)
    (hGF : ∀ x, HasFDerivAt GF (HF x) x) (hGK : ∀ x, HasFDerivAt GK (HK x) x)
    {a : ℝ} (hcomp : ∀ x v, a * ⟪HK x v, v⟫ ≤ ⟪HF x v, v⟫) (x y : E) :
    a * (K y - K x - ⟪GK x, y - x⟫) ≤ F y - F x - ⟪GF x, y - x⟫ := by
  let path := fun t : ℝ => x + t • (y - x)
  have hp (t : ℝ) : HasDerivAt path (y - x) t := by
    simpa [path] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hdF (t : ℝ) : HasDerivAt (fun r => F (path r)) ⟪GF (path t), y - x⟫ t := by
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      (hF (path t)).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hdK (t : ℝ) : HasDerivAt (fun r => K (path r)) ⟪GK (path t), y - x⟫ t := by
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      (hK (path t)).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hddF (t : ℝ) : HasDerivAt (fun r => ⟪GF (path r), y - x⟫)
      ⟪HF (path t) (y - x), y - x⟫ t := by
    simpa using ((hGF (path t)).comp_hasDerivAt t (hp t)).inner ℝ
      (hasDerivAt_const t (y - x))
  have hddK (t : ℝ) : HasDerivAt (fun r => ⟪GK (path r), y - x⟫)
      ⟪HK (path t) (y - x), y - x⟫ t := by
    simpa using ((hGK (path t)).comp_hasDerivAt t (hp t)).inner ℝ
      (hasDerivAt_const t (y - x))
  have hh := GuardedMetricSupport.scalar_support
    (fun t => (hdF t).sub ((hdK t).const_mul a))
    (fun t => (hddF t).sub ((hddK t).const_mul a))
    (fun t _ => sub_nonneg.mpr (hcomp (path t) (y - x)))
  simp only [Pi.sub_apply, path, zero_smul, add_zero, one_smul, add_sub_cancel, zero_div] at hh
  linarith

lemma model_relative_support {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w x y : E) :
    let g := gradient f w
    let H := fderiv ℝ (gradient f) w
    let T := fderiv ℝ (fderiv ℝ (gradient f)) w
    let D := modelValue g H T L y - modelValue g H T L x - ⟪exactGradient g H T L x, y - x⟫
    (1 - 1 / Real.sqrt 2) * kernelBregman H L x y ≤ D ∧
      D ≤ (1 + 1 / Real.sqrt 2) * kernelBregman H L x y := by
  let g := gradient f w
  let H := fderiv ℝ (gradient f) w
  let T := fderiv ℝ (fderiv ℝ (gradient f)) w
  have hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫ := by
    intro a b
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) w a b).symm
  have hT₁ : ∀ a b, T a b = T b a := ThirdOrderObjectiveGeometry.third_swap_first hf w
  have hT₂ : ∀ a b d, ⟪T a b, d⟫ = ⟪T a d, b⟫ := ThirdOrderObjectiveGeometry.third_swap_last hf w
  have hF := model_hasGradientAt g H T hH hT₁ hT₂ L
  have hK := kernel_hasGradientAt H hH L
  have hGF := modelGradient_hasFDerivAt g H T hT₁ L
  have hGK := kernelGradient_hasFDerivAt H L
  have hlo := relative_support hF hK hGF hGK
    (fun s v => (model_kernel_comparison hf hc hL hT w s v).1) x y
  have hb : 0 < 1 + 1 / Real.sqrt 2 := by positivity
  have hhi := relative_support hK hF hGK hGF (a := 1 / (1 + 1 / Real.sqrt 2))
    (fun s v => by
      have hh := (model_kernel_comparison hf hc hL hT w s v).2
      rw [one_div, ← div_eq_inv_mul]
      apply (div_le_iff₀ hb).mpr
      simpa only [mul_comm] using hh) x y
  rw [one_div, ← div_eq_inv_mul] at hhi
  have hh := (div_le_iff₀ hb).mp hhi
  dsimp only
  exact ⟨hlo, by simpa only [kernelBregman, mul_comm] using hh⟩

omit [FiniteDimensional ℝ E] in
lemma kernel_bregman_decomposition (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) (L : ℝ) (x y : E) :
    kernelBregman H L x y = ⟪y - x, H (y - x)⟫ / 2 +
      L * (LongTails.Algorithms.QuarticProximal.value y - LongTails.Algorithms.QuarticProximal.value x -
        ⟪LongTails.Algorithms.QuarticProximal.grad x, y - x⟫) := by
  simp only [kernelBregman, kernelValue, kernelGradient, LongTails.Algorithms.QuarticProximal.value,
    LongTails.Algorithms.QuarticProximal.grad, map_sub, inner_sub_left, inner_sub_right,
    inner_add_left, real_inner_smul_left]
  have hxy : ⟪H y, x⟫ = ⟪H x, y⟫ := by
    simpa only [real_inner_comm] using (hH y x).symm
  simp only [hH, hxy]
  ring

omit [FiniteDimensional ℝ E] in
lemma kernel_bregman_lower (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) (hpos : ∀ v, 0 ≤ ⟪v, H v⟫)
    {L : ℝ} (hL : 0 ≤ L) (x y : E) :
    L * ‖y - x‖ ^ 4 / 12 ≤ kernelBregman H L x y := by
  rw [kernel_bregman_decomposition H hH]
  have hh := mul_le_mul_of_nonneg_left (QuarticProximalGeometry.uniform_support x y) hL
  have hp := hpos (y - x)
  linarith

omit [FiniteDimensional ℝ E] in
lemma kernel_three_point (H : E →L[ℝ] E) (L : ℝ) (x y u : E) :
    kernelBregman H L x u - kernelBregman H L x y - kernelBregman H L y u =
      ⟪kernelGradient H L y - kernelGradient H L x, u - y⟫ := by
  have he : u - x = (u - y) + (y - x) := by abel
  simp only [kernelBregman, he, inner_add_right, inner_sub_left]
  ring

lemma stepPoint_optimal (H : E →L[ℝ] E) (L : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (x e : E) :
    stepPoint H L ρ x e ∈ Metric.closedBall (0 : E) ρ ∧
      IsMinOn (stepObjective H L x e) (Metric.closedBall (0 : E) ρ) (stepPoint H L ρ x e) := by
  have hc : Continuous (stepObjective H L x e) := by
    have hk := (kernel_contDiff H L).continuous
    unfold stepObjective kernelBregman
    fun_prop
  have hh := (isCompact_closedBall (0 : E) ρ).exists_isMinOn
    (show (Metric.closedBall (0 : E) ρ).Nonempty from ⟨0, by simpa using hρ⟩) hc.continuousOn
  simpa only [stepPoint, dite_eq_left hh] using Classical.choose_spec hh

lemma stepObjective_hasGradientAt (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) (L : ℝ) (x e y : E) :
    HasGradientAt (stepObjective H L x e)
      (e + (2 * (1 + 1 / Real.sqrt 2)) • (kernelGradient H L y - kernelGradient H L x)) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hi := hasFDerivAt_id (𝕜 := ℝ) y
  have he := (hasFDerivAt_const e y).inner ℝ hi
  have hk := (kernel_hasGradientAt H hH L y).hasFDerivAt
  have hl := (hasFDerivAt_const (kernelGradient H L x) y).inner ℝ (hi.sub_const x)
  convert he.add (((hk.sub_const (kernelValue H L x)).sub hl).const_mul
    (2 * (1 + 1 / Real.sqrt 2))) using 1
  · rfl
  · ext v
    simp [InnerProductSpace.toDual_apply_apply]

lemma stepPoint_energy (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) (L : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (x e u : E) (hu : u ∈ Metric.closedBall (0 : E) ρ) :
    let y := stepPoint H L ρ x e
    (2 * (1 + 1 / Real.sqrt 2)) * kernelBregman H L y u ≤
      (2 * (1 + 1 / Real.sqrt 2)) * kernelBregman H L x u -
      (2 * (1 + 1 / Real.sqrt 2)) * kernelBregman H L x y + ⟪e, u - y⟫ := by
  have hm := stepPoint_optimal H L hρ x e
  have hg := stepObjective_hasGradientAt H hH L x e (stepPoint H L ρ x e)
  have hh := PowerMirrorGeometry.minimizer_derivative_nonneg (convex_closedBall (0 : E) ρ)
    hm.1 hu hm.2 hg.hasFDerivAt
  simp only [InnerProductSpace.toDual_apply_apply, inner_add_left, real_inner_smul_left] at hh
  have he := kernel_three_point H L x (stepPoint H L ρ x e) u
  rw [← he] at hh
  dsimp only
  nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma quartic_young {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    r * t ^ 3 ≤ r ^ 4 / 96 + 3 * t ^ 4 := by
  have hh := mul_nonneg (sq_nonneg (r - 3 * t))
    (show 0 ≤ r ^ 2 + 6 * r * t + 27 * t ^ 2 by positivity)
  nlinarith [pow_nonneg hr 4, pow_nonneg ht 4]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma kernel_constants :
    (1 / 4 : ℝ) ≤ 1 - 1 / Real.sqrt 2 ∧ 1 ≤ 1 + 1 / Real.sqrt 2 ∧
      1 + 1 / Real.sqrt 2 ≤ 6 * (1 - 1 / Real.sqrt 2) := by
  have hq : 0 ≤ 1 / Real.sqrt 2 := by positivity
  have hs : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  constructor
  · nlinarith
  constructor
  · linarith
  · nlinarith

lemma estimate_error {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L τ : ℝ}
    (hτ : 0 < τ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (z s : E) :
    ‖estimateGradient (gradient f z) (fderiv ℝ (gradient f) z)
      (gradient f (z + τ • s)) (gradient f (z - τ • s)) L τ s -
      exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
        (fderiv ℝ (fderiv ℝ (gradient f)) z) L s‖ ≤ τ * L * ‖s‖ ^ 3 / 6 := by
  let g := gradient f
  let H := fderiv ℝ (gradient f) z
  let T := fderiv ℝ (fderiv ℝ (gradient f)) z
  let rp := g (z + τ • s) - g z - H (τ • s) - (1 / 2 : ℝ) • T (τ • s) (τ • s)
  let rm := g (z + (-τ) • s) - g z - H ((-τ) • s) -
    (1 / 2 : ℝ) • T ((-τ) • s) ((-τ) • s)
  have hp : ‖rp‖ ≤ L * (τ * ‖s‖) ^ 3 / 6 := by
    simpa only [rp, g, H, T, norm_smul, Real.norm_eq_abs, abs_of_pos hτ] using
      gradient_remainder hf hT z (τ • s)
  have hm : ‖rm‖ ≤ L * (τ * ‖s‖) ^ 3 / 6 := by
    simpa only [rm, g, H, T, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hτ] using
      gradient_remainder hf hT z ((-τ) • s)
  have he : rp + rm = g (z + τ • s) + g (z - τ • s) - (2 : ℝ) • g z - τ ^ 2 • T s s := by
    dsimp [rp, rm]
    simp only [map_smul, smul_apply, neg_apply, map_neg, neg_smul, ← sub_eq_add_neg]
    module
  have hτ0 := ne_of_gt hτ
  have hs : (1 / (2 * τ ^ 2)) * τ ^ 2 = (1 / 2 : ℝ) := by field_simp
  have he' : estimateGradient (g z) H (g (z + τ • s)) (g (z - τ • s)) L τ s -
      exactGradient (g z) H T L s = (1 / (2 * τ ^ 2)) • (rp + rm) := by
    rw [he, smul_sub, smul_smul, hs]
    dsimp [estimateGradient, exactGradient]
    module
  change ‖estimateGradient (g z) H (g (z + τ • s)) (g (z - τ • s)) L τ s -
    exactGradient (g z) H T L s‖ ≤ _
  rw [he', norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * τ ^ 2))]
  calc
    _ ≤ (1 / (2 * τ ^ 2)) * (‖rp‖ + ‖rm‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le rp rm) (by positivity)
    _ ≤ (1 / (2 * τ ^ 2)) * (L * (τ * ‖s‖) ^ 3 / 6 + L * (τ * ‖s‖) ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left (add_le_add hp hm) (by positivity)
    _ = _ := by field_simp; ring

lemma eval_probes {n : ℕ} (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (g : E) (H : E →L[ℝ] E) (L τ : ℝ) (z s : E) :
    eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (probes g H L τ z s) =
      estimateGradient g H (gradient (objective f) (z + τ • s))
        (gradient (objective f) (z - τ • s)) L τ s := by
  simp only [probes, eval_bind, eval_map, snapshot, TaylorCorrectedStep.eval_collect,
    meanGradient, id_eq, FiniteSumThirdSmoothGeometry.objective_gradient f hf]

end LongTails.Proofs.TensorFreeModel
