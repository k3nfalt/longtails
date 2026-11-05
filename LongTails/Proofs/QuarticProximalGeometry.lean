import LongTails.Algorithms.QuarticProximal
import LongTails.Proofs.LoraObjective
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

namespace LongTails.Proofs.QuarticProximalGeometry

open LongTails.Algorithms.QuarticProximal
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma uniform_support (x y : E) :
    value x + ⟪grad x, y - x⟫ + ‖y - x‖ ^ 4 / 12 ≤ value y := by
  let s := y - x
  have he : y = x + s := by dsimp [s]; abel
  have hnorm : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, s⟫ + ‖s‖ ^ 2 := by
    rw [he, norm_add_sq_real]
  have hcs := real_inner_mul_inner_self_le x s
  simp only [real_inner_self_eq_norm_sq] at hcs
  have hs := sq_nonneg (3 * ⟪x, s⟫ + ‖s‖ ^ 2)
  have hx4 : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
  have hy4 : ‖y‖ ^ 4 = (‖y‖ ^ 2) ^ 2 := by ring
  have hs4 : ‖s‖ ^ 4 = (‖s‖ ^ 2) ^ 2 := by ring
  dsimp [value, grad]
  rw [real_inner_smul_left]
  change ‖x‖ ^ 4 / 4 + ‖x‖ ^ 2 * ⟪x, s⟫ + ‖s‖ ^ 4 / 12 ≤ ‖y‖ ^ 4 / 4
  rw [hx4, hy4, hs4, hnorm]
  nlinarith

lemma value_contDiff : ContDiff ℝ ⊤ (value : E → ℝ) := by
  convert ((contDiff_norm_sq ℝ (E := E)).pow 2).div_const 4 using 1
  funext x
  dsimp [value]
  ring

lemma grad_hasFDerivAt (x : E) : HasFDerivAt (grad : E → E) (hess x) x := by
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.smul (hasFDerivAt_id x) using 1
  · rfl
  · ext v
    simp [hess]
    module

lemma grad_contDiff : ContDiff ℝ ⊤ (grad : E → E) :=
  (contDiff_norm_sq ℝ).smul contDiff_id

lemma hess_contDiff : ContDiff ℝ ⊤ (hess : E → E →L[ℝ] E) := by
  have he : fderiv ℝ (grad : E → E) = hess := funext (fun x => (grad_hasFDerivAt x).fderiv)
  rw [← he]
  exact grad_contDiff.fderiv_right (by simp)

set_option maxHeartbeats 800000 in
lemma hess_derivative_apply (x u v : E) :
    fderiv ℝ (hess : E → E →L[ℝ] E) x u v =
      (2 * ⟪x, u⟫) • v + (2 * ⟪u, v⟫) • x + (2 * ⟪x, v⟫) • u := by
  have hp : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hh := ((((hess_contDiff (E := E)).differentiable (by simp))
    (x + 0 • u)).hasFDerivAt.comp_hasDerivAt 0 hp).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have hi := HasDerivAt.inner ℝ hp (hasDerivAt_const (0 : ℝ) v)
  have he := (hp.norm_sq.smul_const v).add ((hi.const_mul 2).smul hp)
  have he' : HasDerivAt (fun t : ℝ => hess (x + t • u) v)
      ((2 * ⟪x, u⟫) • v + (2 * ⟪u, v⟫) • x + (2 * ⟪x, v⟫) • u) 0 := by
    convert he using 1
    · funext t
      simp [hess, innerSL_apply_apply, smul_smul, inner_add_left, inner_smul_left]
      module
    · simp only [zero_smul, add_zero, inner_zero_right, add_zero]
      module
  simpa [Function.comp_def] using hh.unique he'

set_option maxHeartbeats 800000 in
lemma hess_derivative_lipschitz (x y : E) :
    ‖fderiv ℝ (hess : E → E →L[ℝ] E) x - fderiv ℝ hess y‖ ≤ 6 * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : (fderiv ℝ (hess : E → E →L[ℝ] E) x - fderiv ℝ hess y) u v =
      (2 * ⟪x - y, u⟫) • v + (2 * ⟪u, v⟫) • (x - y) +
        (2 * ⟪x - y, v⟫) • u := by
    simp only [sub_apply, hess_derivative_apply, inner_sub_left]
    module
  rw [he]
  calc
    _ ≤ ‖(2 * ⟪x - y, u⟫) • v‖ + ‖(2 * ⟪u, v⟫) • (x - y)‖ +
        ‖(2 * ⟪x - y, v⟫) • u‖ := norm_add₃_le
    _ ≤ (2 * (‖x - y‖ * ‖u‖)) * ‖v‖ + (2 * (‖u‖ * ‖v‖)) * ‖x - y‖ +
        (2 * (‖x - y‖ * ‖v‖)) * ‖u‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
      · exact abs_real_inner_le_norm _ _
      · exact abs_real_inner_le_norm _ _
      · exact abs_real_inner_le_norm _ _
    _ = _ := by ring

lemma value_convex : ConvexOn ℝ Set.univ (value : E → ℝ) := by
  apply LoraObjective.support_convex (g := grad)
  intro x y
  have h := uniform_support x y
  have hp : 0 ≤ ‖y - x‖ ^ 4 / 12 := by positivity
  linarith

variable [CompleteSpace E]

lemma value_hasGradientAt (x : E) : HasGradientAt (value : E → ℝ) (grad x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.pow 2).mul_const (1 / 4 : ℝ) using 1
  · funext y
    dsimp [value]
    ring
  · ext v
    simp [grad, innerSL_apply_apply, InnerProductSpace.toDual_apply_apply]
    ring

lemma value_third_lipschitz (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value : E → ℝ))) x -
      fderiv ℝ (fderiv ℝ (gradient (value : E → ℝ))) y‖ ≤ 6 * ‖x - y‖ := by
  have hg : gradient (value : E → ℝ) = grad := gradient_eq value_hasGradientAt
  have hh : fderiv ℝ (grad : E → E) = hess :=
    funext (fun z => (grad_hasFDerivAt z).fderiv)
  rw [hg, hh]
  exact hess_derivative_lipschitz x y

omit [CompleteSpace E] in
lemma penalty_contDiff (γ μ : ℝ) (c y0 : E) :
    ContDiff ℝ ⊤ (penalty γ μ c y0) := by
  exact (contDiff_const.mul (value_contDiff.comp (contDiff_id.sub contDiff_const))).add
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma penalty_hasGradientAt (γ μ : ℝ) (c y0 x : E) :
    HasGradientAt (penalty γ μ c y0) (penaltyGrad γ μ c y0 x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hq := (value_hasGradientAt (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c)
  have hn := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y0).norm_sq
  convert (hq.const_mul γ).add (hn.const_mul (μ / 2)) using 1
  · rfl
  · ext u
    simp [penaltyGrad, InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    ring

omit [CompleteSpace E] in
lemma penaltyGrad_hasFDerivAt (γ μ : ℝ) (c y0 x : E) :
    HasFDerivAt (penaltyGrad γ μ c y0) (penaltyHess γ μ c x) x := by
  have hq := (grad_hasFDerivAt (x - c)).comp x ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c)
  convert (hq.const_smul γ).add (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y0).const_smul μ) using 1
  · rfl
  · simp only [penaltyHess, ContinuousLinearMap.comp_id]

omit [CompleteSpace E] in
lemma penaltyHess_derivative (γ μ : ℝ) (c x : E) :
    fderiv ℝ (penaltyHess γ μ c) x = γ • fderiv ℝ (hess : E → E →L[ℝ] E) (x - c) := by
  have hh := ((hess_contDiff (E := E)).differentiable (by simp) (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c)
  have hd : HasFDerivAt (penaltyHess γ μ c)
      (γ • fderiv ℝ (hess : E → E →L[ℝ] E) (x - c)) x := by
    convert (hh.const_smul γ).add_const (μ • ContinuousLinearMap.id ℝ E) using 1
    · rfl
    · simp only [ContinuousLinearMap.comp_id]
  exact hd.fderiv

lemma penalty_third_lipschitz {γ μ : ℝ} (hγ : 0 ≤ γ) (c y0 x y : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) x -
      fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) y‖ ≤ 6 * γ * ‖x - y‖ := by
  have hg : gradient (penalty γ μ c y0) = penaltyGrad γ μ c y0 :=
    gradient_eq (penalty_hasGradientAt γ μ c y0)
  have hh : fderiv ℝ (penaltyGrad γ μ c y0) = penaltyHess γ μ c :=
    funext (fun z => (penaltyGrad_hasFDerivAt γ μ c y0 z).fderiv)
  rw [hg, hh, penaltyHess_derivative, penaltyHess_derivative]
  have heq : γ • fderiv ℝ (hess : E → E →L[ℝ] E) (x - c) -
      γ • fderiv ℝ hess (y - c) = γ • (fderiv ℝ hess (x - c) - fderiv ℝ hess (y - c)) :=
    (smul_sub γ _ _).symm
  rw [heq]
  let T := fderiv ℝ (hess : E → E →L[ℝ] E) (x - c) - fderiv ℝ hess (y - c)
  have hb : ‖T‖ ≤ 6 * ‖x - y‖ := by
    have he : x - c - (y - c) = x - y := by abel
    simpa only [T, he] using hess_derivative_lipschitz (x - c) (y - c)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖((γ • T) u) v‖ ≤ (6 * γ * ‖x - y‖ * ‖u‖) * ‖v‖
  calc
    _ = γ * ‖T u v‖ := by simp only [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    _ ≤ γ * (‖T‖ * ‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left
      (((T u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (T.le_opNorm u) (norm_nonneg v))) hγ
    _ ≤ γ * ((6 * ‖x - y‖) * ‖u‖ * ‖v‖) := by gcongr
    _ = _ := by ring

omit [CompleteSpace E] in
lemma penalty_support {γ μ : ℝ} (hγ : 0 ≤ γ) (c y0 x y : E) :
    penalty γ μ c y0 x + ⟪penaltyGrad γ μ c y0 x, y - x⟫ +
      γ * ‖y - x‖ ^ 4 / 12 + μ * ‖y - x‖ ^ 2 / 2 ≤ penalty γ μ c y0 y := by
  have hq := mul_le_mul_of_nonneg_left (uniform_support (x - c) (y - c)) hγ
  have he : y - c - (x - c) = y - x := by abel
  rw [he] at hq
  have hn : ‖y - y0‖ ^ 2 = ‖x - y0‖ ^ 2 + 2 * ⟪x - y0, y - x⟫ + ‖y - x‖ ^ 2 := by
    convert norm_add_sq_real (x - y0) (y - x) using 1
    congr 2
    abel
  simp only [penalty, penaltyGrad, inner_add_left, real_inner_smul_left]
  rw [hn]
  nlinarith

lemma add_penalty_hasGradientAt {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasGradientAt f (g x) x) (γ μ : ℝ) (c y0 x : E) :
    HasGradientAt (fun z => f z + penalty γ μ c y0 z)
      (g x + penaltyGrad γ μ c y0 x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hf x).hasFDerivAt.add (penalty_hasGradientAt γ μ c y0 x).hasFDerivAt using 1
  exact map_add _ _ _

lemma add_penalty_support {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasGradientAt f (g x) x) (hc : ConvexOn ℝ Set.univ f)
    {γ μ : ℝ} (hγ : 0 ≤ γ) (c y0 x y : E) :
    f x + penalty γ μ c y0 x + ⟪g x + penaltyGrad γ μ c y0 x, y - x⟫ +
      γ * ‖y - x‖ ^ 4 / 12 + μ * ‖y - x‖ ^ 2 / 2 ≤ f y + penalty γ μ c y0 y := by
  have hq := penalty_support (μ := μ) hγ c y0 x y
  have hs := OracleTemplate.Gradient.convex_support hc hf x y
  rw [inner_add_left]
  linarith

end LongTails.Proofs.QuarticProximalGeometry
