import LongTails.Proofs.NearestSetPotential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set Metric Filter InnerProductSpace
open scoped RealInnerProductSpace Topology

namespace OracleTemplate.NearestSet

lemma radial_growth {F F' : ℝ → ℝ} {c : ℝ} (hzero : F 0 = 0)
    (hderiv0 : HasDerivAt F 0 0)
    (hderiv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (haim : ∀ t ∈ Ioc (0 : ℝ) 1, F t + c * t ^ 2 ≤ t * F' t) :
    c ≤ F 1 := by
  let H := fun t : ℝ => F t / t - c * t
  have hH : ∀ t ∈ Ioc (0 : ℝ) 1,
      HasDerivAt H ((F' t * t - F t) / t ^ 2 - c) t := by
    intro t ht
    convert ((hderiv t ht).div (hasDerivAt_id t) ht.1.ne').sub
      ((hasDerivAt_id t).const_mul c) using 1 <;> simp [H]; rfl
  have hmono : MonotoneOn H (Ioc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · exact fun t ht => (hH t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hH t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioc (0 : ℝ) 1 := interior_subset ht
      rw [(hH t ht').deriv]
      have h := haim t ht'
      apply sub_nonneg.mpr
      apply (le_div_iff₀ (sq_pos_of_pos ht'.1)).mpr
      nlinarith
  have hlimF : Tendsto (fun t : ℝ => F t / t) (𝓝[>] 0) (𝓝 0) := by
    simpa [hzero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hderiv0.tendsto_slope_zero_right
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto H (𝓝[>] 0) (𝓝 0) := by
    simpa [H] using hlimF.sub (tendsto_const_nhds.mul ht)
  have hle : 0 ≤ H 1 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht0 ht1
    exact hmono ⟨ht0, ht1.le⟩ (by simp) ht1.le
  simpa [H] using hle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma nearest_segment {M : Set E} {x p : E} (hp : p ∈ M)
    (hnear : infDist x M = ‖x - p‖) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    infDist (p + t • (x - p)) M = t * infDist x M := by
  have hupper := infDist_le_dist_of_mem (x := p + t • (x - p)) hp
  have hlower : infDist x M ≤ infDist (p + t • (x - p)) M +
      dist x (p + t • (x - p)) := infDist_le_infDist_add_dist
  have hvec : x - (p + t • (x - p)) = (1 - t) • (x - p) := by module
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    ← hnear] at hupper
  rw [dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr ht1), ← hnear] at hlower
  linarith

lemma local_quadratic_growth [CompleteSpace E] {M : Set E} {f : E → ℝ} {g : E → E}
    {μ r : ℝ} {x p : E} (hg : ∀ y, HasGradientAt f (g y) y)
    (hp : p ∈ M) (hmin : IsMinOn f univ p)
    (hnear : infDist x M = ‖x - p‖) (hx : infDist x M < r)
    (haim : ∀ y z, infDist y M < r → z ∈ M → infDist y M = ‖y - z‖ →
      f y - f p + μ / 2 * ‖y - z‖ ^ 2 ≤ ⟪g y, y - z⟫) :
    μ / 2 * ‖x - p‖ ^ 2 ≤ f x - f p := by
  let F := fun t : ℝ => f (p + t • (x - p)) - f p
  let F' := fun t : ℝ => ⟪g (p + t • (x - p)), x - p⟫
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h := ((hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const (x - p) |>.const_add p)).sub_const (f p)
    simpa [F, F', toDual_apply_apply] using h
  have hFzero : F 0 = 0 := by simp [F]
  have hFmin : IsLocalMin F 0 := by
    apply Filter.Eventually.of_forall
    intro t
    dsimp [F]
    simp only [zero_smul, add_zero, sub_self]
    exact sub_nonneg.mpr (hmin (mem_univ _))
  have hF'zero : F' 0 = 0 := hFmin.hasDerivAt_eq_zero (hF 0)
  have hbound := radial_growth (c := μ / 2 * ‖x - p‖ ^ 2) hFzero
    (by simpa only [hF'zero] using hF 0) (fun t _ => hF t) (by
      intro t ht
      have hseg := nearest_segment hp hnear ht.1.le ht.2
      have hnear' : infDist (p + t • (x - p)) M = ‖p + t • (x - p) - p‖ := by
        rw [hseg, hnear]
        simp [norm_smul, abs_of_pos ht.1]
      have hrad : infDist (p + t • (x - p)) M < r := by
        rw [hseg]
        exact (mul_le_of_le_one_left infDist_nonneg ht.2).trans_lt hx
      have h := haim (p + t • (x - p)) p hrad hp hnear'
      simp only [add_sub_cancel_left, inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht.1, mul_pow] at h
      dsimp [F, F']
      nlinarith only [h])
  simpa [F] using hbound

lemma segment_upper_bound [CompleteSpace E] {f : E → ℝ} {g : E → E} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x) (x y : E)
    (hlip : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖g (x + t • (y - x)) - g x‖ ≤ L * t * ‖y - x‖) :
    f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let F := fun t : ℝ => f (x + t • d)
  let F' := fun t : ℝ => ⟪g (x + t • d), d⟫
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h := (hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const d |>.const_add x)
    simp only [id_eq, one_smul, toDual_apply_apply] at h
    exact h
  let B := fun t : ℝ => f x + t * ⟪g x, d⟫ + t ^ 2 * (L / 2 * ‖d‖ ^ 2)
  have hB : ∀ t, HasDerivAt B (⟪g x, d⟫ + L * ‖d‖ ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).mul_const ⟪g x, d⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * ‖d‖ ^ 2)) using 1
    · funext u
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1, F' t ≤ ⟪g x, d⟫ + L * ‖d‖ ^ 2 * t := by
    intro t ht
    have h := (real_inner_le_norm (g (x + t • d) - g x) d).trans
      (mul_le_mul_of_nonneg_right (hlip t ht) (norm_nonneg d))
    simp only [inner_sub_left] at h
    dsimp [F']
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, d] using h

lemma gradient_bound [CompleteSpace E] {M : Set E} {f : E → ℝ} {g : E → E}
    {L r : ℝ} (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, infDist x M < r → infDist y M < r →
      ‖g x - g y‖ ≤ L * ‖x - y‖)
    {x p : E} (hp : p ∈ M) (hmin : IsMinOn f univ p)
    (hnear : infDist x M = ‖x - p‖) (hx : infDist x M < r) :
    ‖g x‖ ≤ L * infDist x M := by
  have hzero : g p = 0 := by
    apply (toDual ℝ E).injective
    simpa using (hmin.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hg p).hasFDerivAt
  have hr : 0 < r := lt_of_le_of_lt infDist_nonneg hx
  have h := hlip x p hx (by simpa [infDist_zero_of_mem hp] using hr)
  simpa [hzero, ← hnear] using h

lemma descent_on_segment [CompleteSpace E] {M : Set E} {f : E → ℝ} {g : E → E}
    {L r s : ℝ} (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, infDist x M < r → infDist y M < r →
      ‖g x - g y‖ ≤ L * ‖x - y‖)
    {y : E} (hy : infDist y M < r) (hstep : s ^ 2 * L ≤ 1)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, infDist (y - (t * s ^ 2) • g y) M < r) :
    f (y - s ^ 2 • g y) ≤ f y - s ^ 2 / 2 * ‖g y‖ ^ 2 := by
  have h := segment_upper_bound hg y (y - s ^ 2 • g y) (by
    intro t ht
    have he : y + t • (y - s ^ 2 • g y - y) = y - (t * s ^ 2) • g y := by module
    have hh := hlip (y + t • (y - s ^ 2 • g y - y)) y
      (by rw [he]; exact hsegment t ⟨ht.1, ht.2.le⟩) hy
    simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, mul_assoc] using hh)
  have he : y - s ^ 2 • g y - y = -(s ^ 2) • g y := by module
  rw [he] at h
  simp only [inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at h
  have hb := mul_le_mul_of_nonneg_right hstep
    (show 0 ≤ s ^ 2 / 2 * ‖g y‖ ^ 2 by positivity)
  nlinarith only [h, hb]

end OracleTemplate.NearestSet
