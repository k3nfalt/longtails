import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ImplicitContDiff

set_option maxSynthPendingDepth 3

namespace LongTails.Proofs.BilevelImplicit

open Filter
open scoped Topology ContDiff

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma contDiff_root {F : X × Y → Y} {s : X → Y} {n : ℕ∞ω}
    (hF : ContDiff ℝ n F) (hn : n ≠ 0) (hs : ∀ x, F (x, s x) = 0)
    (hu : ∀ x y, F (x, y) = 0 → y = s x)
    (hi : ∀ x, (fderiv ℝ F (x, s x) ∘L .inr ℝ X Y).IsInvertible) :
    ContDiff ℝ n s := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hc := hF.contDiffAt (x := (x, s x))
  have he : s =ᶠ[𝓝 x] hc.implicitFunction hn (hi x) := by
    filter_upwards [hc.eventually_apply_implicitFunction hn (hi x)] with z hz
    exact (hu z _ (hz.trans (hs x))).symm
  exact (hc.contDiffAt_implicitFunction hn (hi x)).congr_of_eventuallyEq he

lemma hasFDerivAt_root {F : X × Y → Y} {s : X → Y} {n : ℕ∞ω}
    (hF : ContDiff ℝ n F) (hn : n ≠ 0) (hs : ∀ x, F (x, s x) = 0)
    (hu : ∀ x y, F (x, y) = 0 → y = s x)
    (hi : ∀ x, (fderiv ℝ F (x, s x) ∘L .inr ℝ X Y).IsInvertible) (x : X) :
    HasFDerivAt s (-(fderiv ℝ F (x, s x) ∘L .inr ℝ X Y).inverse ∘L
      (fderiv ℝ F (x, s x) ∘L .inl ℝ X Y)) x := by
  have hc := hF.contDiffAt (x := (x, s x))
  have he : s =ᶠ[𝓝 x] hc.implicitFunction hn (hi x) := by
    filter_upwards [hc.eventually_apply_implicitFunction hn (hi x)] with z hz
    exact (hu z _ (hz.trans (hs x))).symm
  exact (hc.hasStrictFDerivAt_implicitFunction hn (hi x)).hasFDerivAt.congr_of_eventuallyEq he


omit [CompleteSpace X] [CompleteSpace Y] in
lemma root_first_equation {F : X × Y → Y} {s : X → Y}
    (hF : Differentiable ℝ F) (hs : Differentiable ℝ s) (hr : ∀ x, F (x, s x) = 0)
    (x a : X) : fderiv ℝ F (x, s x) (a, fderiv ℝ s x a) = 0 := by
  have hd := (hF (x, s x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hs x).hasFDerivAt)
  have he : (fun x => F (x, s x)) = fun _ => (0 : Y) := funext hr
  simp only [Function.comp_def, id_eq] at hd
  rw [he] at hd
  have hz := hd.unique (hasFDerivAt_const (0 : Y) x)
  exact DFunLike.congr_fun hz a

omit [CompleteSpace X] [CompleteSpace Y] in
lemma root_second_equation {F : X × Y → Y} {s : X → Y}
    (hF : ContDiff ℝ 2 F) (hs : ContDiff ℝ 2 s) (hr : ∀ x, F (x, s x) = 0)
    (x a b : X) :
    fderiv ℝ (fderiv ℝ F) (x, s x) (b, fderiv ℝ s x b) (a, fderiv ℝ s x a) +
      fderiv ℝ F (x, s x) (0, fderiv ℝ (fderiv ℝ s) x b a) = 0 := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := (contDiff_succ_iff_fderiv.mp hF).2.2
  have hs1 : ContDiff ℝ 1 (fderiv ℝ s) := (contDiff_succ_iff_fderiv.mp hs).2.2
  have hl : HasDerivAt (fun t : ℝ => x + t • b) b 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const b |>.const_add x
  have hsl := ((hs.differentiable (by norm_num) (x + (0 : ℝ) • b)).hasFDerivAt).comp_hasDerivAt 0 hl
  simp only [zero_smul, add_zero] at hsl
  have hz := hl.prodMk hsl
  have hdF := ((hF1.differentiable (by norm_num) (x + (0 : ℝ) • b, s (x + (0 : ℝ) • b))).hasFDerivAt).comp_hasDerivAt 0 hz
  have hds := ((hs1.differentiable (by norm_num) (x + (0 : ℝ) • b)).hasFDerivAt).comp_hasDerivAt 0 hl
  have hv := (hasDerivAt_const (0 : ℝ) a).prodMk
    (hds.clm_apply (hasDerivAt_const (0 : ℝ) a))
  have hd := hdF.clm_apply hv
  have he : (fun t : ℝ => fderiv ℝ F (x + t • b, s (x + t • b))
      (a, fderiv ℝ s (x + t • b) a)) = fun _ => (0 : Y) := by
    funext t
    exact root_first_equation (hF.differentiable (by norm_num))
      (hs.differentiable (by norm_num)) hr _ a
  simp only [Function.comp_def, zero_smul, add_zero] at hd
  rw [he] at hd
  simpa [add_comm] using hd.unique (hasDerivAt_const (0 : ℝ) (0 : Y))



omit [CompleteSpace X] [CompleteSpace Y] in
lemma graph_composite_first {f : X × Y → ℝ} {s : X → Y}
    (hf : Differentiable ℝ f) (hs : Differentiable ℝ s) (x a : X) :
    fderiv ℝ (fun x => f (x, s x)) x a = fderiv ℝ f (x, s x) (a, fderiv ℝ s x a) := by
  have hd := (hf (x, s x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hs x).hasFDerivAt)
  have he := hd.fderiv
  simp only [Function.comp_def, id_eq] at he
  rw [he]
  rfl

omit [CompleteSpace X] [CompleteSpace Y] in
lemma graph_composite_second {f : X × Y → ℝ} {s : X → Y}
    (hf : ContDiff ℝ 2 f) (hs : ContDiff ℝ 2 s) (x a b : X) :
    fderiv ℝ (fderiv ℝ (fun x => f (x, s x))) x b a =
      fderiv ℝ (fderiv ℝ f) (x, s x) (b, fderiv ℝ s x b) (a, fderiv ℝ s x a) +
        fderiv ℝ f (x, s x) (0, fderiv ℝ (fderiv ℝ s) x b a) := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  have hs1 : ContDiff ℝ 1 (fderiv ℝ s) := (contDiff_succ_iff_fderiv.mp hs).2.2
  have hF : ContDiff ℝ 2 (fun x => f (x, s x)) := hf.comp (contDiff_id.prodMk hs)
  have hF1 : ContDiff ℝ 1 (fderiv ℝ (fun x => f (x, s x))) :=
    (contDiff_succ_iff_fderiv.mp hF).2.2
  have hl : HasDerivAt (fun t : ℝ => x + t • b) b 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const b |>.const_add x
  have hsl := ((hs.differentiable (by norm_num) (x + (0 : ℝ) • b)).hasFDerivAt).comp_hasDerivAt 0 hl
  simp only [zero_smul, add_zero] at hsl
  have hz := hl.prodMk hsl
  have hdf := ((hf1.differentiable (by norm_num)
    (x + (0 : ℝ) • b, s (x + (0 : ℝ) • b))).hasFDerivAt).comp_hasDerivAt 0 hz
  have hds := ((hs1.differentiable (by norm_num) (x + (0 : ℝ) • b)).hasFDerivAt).comp_hasDerivAt 0 hl
  have hv := (hasDerivAt_const (0 : ℝ) a).prodMk
    (hds.clm_apply (hasDerivAt_const (0 : ℝ) a))
  have hd := hdf.clm_apply hv
  have hdirect := (((hF1.differentiable (by norm_num) (x + (0 : ℝ) • b)).hasFDerivAt).comp_hasDerivAt 0 hl).clm_apply
    (hasDerivAt_const (0 : ℝ) a)
  have he : (fun t : ℝ => fderiv ℝ (fun x => f (x, s x)) (x + t • b) a) =
      (fun t : ℝ => fderiv ℝ f (x + t • b, s (x + t • b))
        (a, fderiv ℝ s (x + t • b) a)) := by
    funext t
    exact graph_composite_first (hf.differentiable (by norm_num))
      (hs.differentiable (by norm_num)) _ a
  simp only [Function.comp_def, zero_smul, add_zero, map_zero] at hd hdirect
  rw [he] at hdirect
  simpa [add_comm] using hdirect.unique hd

omit [CompleteSpace X] [CompleteSpace Y] in
lemma norm_increment_le_of_right_slope {z : ℝ → Y} {a b C : ℝ} (hab : a ≤ b)
    (hz : ContinuousOn z (Set.Icc a b))
    (hs : ∀ s ∈ Set.Ico a b, ∀ r, C < r →
      ∃ᶠ t in 𝓝[>] s, ‖slope z s t‖ < r) : ‖z b - z a‖ ≤ C * (b - a) := by
  let f : ℝ → ℝ := fun t => ‖z t - z a‖
  let B : ℝ → ℝ := fun t => C * (t - a)
  have hf : ContinuousOn f (Set.Icc a b) := (hz.sub continuousOn_const).norm
  have hB : ContinuousOn B (Set.Icc a b) := by fun_prop
  have hBd : ∀ t, HasDerivAt B C t := by
    intro t
    simpa [B] using ((hasDerivAt_id t).sub_const a).const_mul C
  have hbound : ∀ s ∈ Set.Ico a b, ∀ r, C < r →
      ∃ᶠ t in 𝓝[>] s, slope f s t < r := by
    intro s hmem r hr
    have hh := (hs s hmem r hr).and_eventually self_mem_nhdsWithin
    apply hh.mono
    intro t ht
    have hst : 0 < t - s := sub_pos.mpr ht.2
    have hn : ‖z t - z a‖ - ‖z s - z a‖ ≤ ‖z t - z s‖ := by
      simpa only [sub_sub_sub_cancel_right] using norm_sub_norm_le (z t - z a) (z s - z a)
    have he : slope f s t ≤ ‖slope z s t‖ := by
      simp only [slope_def_module, f, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hst, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hst.le)
    exact he.trans_lt ht.1
  have h := image_le_of_liminf_slope_right_le_deriv_boundary hf
    (B := B) (B' := fun _ => C) (by simp [f, B]) hB
    (fun t _ => (hBd t).hasDerivWithinAt) hbound (x := b) ⟨hab, le_rfl⟩
  exact h

omit [CompleteSpace Y] in
lemma norm_increment_le_of_local_slope {z : ℝ → Y} {a b C : ℝ} (hab : a ≤ b)
    (hz : ContinuousOn z (Set.Icc a b))
    (hs : ∀ s ∈ Set.Ico a b, ∀ r, C < r →
      ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖h⁻¹ • (z (s + h) - z s)‖ < r) :
    ‖z b - z a‖ ≤ C * (b - a) := by
  apply norm_increment_le_of_right_slope hab hz
  intro s hmem r hr
  have ht : Tendsto (fun t : ℝ => t - s) (𝓝[>] s) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hsub : Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 (s - s)) := tendsto_id.sub_const s
      simpa using hsub.mono_left (show 𝓝[>] s ≤ 𝓝 s from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_ne_zero.mpr (ne_of_gt ht)
  have hh := ht.eventually (hs s hmem r hr)
  apply Eventually.frequently
  filter_upwards [hh] with t ht
  simpa [slope_def_module] using ht

omit [CompleteSpace X] [CompleteSpace Y] in
lemma norm_sub_le_of_unit_local_slope {f : X → Y} {C : ℝ} (hf : Continuous f)
    (hs : ∀ x w : X, ‖w‖ ≤ 1 → ∀ r : ℝ, C < r →
      ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖h⁻¹ • (f (x + h • w) - f x)‖ < r)
    (x y : X) : ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  by_cases he : y = x
  · simp [he]
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  let w := ‖y - x‖⁻¹ • (y - x)
  have hw : ‖w‖ ≤ 1 := by
    simp [w, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le), hd.ne']
  let z := fun t : ℝ => f (x + t • w)
  have hz : Continuous z := by dsimp [z]; fun_prop
  have hlocal : ∀ s ∈ Set.Ico 0 ‖y - x‖, ∀ r, C < r →
      ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖h⁻¹ • (z (s + h) - z s)‖ < r := by
    intro s _ r hr
    simpa [z, add_smul, add_assoc] using hs (x + s • w) w hw r hr
  have hh := norm_increment_le_of_local_slope hd.le hz.continuousOn hlocal
  have hend : x + ‖y - x‖ • w = y := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
    abel
  simpa [z, hend] using hh

end LongTails.Proofs.BilevelImplicit
