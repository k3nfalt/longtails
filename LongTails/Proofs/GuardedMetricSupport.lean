import LongTails.Proofs.QuarticMetricTransport
import Mathlib.Analysis.Convex.Deriv

namespace LongTails.Proofs.GuardedMetricSupport

open Set
open scoped RealInnerProductSpace

lemma scalar_support {f g h : ℝ → ℝ} {m : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ h t) :
    f 0 + g 0 + m / 2 ≤ f 1 := by
  let r := fun t : ℝ => f t - m * t ^ 2 / 2
  let r' := fun t : ℝ => g t - m * t
  let r'' := fun t : ℝ => h t - m
  have hd (t : ℝ) : HasDerivAt r (r' t) t := by
    convert (hf t).sub ((((hasDerivAt_id t).pow 2).const_mul m).div_const 2) using 1
    · rfl
    · dsimp [r']
      ring
  have hd' (t : ℝ) : HasDerivAt r' (r'' t) t := by
    convert (hg t).sub ((hasDerivAt_id t).const_mul m) using 1
    · funext s
      rfl
    · simp [r'']
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) r :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t _ => (hd' t).hasDerivWithinAt)
      (fun t ht => sub_nonneg.mpr (hh t (interior_subset ht)))
  have hs := hc.le_slope_of_hasDerivAt (by simp) (by simp) (by norm_num : (0 : ℝ) < 1) (hd 0)
  simp [slope, r, r'] at hs
  linarith

lemma failed_support_conversion {D B n α β μ : ℝ}
    (hB : 0 ≤ B) (hn : 0 ≤ n) (hα : 0 ≤ α) (hβ : 0 < β) (hμ : 0 ≤ μ)
    (hμ₁ : μ ≤ 1 / 8) (htune : μ * β ≤ α / 64)
    (hlower : 7 / 16 * B - 4 * β * n ≤ D)
    (hfailure : D + α * n < μ / 2 * B) :
    B ≤ 20 * β * n ∧ D ≤ -α * n / 2 := by
  have hm := mul_le_mul_of_nonneg_right hμ₁ hB
  have han := mul_nonneg hα hn
  have hbn := mul_nonneg hβ.le hn
  have hb : B ≤ 20 * β * n := by nlinarith
  have hb' := mul_le_mul_of_nonneg_left hb hμ
  have ht := mul_le_mul_of_nonneg_right htune hn
  constructor
  · exact hb
  · nlinarith

lemma scalar_upper {f g h : ℝ → ℝ} {m : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, h t ≤ m) :
    f 1 ≤ f 0 + g 0 + m / 2 := by
  have hs := scalar_support (fun t => (hf t).neg) (fun t => (hg t).neg)
    (fun t ht => neg_le_neg (hh t ht))
  dsimp at hs
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma hessian_support {f : E → ℝ} (hf : ContDiff ℝ 3 f) (u v : E) {m : ℝ}
    (hh : ∀ t ∈ Icc (0 : ℝ) 1,
      m ≤ ⟪fderiv ℝ (gradient f) (v + t • (u - v)) (u - v), u - v⟫) :
    f v + ⟪gradient f v, u - v⟫ + m / 2 ≤ f u := by
  let path := fun t : ℝ => v + t • (u - v)
  have hp (t : ℝ) : HasDerivAt path (u - v) t := by
    convert (hasDerivAt_const t v).add ((hasDerivAt_id t).smul_const (u - v)) using 1
    · funext r
      rfl
    · simp
  obtain ⟨h₀, h₁, h₂⟩ := GradientDependentLocal.derivative_chain hf
  have hd (t : ℝ) : HasDerivAt (fun s => f (path s)) ⟪gradient f (path t), u - v⟫ t := by
    simpa only [Function.comp_def, innerSL_apply_apply] using (h₀ (path t)).comp_hasDerivAt t (hp t)
  have hd' (t : ℝ) : HasDerivAt (fun s => ⟪gradient f (path s), u - v⟫)
      ⟪fderiv ℝ (gradient f) (path t) (u - v), u - v⟫ t := by
    simpa using HasDerivAt.inner ℝ ((h₁ (path t)).comp_hasDerivAt t (hp t))
      (hasDerivAt_const t (u - v))
  simpa [path] using scalar_support hd hd' hh

lemma hessian_upper {f : E → ℝ} (hf : ContDiff ℝ 3 f) (u v : E) {m : ℝ}
    (hh : ∀ t ∈ Icc (0 : ℝ) 1,
      ⟪fderiv ℝ (gradient f) (v + t • (u - v)) (u - v), u - v⟫ ≤ m) :
    f u ≤ f v + ⟪gradient f v, u - v⟫ + m / 2 := by
  let path := fun t : ℝ => v + t • (u - v)
  have hp (t : ℝ) : HasDerivAt path (u - v) t := by
    convert (hasDerivAt_const t v).add ((hasDerivAt_id t).smul_const (u - v)) using 1
    · funext r
      rfl
    · simp
  obtain ⟨h₀, h₁, h₂⟩ := GradientDependentLocal.derivative_chain hf
  have hd (t : ℝ) : HasDerivAt (fun s => f (path s)) ⟪gradient f (path t), u - v⟫ t := by
    simpa only [Function.comp_def, innerSL_apply_apply] using (h₀ (path t)).comp_hasDerivAt t (hp t)
  have hd' (t : ℝ) : HasDerivAt (fun s => ⟪gradient f (path s), u - v⟫)
      ⟪fderiv ℝ (gradient f) (path t) (u - v), u - v⟫ t := by
    simpa using HasDerivAt.inner ℝ ((h₁ (path t)).comp_hasDerivAt t (hp t))
      (hasDerivAt_const t (u - v))
  simpa [path] using scalar_upper hd hd' hh

omit [FiniteDimensional ℝ E] in
lemma segment_radius (S : E ≃L[ℝ] E) (x u v : E) {r t : ℝ}
    (hu : ‖S (u - x)‖ ≤ r) (hv : ‖S (v - x)‖ ≤ r) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖S (v + t • (u - v) - x)‖ ≤ r := by
  have he : S (v + t • (u - v) - x) = (1 - t) • S (v - x) + t • S (u - x) := by
    simp only [map_add, map_sub, map_smul]
    module
  rw [he]
  calc
    _ ≤ ‖(1 - t) • S (v - x)‖ + ‖t • S (u - x)‖ := norm_add_le _ _
    _ = (1 - t) * ‖S (v - x)‖ + t * ‖S (u - x)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * r + t * r := add_le_add
      (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left hu ht.1)
    _ = r := by ring

lemma guarded_support_bounds {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ R : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hR : 0 < R)
    (hΔ : Δ = L * σ ^ 2) (hRΔ : R ^ 2 = Δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x : E) (hgap : ∀ y, f x - f y ≤ Δ) (S : E ≃L[ℝ] E)
    (hS : ∀ v, ‖S v‖ ^ 2 = ⟪fderiv ℝ (gradient f) x v, v⟫ + 8 * L * σ * ‖v‖ ^ 2)
    (u v : E) (hu : ‖S (u - x)‖ ≤ R / 256) (hv : ‖S (v - x)‖ ≤ R / 256) :
    7 / 16 * ‖S (u - v)‖ ^ 2 - 4 * L * σ * ‖u - v‖ ^ 2 ≤
        f u - f v - ⟪gradient f v, u - v⟫ ∧
      f u - f v - ⟪gradient f v, u - v⟫ ≤ 9 / 16 * ‖S (u - v)‖ ^ 2 := by
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    QuarticMetricTransport.guarded_hessian_bound hf hL hσ hR hΔ hRΔ hT x hgap S hS
      (v + t • (u - v) - x) (u - v) (segment_radius S x u v hu hv ht)
  have hx (t : ℝ) : x + (v + t • (u - v) - x) = v + t • (u - v) := by abel
  have hl := hessian_support hf u v
    (m := 7 / 8 * ‖S (u - v)‖ ^ 2 - 8 * L * σ * ‖u - v‖ ^ 2)
    (fun t ht => by simpa only [hx] using (hh t ht).1)
  have hu' := hessian_upper hf u v (m := 9 / 8 * ‖S (u - v)‖ ^ 2)
    (fun t ht => by simpa only [hx] using (hh t ht).2)
  constructor <;> linarith

end LongTails.Proofs.GuardedMetricSupport
