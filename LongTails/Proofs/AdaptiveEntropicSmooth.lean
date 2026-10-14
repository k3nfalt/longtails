import LongTails.Proofs.AdaptiveEntropicGeometry
import LongTails.Proofs.GdConvex
import LongTails.Proofs.SmoothConvexConcaveGap

open Set InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma simplex_segment {d : ℕ} (x y : simplex d) {t : ℝ} (ht : t ∈ Icc 0 1) :
    x.val + t • (y.val - x.val) ∈ simplex d := by
  have he : x.val + t • (y.val - x.val) = (1 - t) • x.val + t • y.val := by module
  rw [he]
  constructor
  · intro i
    change 0 ≤ (1 - t) * x.val i + t * y.val i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (x.property.1 i))
      (mul_nonneg ht.1 (y.property.1 i))
  · change (∑ i, ((1 - t) * x.val i + t * y.val i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      x.property.2, y.property.2]
    ring

lemma simplex_smooth_upper {d : ℕ} {f : Vector d → ℝ} {L : ℝ}
    (hg : ∀ x ∈ simplex d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex d, ∀ y ∈ simplex d,
      dualNorm (gradient f x - gradient f y) ≤ L * oneNorm (x - y))
    (x y : simplex d) :
    f y ≤ f x + ⟪gradient f x, y.val - x.val⟫ +
      L / 2 * oneNorm (y.val - x.val) ^ 2 := by
  let v := y.val - x.val
  let F := fun t : ℝ => f (x.val + t • v)
  let F' := fun t : ℝ => ⟪gradient f (x.val + t • v), v⟫
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) : x.val + t • v ∈ simplex d :=
    simplex_segment x y ht
  have hF (t : ℝ) (ht : t ∈ Icc 0 1) : HasDerivAt F (F' t) t := by
    have h := (hg _ (hmem t ht)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const v |>.const_add x.val)
    simpa only [F, F', Function.comp_def, id_eq, one_smul, toDual_apply_apply] using h
  let B := fun t : ℝ => f x + t * ⟪gradient f x, v⟫ +
    t ^ 2 * (L / 2 * oneNorm v ^ 2)
  have hB (t : ℝ) : HasDerivAt B (⟪gradient f x, v⟫ + L * oneNorm v ^ 2 * t) t := by
    convert ((hasDerivAt_id t).mul_const ⟪gradient f x, v⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * oneNorm v ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1,
      F' t ≤ ⟪gradient f x, v⟫ + L * oneNorm v ^ 2 * t := by
    intro t ht
    have hp := (le_abs_self ⟪gradient f (x.val + t • v) - gradient f x, v⟫).trans
      (abs_inner_le_dual_one (gradient f (x.val + t • v) - gradient f x) v)
    have hs := mul_le_mul_of_nonneg_right
      (hlip _ (hmem t ⟨ht.1, ht.2.le⟩) _ x.property) (oneNorm_nonneg v)
    simp only [add_sub_cancel_left, oneNorm_smul, abs_of_nonneg ht.1] at hs
    rw [inner_sub_left] at hp
    dsimp [F']
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hF t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, v] using h

lemma accelerated_coupling {d : ℕ} {f : Vector d → ℝ} {L α : ℝ}
    (hc : ConvexOn ℝ (simplex d) f)
    (hg : ∀ x ∈ simplex d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex d, ∀ y ∈ simplex d,
      dualNorm (gradient f x - gradient f y) ≤ L * oneNorm (x - y))
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (x y z z' y' xstar : simplex d)
    (hx : x.val = (1 - α) • y.val + α • z.val)
    (hy : y'.val = (1 - α) • y.val + α • z'.val) :
    f y' - f xstar ≤ (1 - α) * (f y - f xstar) +
      α * ⟪gradient f x, z'.val - xstar.val⟫ +
      L / 2 * α ^ 2 * oneNorm (z'.val - z.val) ^ 2 := by
  have hsy := SaddlePoint.convex_support_on hc x.property y.property (hg _ x.property)
  have hsx := SaddlePoint.convex_support_on hc x.property xstar.property (hg _ x.property)
  have hby := mul_le_mul_of_nonneg_left hsy (sub_nonneg.mpr hα1)
  have hbx := mul_le_mul_of_nonneg_left hsx hα
  have hsm := simplex_smooth_upper hg hlip x y'
  have hd : y'.val - x.val = α • (z'.val - z.val) := by
    rw [hx, hy]
    module
  have hi := congrArg (fun v => ⟪gradient f x, v⟫) hx
  simp only [inner_add_right, real_inner_smul_right] at hi
  rw [hd, real_inner_smul_right, oneNorm_smul, abs_of_nonneg hα] at hsm
  simp only [inner_sub_right] at hby hbx hsm ⊢
  nlinarith

lemma accelerated_weighted_step {d : ℕ} {f : Vector d → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hc : ConvexOn ℝ (simplex d) f)
    (hg : ∀ x ∈ simplex d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex d, ∀ y ∈ simplex d,
      dualNorm (gradient f x - gradient f y) ≤ L * oneNorm (x - y))
    (n : ℕ) (y z z' xstar : simplex d) :
    ((n : ℝ) + 1) * (n + 2) / 2 * (f (mix n y z') - f xstar) -
      (n : ℝ) * (n + 1) / 2 * (f y - f xstar) ≤
      ((n : ℝ) + 1) * ⟪gradient f (mix n y z), z'.val - xstar.val⟫ +
        L * oneNorm (z'.val - z.val) ^ 2 := by
  have hn : (0 : ℝ) < n + 2 := by positivity
  have ha : (0 : ℝ) ≤ 2 / (n + 2) := by positivity
  have ha1 : (2 : ℝ) / (n + 2) ≤ 1 := by
    apply (div_le_one hn).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h := accelerated_coupling hc hg hlip ha ha1
    (mix n y z) y z z' (mix n y z') xstar rfl rfl
  have hw : (0 : ℝ) ≤ (n + 1) * (n + 2) / 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left h hw
  have he₁ : ((n : ℝ) + 1) * (n + 2) / 2 * (1 - 2 / (n + 2)) =
      n * (n + 1) / 2 := by field_simp; ring
  have he₂ : ((n : ℝ) + 1) * (n + 2) / 2 * (2 / (n + 2)) = n + 1 := by
    field_simp
  have he₃ : ((n : ℝ) + 1) * (n + 2) / 2 * (L / 2 * (2 / (n + 2)) ^ 2) =
      L * (n + 1) / (n + 2) := by field_simp
  have hratio : ((n : ℝ) + 1) / (n + 2) ≤ 1 := by
    apply (div_le_one hn).mpr
    linarith
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio hL) (sq_nonneg (oneNorm (z'.val - z.val)))
  have he : ((n : ℝ) + 1) * (n + 2) / 2 *
      ((1 - 2 / (n + 2)) * (f y - f xstar) +
        (2 / (n + 2)) * ⟪gradient f (mix n y z), z'.val - xstar.val⟫ +
        L / 2 * (2 / (n + 2)) ^ 2 * oneNorm (z'.val - z.val) ^ 2) =
      n * (n + 1) / 2 * (f y - f xstar) +
        (n + 1) * ⟪gradient f (mix n y z), z'.val - xstar.val⟫ +
        L * (n + 1) / (n + 2) * oneNorm (z'.val - z.val) ^ 2 := by
    calc
      _ = (((n : ℝ) + 1) * (n + 2) / 2 * (1 - 2 / (n + 2))) * (f y - f xstar) +
          (((n : ℝ) + 1) * (n + 2) / 2 * (2 / (n + 2))) *
            ⟪gradient f (mix n y z), z'.val - xstar.val⟫ +
          (((n : ℝ) + 1) * (n + 2) / 2 * (L / 2 * (2 / (n + 2)) ^ 2)) *
            oneNorm (z'.val - z.val) ^ 2 := by ring
      _ = _ := by rw [he₁, he₂, he₃]
  rw [he] at hm
  have hb' : L * ((n : ℝ) + 1) / (n + 2) * oneNorm (z'.val - z.val) ^ 2 ≤
      L * oneNorm (z'.val - z.val) ^ 2 := by
    simpa only [mul_div_assoc, mul_one] using hb
  linarith

lemma measurable_restricted_gradient {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.SFinite P]
    {g : simplex d → Ω → Vector d} (hg : Measurable (Function.uncurry g))
    {f : Vector d → ℝ}
    (hgu : ∀ x : simplex d, (∫ ω, g x ω ∂P) = gradient f x) :
    Measurable (fun x : simplex d => gradient f x) := by
  have hm : Measurable (fun x : simplex d => ∫ ω, g x ω ∂P) :=
    hg.stronglyMeasurable.integral_prod_right.measurable
  have he : (fun x : simplex d => ∫ ω, g x ω ∂P) = (fun x : simplex d => gradient f x) :=
    funext hgu
  rw [he] at hm
  exact hm

lemma measurable_restricted_objective {d : ℕ} {f : Vector d → ℝ}
    (hgrad : ∀ x ∈ simplex d, HasGradientAt f (gradient f x) x) :
    Measurable (fun x : simplex d => f x) := by
  have hc : ContinuousOn f (simplex d) :=
    fun x hx => (hgrad x hx).continuousAt.continuousWithinAt
  exact hc.domRestrict.measurable

end OracleTemplate.AdaptiveHeavyTailSimplex
