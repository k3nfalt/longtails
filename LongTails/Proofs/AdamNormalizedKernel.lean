import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.AdamNormalizedKernel

noncomputable def kernel (a γ ε s : ℝ) : ℝ := s / (Real.sqrt (a + γ * s ^ 2) + ε)

noncomputable def slope (a γ ε s : ℝ) : ℝ :=
  (a / Real.sqrt (a + γ * s ^ 2) + ε) / (Real.sqrt (a + γ * s ^ 2) + ε) ^ 2

noncomputable def curvature (a γ ε s : ℝ) : ℝ :=
  -(a * γ * s / (Real.sqrt (a + γ * s ^ 2) ^ 3 *
    (Real.sqrt (a + γ * s ^ 2) + ε) ^ 2)) -
    2 * (a / Real.sqrt (a + γ * s ^ 2) + ε) * γ * s /
      (Real.sqrt (a + γ * s ^ 2) * (Real.sqrt (a + γ * s ^ 2) + ε) ^ 3)

lemma hasDerivAt_kernel {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (s : ℝ) :
    HasDerivAt (kernel a γ ε) (slope a γ ε s) s := by
  have hp : 0 < a + γ * s ^ 2 := by positivity
  have hr : 0 < Real.sqrt (a + γ * s ^ 2) := Real.sqrt_pos.2 hp
  have hd : Real.sqrt (a + γ * s ^ 2) + ε ≠ 0 := by positivity
  have hsq := Real.sq_sqrt hp.le
  have hs := (((hasDerivAt_id s).pow 2).const_mul γ).const_add a
  have ht := ((hs.sqrt hp.ne').add_const ε)
  convert (hasDerivAt_id s).div ht hd using 1
  · rfl
  · dsimp [slope]
    field_simp
    nlinarith

lemma hasDerivAt_slope {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (s : ℝ) :
    HasDerivAt (slope a γ ε) (curvature a γ ε s) s := by
  have hp : 0 < a + γ * s ^ 2 := by positivity
  have hr : Real.sqrt (a + γ * s ^ 2) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hd : Real.sqrt (a + γ * s ^ 2) + ε ≠ 0 := by positivity
  have hs := ((((hasDerivAt_id s).pow 2).const_mul γ).const_add a).sqrt hp.ne'
  have hn := ((hasDerivAt_const s a).div hs hr).add_const ε
  have ht := (hs.add_const ε).pow 2
  convert hn.div ht (pow_ne_zero 2 hd) using 1
  · rfl
  · dsimp [curvature]
    field_simp
    ring

lemma abs_curvature_le {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (s : ℝ) :
    |curvature a γ ε s| ≤ 3 * Real.sqrt γ / a := by
  let r := Real.sqrt (a + γ * s ^ 2)
  let d := r + ε
  let τ := Real.sqrt γ
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hd : 0 < d := by dsimp [d]; positivity
  have hτ : 0 ≤ τ := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = a + γ * s ^ 2 := Real.sq_sqrt (by positivity)
  have hτ2 : τ ^ 2 = γ := Real.sq_sqrt hγ
  have har : a ≤ r ^ 2 := by nlinarith
  have hrd : r ≤ d := by dsimp [d]; linarith
  have had : a ≤ d ^ 2 := by nlinarith
  have hg : |γ * s| ≤ τ * r := by
    have habs : |γ * s| ^ 2 = γ ^ 2 * s ^ 2 := by rw [sq_abs]; ring
    have hprod : 0 ≤ γ * a := mul_nonneg hγ ha.le
    have hsquare : |γ * s| ^ 2 ≤ (τ * r) ^ 2 := by
      rw [mul_pow, hτ2, hr2, habs]
      nlinarith
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hτ hr.le)).1 hsquare
  have h1 : a / r ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hr)).2 har
  have h2 : |γ * s| / r ≤ τ := (div_le_iff₀ hr).2 hg
  have h3 : 1 / d ^ 2 ≤ 1 / a := one_div_le_one_div_of_le ha had
  have h4 : (a / r + ε) / d ≤ 1 := by
    apply (div_le_one hd).2
    have : a / r ≤ r := (div_le_iff₀ hr).2 (by nlinarith)
    dsimp [d]
    linarith
  have hn : 0 ≤ a / r + ε := by positivity
  have he1 : |a * γ * s / (r ^ 3 * d ^ 2)| =
      (a / r ^ 2) * (|γ * s| / r) * (1 / d ^ 2) := by
    rw [abs_div, show a * γ * s = a * (γ * s) by ring, abs_mul, abs_of_pos ha,
      abs_of_pos (by positivity : 0 < r ^ 3 * d ^ 2)]
    field_simp
  have he2 : |2 * (a / r + ε) * γ * s / (r * d ^ 3)| =
      2 * ((a / r + ε) / d) * (|γ * s| / r) * (1 / d ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < r * d ^ 3),
      show 2 * (a / r + ε) * γ * s = (2 * (a / r + ε)) * (γ * s) by ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (a / r + ε))]
    field_simp
  have hb1 : |a * γ * s / (r ^ 3 * d ^ 2)| ≤ τ / a := by
    rw [he1]
    calc (a / r ^ 2) * (|γ * s| / r) * (1 / d ^ 2)
        ≤ 1 * τ * (1 / a) := by gcongr
      _ = τ / a := by ring
  have hb2 : |2 * (a / r + ε) * γ * s / (r * d ^ 3)| ≤ 2 * τ / a := by
    rw [he2]
    calc 2 * ((a / r + ε) / d) * (|γ * s| / r) * (1 / d ^ 2)
        ≤ 2 * 1 * τ * (1 / a) := by gcongr
      _ = 2 * τ / a := by ring
  change |-(a * γ * s / (r ^ 3 * d ^ 2)) -
    2 * (a / r + ε) * γ * s / (r * d ^ 3)| ≤ 3 * τ / a
  have ht := abs_sub (-(a * γ * s / (r ^ 3 * d ^ 2)))
    (2 * (a / r + ε) * γ * s / (r * d ^ 3))
  rw [abs_neg] at ht
  calc _ ≤ _ := ht
    _ ≤ τ / a + 2 * τ / a := add_le_add hb1 hb2
    _ = 3 * τ / a := by ring

lemma abs_slope_le {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (s : ℝ) :
    |slope a γ ε s| ≤ 1 / Real.sqrt a := by
  let r := Real.sqrt (a + γ * s ^ 2)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hra : Real.sqrt a ≤ r := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])
  have hd : 0 < r + ε := by positivity
  have hsq : r ^ 2 = a + γ * s ^ 2 := Real.sq_sqrt (by positivity)
  have har : a / r ≤ r := (div_le_iff₀ hr).2 (by nlinarith [sq_nonneg s])
  change |(a / r + ε) / (r + ε) ^ 2| ≤ _
  rw [abs_of_nonneg (by positivity)]
  calc (a / r + ε) / (r + ε) ^ 2 ≤ (r + ε) / (r + ε) ^ 2 := by gcongr
    _ = 1 / (r + ε) := by field_simp
    _ ≤ 1 / Real.sqrt a := one_div_le_one_div_of_le (Real.sqrt_pos.2 ha) (by linarith)

lemma kernel_sub_le {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (s t : ℝ) :
    |kernel a γ ε s - kernel a γ ε t| ≤ (1 / Real.sqrt a) * |s - t| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (f := kernel a γ ε) (f' := slope a γ ε)
      (fun x _ => (hasDerivAt_kernel ha hγ hε x).hasDerivWithinAt)
      (fun x _ => by simpa only [Real.norm_eq_abs] using abs_slope_le ha hγ hε x)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ t) (Set.mem_univ s)

lemma slope_sub_le {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (s t : ℝ) :
    |slope a γ ε s - slope a γ ε t| ≤ (3 * Real.sqrt γ / a) * |s - t| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (f := slope a γ ε) (f' := curvature a γ ε)
      (fun x _ => (hasDerivAt_slope ha hγ hε x).hasDerivWithinAt)
      (fun x _ => by simpa only [Real.norm_eq_abs] using abs_curvature_le ha hγ hε x)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ t) (Set.mem_univ s)

lemma kernel_remainder_le {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (s t : ℝ) :
    |kernel a γ ε s - kernel a γ ε t - slope a γ ε t * (s - t)| ≤
      (3 * Real.sqrt γ / a) * (s - t) ^ 2 := by
  let f : ℝ → ℝ := fun x => kernel a γ ε x - slope a γ ε t * (x - t)
  have hf (x : ℝ) : HasDerivAt f (slope a γ ε x - slope a γ ε t) x := by
    convert (hasDerivAt_kernel ha hγ hε x).sub
      (((hasDerivAt_id x).sub_const t).const_mul (slope a γ ε t)) using 1 <;> simp [f]
    rfl
  have hb (x : ℝ) (hx : x ∈ Set.uIcc t s) :
      ‖slope a γ ε x - slope a γ ε t‖ ≤ (3 * Real.sqrt γ / a) * |s - t| := by
    rw [Real.norm_eq_abs]
    exact (slope_sub_le ha hγ hε x t).trans
      (mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hx) (by positivity))
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ Set.uIcc t s) => (hf x).hasDerivWithinAt) hb
    (convex_uIcc t s) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  simp only [f, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at hm
  convert hm using 1
  · congr 1; ring
  · rw [mul_assoc, ← sq, sq_abs]

lemma abs_kernel_le {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 < γ) (hε : 0 ≤ ε) (s : ℝ) :
    |kernel a γ ε s| ≤ 1 / Real.sqrt γ := by
  have hp : 0 < a + γ * s ^ 2 := by positivity
  have hr : 0 < Real.sqrt (a + γ * s ^ 2) := Real.sqrt_pos.2 hp
  have ht : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  have hsq := Real.sq_sqrt hp.le
  have ht2 := Real.sq_sqrt hγ.le
  have hb : Real.sqrt γ * |s| ≤ Real.sqrt (a + γ * s ^ 2) := by
    have he : (Real.sqrt γ * |s|) ^ 2 = γ * s ^ 2 := by
      rw [mul_pow, ht2, sq_abs]
    nlinarith [sq_nonneg (Real.sqrt γ * |s| - Real.sqrt (a + γ * s ^ 2))]
  rw [kernel, abs_div, abs_of_pos (by positivity : 0 < Real.sqrt (a + γ * s ^ 2) + ε)]
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (a + γ * s ^ 2) + ε)).2
  have hh : |s| ≤ (Real.sqrt (a + γ * s ^ 2) + ε) / Real.sqrt γ :=
    (le_div_iff₀ ht).2 (by nlinarith)
  convert hh using 1; ring

open MeasureTheory

lemma integrable_kernel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → ℝ} (hg : Measurable g) (hi : Integrable g P)
    {a γ ε : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) :
    Integrable (fun ω => kernel a γ ε (g ω)) P := by
  have hc : Continuous (kernel a γ ε) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_kernel ha hγ hε x).continuousAt
  apply (hi.norm.const_mul (1 / Real.sqrt a)).mono'
    (hc.measurable.comp hg).aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Function.comp_apply, Real.norm_eq_abs, show kernel a γ ε 0 = 0 by simp [kernel],
    sub_zero] using kernel_sub_le ha hγ hε (g ω) 0

lemma integral_kernel_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : Ω → ℝ} (hg : Measurable g) (hi : Integrable g P)
    {a γ ε h : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hmean : (∫ ω, g ω ∂P) = h) (h2 : Integrable (fun ω => (g ω - h) ^ 2) P) :
    |(∫ ω, kernel a γ ε (g ω) ∂P) - kernel a γ ε h| ≤
      (3 * Real.sqrt γ / a) * ∫ ω, (g ω - h) ^ 2 ∂P := by
  have hk := integrable_kernel hg hi ha hγ hε
  have hlin : Integrable (fun ω => slope a γ ε h * (g ω - h)) P :=
    (hi.sub (integrable_const h)).const_mul (slope a γ ε h)
  have hbase : Integrable (fun ω => kernel a γ ε (g ω) - kernel a γ ε h) P :=
    hk.sub (integrable_const _)
  have he : (∫ ω, kernel a γ ε (g ω) - kernel a γ ε h -
      slope a γ ε h * (g ω - h) ∂P) =
      (∫ ω, kernel a γ ε (g ω) ∂P) - kernel a γ ε h := by
    rw [integral_sub hbase hlin, integral_sub hk (integrable_const _),
      integral_const_mul]
    have hmean' : (∫ ω, g ω - h ∂P) = 0 := by
      rw [integral_sub hi (integrable_const h)]
      simp [hmean]
    rw [hmean']
    simp
  have hb := norm_integral_le_of_norm_le
    (f := fun ω => kernel a γ ε (g ω) - kernel a γ ε h -
      slope a γ ε h * (g ω - h)) (h2.const_mul (3 * Real.sqrt γ / a))
    (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using kernel_remainder_le ha hγ hε (g ω) h)
  rw [he, Real.norm_eq_abs, integral_const_mul] at hb
  exact hb

end LongTails.Proofs.AdamNormalizedKernel
