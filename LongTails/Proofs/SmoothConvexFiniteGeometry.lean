import LongTails.Proofs.FiniteSumNondualLowerComponents
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology RealInnerProductSpace

namespace LongTails.Proofs.SmoothConvexFiniteGeometry

noncomputable def ramp (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then t ^ 2 / 2 else t - 1 / 2

def rampSlope (t : ℝ) : ℝ := min 1 (max 0 t)

lemma rampSlope_cases (x : ℝ) :
    rampSlope x = if x ≤ 0 then 0 else if x ≤ 1 then x else 1 := by
  simp only [rampSlope, min_def, max_def]
  split_ifs <;> linarith

lemma ramp_model (x y : ℝ) :
    0 ≤ ramp y - ramp x - rampSlope x * (y - x) ∧
      ramp y - ramp x - rampSlope x * (y - x) ≤ (y - x) ^ 2 / 2 := by
  simp only [ramp, rampSlope_cases]
  split_ifs <;> constructor <;>
    nlinarith [sq_nonneg (y - x), sq_nonneg (x - 1), sq_nonneg (y - 1),
      mul_self_nonneg x, mul_self_nonneg y]

lemma rampSlope_nonneg (x : ℝ) : 0 ≤ rampSlope x := by
  exact le_min (by norm_num) (le_max_left _ _)

lemma rampSlope_le_one (x : ℝ) : rampSlope x ≤ 1 := min_le_left _ _

lemma rampSlope_lipschitz (x y : ℝ) : |rampSlope x - rampSlope y| ≤ |x - y| := by
  simp only [rampSlope, min_def, max_def, abs]
  split_ifs <;> linarith

lemma ramp_hasDerivAt (x : ℝ) : HasDerivAt ramp (rampSlope x) x := by
  apply HasDerivAt.of_isLittleO
  have hb : (fun y => ramp y - ramp x - (y - x) • rampSlope x) =O[nhds x]
      (fun y => ‖y - x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with y
    have h := ramp_model x y
    simp only [Real.norm_eq_abs, smul_eq_mul, mul_comm (y - x),
      abs_of_nonneg h.1, sq_abs, abs_of_nonneg (sq_nonneg (y - x)), one_mul]
    nlinarith [sq_nonneg (y - x)]
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < 2))

noncomputable def smoothMax (w x y : ℝ) : ℝ := y + w * ramp ((x - y) / w + 1 / 2)

noncomputable def weight (w x y : ℝ) : ℝ := rampSlope ((x - y) / w + 1 / 2)

lemma weight_nonneg (w x y : ℝ) : 0 ≤ weight w x y := rampSlope_nonneg _

lemma weight_le_one (w x y : ℝ) : weight w x y ≤ 1 := rampSlope_le_one _

lemma smoothMax_eq_left (w x y : ℝ) (hw : 0 < w) (h : w / 2 ≤ x - y) :
    smoothMax w x y = x ∧ weight w x y = 1 := by
  have ht : 1 ≤ (x - y) / w + 1 / 2 := by
    have := (le_div_iff₀ hw).mpr (show (1 / 2 : ℝ) * w ≤ x - y by linarith)
    linarith
  have he : w * ((x - y) / w) = x - y := mul_div_cancel₀ _ hw.ne'
  simp only [smoothMax, weight, ramp, rampSlope, min_def, max_def]
  split_ifs <;> constructor <;> nlinarith

lemma smoothMax_eq_right (w x y : ℝ) (hw : 0 < w) (h : x - y ≤ -(w / 2)) :
    smoothMax w x y = y ∧ weight w x y = 0 := by
  have ht : (x - y) / w + 1 / 2 ≤ 0 := by
    have := (div_le_iff₀ hw).mpr (show x - y ≤ (-1 / 2 : ℝ) * w by linarith)
    linarith
  simp only [smoothMax, weight, ramp, ite_eq_left ht, rampSlope, max_eq_left ht]
  norm_num

lemma smoothMax_ge (w x y : ℝ) (hw : 0 < w) : max x y ≤ smoothMax w x y := by
  have he : w * ((x - y) / w) = x - y := mul_div_cancel₀ _ hw.ne'
  have hs := mul_nonneg hw.le (sq_nonneg ((x - y) / w + 1 / 2 - 1))
  have hs' := mul_nonneg hw.le (sq_nonneg ((x - y) / w + 1 / 2))
  simp only [smoothMax, ramp]
  split_ifs <;> apply max_le <;> nlinarith

lemma smoothMax_support (w x y x' y' : ℝ) (hw : 0 < w) :
    weight w x y * (x' - x) + (1 - weight w x y) * (y' - y) ≤
      smoothMax w x' y' - smoothMax w x y := by
  have h := mul_nonneg hw.le
    (ramp_model ((x - y) / w + 1 / 2) ((x' - y') / w + 1 / 2)).1
  have hx : w * ((x - y) / w) = x - y := mul_div_cancel₀ _ hw.ne'
  have hy : w * ((x' - y') / w) = x' - y' := mul_div_cancel₀ _ hw.ne'
  have hd : w * ((x' - y') / w + 1 / 2 - ((x - y) / w + 1 / 2)) =
      x' - x - (y' - y) := by nlinarith only [hx, hy]
  rw [mul_sub, mul_sub, mul_left_comm w (rampSlope _), hd] at h
  dsimp [smoothMax, weight]
  linarith

lemma weight_lipschitz (w x y x' y' : ℝ) (hw : 0 < w) :
    |weight w x y - weight w x' y'| ≤ (|x - x'| + |y - y'|) / w := by
  have he : (x - y) / w + 1 / 2 - ((x' - y') / w + 1 / 2) =
      ((x - x') - (y - y')) / w := by ring
  have h := rampSlope_lipschitz ((x - y) / w + 1 / 2) ((x' - y') / w + 1 / 2)
  rw [he, abs_div, abs_of_pos hw] at h
  exact h.trans (div_le_div_of_nonneg_right (abs_sub _ _) hw.le)

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smoothMax_gradient (w : ℝ) (hw : 0 < w) (f g : E → ℝ) (x df dg : E)
    (hf : HasGradientAt f df x) (hg : HasGradientAt g dg x) :
    HasGradientAt (fun z => smoothMax w (f z) (g z))
      (weight w (f x) (g x) • df + (1 - weight w (f x) (g x)) • dg) x := by
  have hi : HasFDerivAt (fun z => (f z - g z) / w + 1 / 2)
      (w⁻¹ • (InnerProductSpace.toDual ℝ E df - InnerProductSpace.toDual ℝ E dg)) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((hf.hasFDerivAt.sub hg.hasFDerivAt).const_mul w⁻¹).add_const (1 / 2)
  have hr := (ramp_hasDerivAt ((f x - g x) / w + 1 / 2)).comp_hasFDerivAt x hi
  have hd := hg.hasFDerivAt.add (hr.const_mul w)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext v
    change ⟪weight w (f x) (g x) • df + (1 - weight w (f x) (g x)) • dg, v⟫ =
      ⟪dg, v⟫ + w * (rampSlope ((f x - g x) / w + 1 / 2) *
        (w⁻¹ * (⟪df, v⟫ - ⟪dg, v⟫)))
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    dsimp only [weight]
    field_simp
    ring

omit [CompleteSpace E] in
lemma smoothMax_convex (w : ℝ) (hw : 0 < w) (f g : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g) :
    ConvexOn ℝ Set.univ (fun x => smoothMax w (f x) (g x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  let t := weight w (f z) (g z)
  have ht : 0 ≤ t := weight_nonneg _ _ _
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr (weight_le_one _ _ _)
  have hf' := hf.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hg' := hg.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hx := smoothMax_support w (f z) (g z) (f x) (g x) hw
  have hy := smoothMax_support w (f z) (g z) (f y) (g y) hw
  change smoothMax w (f z) (g z) ≤ a * smoothMax w (f x) (g x) +
    b * smoothMax w (f y) (g y)
  change t * (f x - f z) + (1 - t) * (g x - g z) ≤ _ at hx
  change t * (f y - f z) + (1 - t) * (g y - g z) ≤ _ at hy
  change f z ≤ a * f x + b * f y at hf'
  change g z ≤ a * g x + b * g y at hg'
  have hz := congrArg (fun s => s * smoothMax w (f z) (g z)) hab
  have hzf := congrArg (fun s => s * f z) hab
  have hzg := congrArg (fun s => s * g z) hab
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hb (sub_nonneg.mpr hy),
    mul_nonneg ht (sub_nonneg.mpr hf'), mul_nonneg ht' (sub_nonneg.mpr hg')]

omit [CompleteSpace E] in
lemma blend_difference (a b a' b' : E) (t s : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ‖(t • a + (1 - t) • b) - (s • a' + (1 - s) • b')‖ ≤
      t * ‖a - a'‖ + (1 - t) * ‖b - b'‖ + |t - s| * ‖a' - b'‖ := by
  have he : (t • a + (1 - t) • b) - (s • a' + (1 - s) • b') =
      (t • (a - a') + (1 - t) • (b - b')) + (t - s) • (a' - b') := by module
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    abs_of_nonneg (sub_nonneg.mpr ht')]
  exact le_rfl

omit [CompleteSpace E] in
lemma smoothMax_field_lipschitz (w M C : ℝ) (hw : 0 < w) (hM : 0 ≤ M)
    (f g : E → ℝ) (df dg : E → E) (x y : E)
    (hf : ‖df x - df y‖ ≤ C * ‖x - y‖)
    (hg : ‖dg x - dg y‖ ≤ C * ‖x - y‖)
    (hv : |f x - f y| + |g x - g y| ≤ M * ‖x - y‖)
    (hn : ‖df y‖ + ‖dg y‖ ≤ M) :
    ‖(weight w (f x) (g x) • df x + (1 - weight w (f x) (g x)) • dg x) -
      (weight w (f y) (g y) • df y + (1 - weight w (f y) (g y)) • dg y)‖ ≤
      (C + M ^ 2 / w) * ‖x - y‖ := by
  let t := weight w (f x) (g x)
  let s := weight w (f y) (g y)
  have ht : 0 ≤ t := weight_nonneg _ _ _
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr (weight_le_one _ _ _)
  have hdiff : |t - s| ≤ M * ‖x - y‖ / w :=
    (weight_lipschitz w (f x) (g x) (f y) (g y) hw).trans
      (div_le_div_of_nonneg_right hv hw.le)
  have hnorm : ‖df y - dg y‖ ≤ M := (norm_sub_le _ _).trans hn
  have h := blend_difference (df x) (dg x) (df y) (dg y) t s ht
    (weight_le_one _ _ _)
  have h₁ := mul_le_mul_of_nonneg_left hf ht
  have h₂ := mul_le_mul_of_nonneg_left hg ht'
  have h₃ := mul_le_mul hdiff hnorm (norm_nonneg _) (by positivity : 0 ≤ M * ‖x - y‖ / w)
  change _ ≤ (C + M ^ 2 / w) * ‖x - y‖
  calc
    _ ≤ t * ‖df x - df y‖ + (1 - t) * ‖dg x - dg y‖ + |t - s| * ‖df y - dg y‖ := h
    _ ≤ t * (C * ‖x - y‖) + (1 - t) * (C * ‖x - y‖) + (M * ‖x - y‖ / w) * M :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

end InnerProduct

end LongTails.Proofs.SmoothConvexFiniteGeometry
