import LongTails.Proofs.NcPlFlat
import LongTails.Proofs.AbcHardFunction
import LongTails.Proofs.MintyChainGeometry

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlCut

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlCalc
open LongTails.Proofs.NcPlChainPL
open LongTails.Proofs.MintyChainGeometry (ball ball_norm_le ball_lipschitz ball_of_le)

noncomputable def cut (v : ℝ) : ℝ := 1 - psi (v / 2)

noncomputable def dcut (v : ℝ) : ℝ := -(dpsi (v / 2) / 2)

lemma cut_hasDerivAt (v : ℝ) : HasDerivAt cut (dcut v) v := by
  have h : HasDerivAt (psi ∘ fun x : ℝ => x / 2) (dpsi (v / 2) * (1 / 2)) v :=
    HasDerivAt.comp v (psi_hasDerivAt (v / 2)) ((hasDerivAt_id' v).div_const 2)
  have h2 : HasDerivAt (fun x : ℝ => 1 - (psi ∘ fun x : ℝ => x / 2) x)
      (-(dpsi (v / 2) * (1 / 2))) v := h.const_sub 1
  have e : -(dpsi (v / 2) * (1 / 2)) = dcut v := by
    unfold dcut
    ring
  rw [e] at h2
  exact h2

lemma cut_nonneg (v : ℝ) : 0 ≤ cut v := by
  unfold cut
  linarith [psi_le_one (v / 2)]

lemma cut_le_one (v : ℝ) : cut v ≤ 1 := by
  unfold cut
  linarith [psi_nonneg (v / 2)]

lemma cut_of_le {v : ℝ} (h : v ≤ 1) : cut v = 1 := by
  unfold cut
  rw [psi_of_le (by linarith), sub_zero]

lemma cut_of_ge {v : ℝ} (h : 2 ≤ v) : cut v = 0 := by
  unfold cut
  rw [psi_of_ge (by linarith), sub_self]

lemma dcut_of_le {v : ℝ} (h : v ≤ 1) : dcut v = 0 := by
  unfold dcut
  rw [dpsi_of_le (by linarith)]
  norm_num

lemma dcut_of_ge {v : ℝ} (h : 2 ≤ v) : dcut v = 0 := by
  unfold dcut
  rw [dpsi_of_ge (by linarith)]
  norm_num

lemma dcut_nonpos (v : ℝ) : dcut v ≤ 0 := by
  unfold dcut
  linarith [dpsi_nonneg (v / 2)]

lemma dcut_abs (v : ℝ) : |dcut v| ≤ 2 := by
  unfold dcut
  rw [abs_neg, abs_of_nonneg (by linarith [dpsi_nonneg (v / 2)])]
  linarith [dpsi_le (v / 2)]

lemma cut_lip (a b : ℝ) : |cut a - cut b| ≤ 2 * |a - b| := by
  have h := psi_lipschitz (a / 2) (b / 2)
  have e : cut a - cut b = -(psi (a / 2) - psi (b / 2)) := by
    unfold cut
    ring
  have e2 : a / 2 - b / 2 = (a - b) / 2 := by ring
  rw [e, abs_neg]
  rw [e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

lemma dcut_lip (a b : ℝ) : |dcut a - dcut b| ≤ 16 * |a - b| := by
  have h := dpsi_lipschitz (a / 2) (b / 2)
  have e : dcut a - dcut b = -((dpsi (a / 2) - dpsi (b / 2)) / 2) := by
    unfold dcut
    ring
  have e2 : a / 2 - b / 2 = (a - b) / 2 := by ring
  rw [e, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def cutv (B : ℝ) (x : E) : ℝ := cut (‖x‖ ^ 2 / B ^ 2)

noncomputable def cutGrad (B : ℝ) (x : E) : E := (dcut (‖x‖ ^ 2 / B ^ 2) * (2 / B ^ 2)) • x

omit [InnerProductSpace ℝ E] in
lemma cutv_nonneg (B : ℝ) (x : E) : 0 ≤ cutv B x := cut_nonneg _

omit [InnerProductSpace ℝ E] in
lemma cutv_le_one (B : ℝ) (x : E) : cutv B x ≤ 1 := cut_le_one _

omit [InnerProductSpace ℝ E] in
lemma cutv_abs (B : ℝ) (x : E) : |cutv B x| ≤ 1 := by
  rw [abs_of_nonneg (cutv_nonneg B x)]
  exact cutv_le_one B x

omit [InnerProductSpace ℝ E] in
lemma ratio_le_one {B : ℝ} (hB : 0 < B) {x : E} (h : ‖x‖ ≤ B) : ‖x‖ ^ 2 / B ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg x) h 2

omit [InnerProductSpace ℝ E] in
lemma two_le_ratio {B : ℝ} (hB : 0 < B) {x : E} (h : 2 * B ≤ ‖x‖) : 2 ≤ ‖x‖ ^ 2 / B ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg x]

omit [InnerProductSpace ℝ E] in
lemma cutv_of_le {B : ℝ} (hB : 0 < B) {x : E} (h : ‖x‖ ≤ B) : cutv B x = 1 :=
  cut_of_le (ratio_le_one hB h)

lemma cutGrad_of_le {B : ℝ} (hB : 0 < B) {x : E} (h : ‖x‖ ≤ B) : cutGrad B x = 0 := by
  unfold cutGrad
  rw [dcut_of_le (ratio_le_one hB h), zero_mul, zero_smul]

omit [InnerProductSpace ℝ E] in
lemma cutv_of_ge {B : ℝ} (hB : 0 < B) {x : E} (h : 2 * B ≤ ‖x‖) : cutv B x = 0 :=
  cut_of_ge (two_le_ratio hB h)

lemma cutGrad_of_ge {B : ℝ} (hB : 0 < B) {x : E} (h : 2 * B ≤ ‖x‖) : cutGrad B x = 0 := by
  unfold cutGrad
  rw [dcut_of_ge (two_le_ratio hB h), zero_mul, zero_smul]

lemma cutv_hasGradientAt {B : ℝ} [CompleteSpace E] (x : E) :
    HasGradientAt (cutv B) (cutGrad B x) x := by
  have h0 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / B ^ 2)
  have h1 := (cut_hasDerivAt (1 / B ^ 2 * ‖x‖ ^ 2)).comp_hasFDerivAt x h0
  have e : ‖x‖ ^ 2 / B ^ 2 = 1 / B ^ 2 * ‖x‖ ^ 2 := by ring
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h1 using 1
  · funext y
    unfold cutv
    rw [Function.comp_apply]
    congr 1
    ring
  · ext v
    unfold cutGrad
    rw [e]
    simp only [InnerProductSpace.toDual_apply_apply, smul_apply, smul_eq_mul,
      innerSL_apply_apply, real_inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat]
    ring

lemma ball_norm_of_gt {B : ℝ} (hB : 0 ≤ B) {u : E} (h : B < ‖u‖) : ‖ball B u‖ = B := by
  unfold ball
  rw [ite_eq_right (not_le.mpr h)]
  have hu : 0 < ‖u‖ := lt_of_le_of_lt hB h
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hB, abs_norm, div_mul_cancel₀ _ hu.ne']

lemma cutv_ball {B : ℝ} (hB : 0 < B) (x : E) : cutv B (ball (2 * B) x) = cutv B x := by
  rcases le_or_gt ‖x‖ (2 * B) with h | h
  · rw [ball_of_le _ _ h]
  · rw [cutv_of_ge hB h.le,
      cutv_of_ge hB (le_of_eq (ball_norm_of_gt (by positivity) h).symm)]

lemma smul_cutGrad_ball {B : ℝ} (hB : 0 < B) (f : E → ℝ) (x : E) :
    f x • cutGrad B x = f (ball (2 * B) x) • cutGrad B x := by
  rcases le_or_gt ‖x‖ (2 * B) with h | h
  · rw [ball_of_le _ _ h]
  · rw [cutGrad_of_ge hB h.le, smul_zero, smul_zero]

lemma cutv_smul_ball {F : Type*} [AddCommGroup F] [Module ℝ F] {B : ℝ} (hB : 0 < B) (f : E → F)
    (x : E) : cutv B x • f x = cutv B x • f (ball (2 * B) x) := by
  rcases le_or_gt ‖x‖ (2 * B) with h | h
  · rw [ball_of_le _ _ h]
  · rw [cutv_of_ge hB h.le, zero_smul, zero_smul]

omit [InnerProductSpace ℝ E] in
lemma ratio_lip {B : ℝ} (hB : 0 < B) {x x' : E} (hx : ‖x‖ ≤ 2 * B) (hx' : ‖x'‖ ≤ 2 * B) :
    |‖x‖ ^ 2 / B ^ 2 - ‖x'‖ ^ 2 / B ^ 2| ≤ 4 / B * ‖x - x'‖ := by
  have h1 : |‖x‖ - ‖x'‖| ≤ ‖x - x'‖ := abs_norm_sub_norm_le x x'
  have h2 : 0 ≤ ‖x‖ + ‖x'‖ := by positivity
  have e : ‖x‖ ^ 2 / B ^ 2 - ‖x'‖ ^ 2 / B ^ 2 = (‖x‖ - ‖x'‖) * (‖x‖ + ‖x'‖) / B ^ 2 := by ring
  rw [e, abs_div, abs_mul, abs_of_nonneg h2, abs_of_pos (by positivity : (0 : ℝ) < B ^ 2),
    div_le_iff₀ (by positivity)]
  have h3 : |‖x‖ - ‖x'‖| * (‖x‖ + ‖x'‖) ≤ ‖x - x'‖ * (4 * B) :=
    mul_le_mul h1 (by linarith) h2 (norm_nonneg _)
  have e2 : 4 / B * ‖x - x'‖ * B ^ 2 = ‖x - x'‖ * (4 * B) := by
    field_simp
  rw [e2]
  exact h3

lemma cutv_lip {B : ℝ} (hB : 0 < B) (x x' : E) : |cutv B x - cutv B x'| ≤ 8 / B * ‖x - x'‖ := by
  rw [← cutv_ball hB x, ← cutv_ball hB x']
  have hb := ball_norm_le (2 * B) (by positivity) x
  have hb' := ball_norm_le (2 * B) (by positivity) x'
  have h1 := cut_lip (‖ball (2 * B) x‖ ^ 2 / B ^ 2) (‖ball (2 * B) x'‖ ^ 2 / B ^ 2)
  have h2 := ratio_lip hB hb hb'
  have h3 := ball_lipschitz (2 * B) (by positivity) x x'
  have h4 : 4 / B * ‖ball (2 * B) x - ball (2 * B) x'‖ ≤ 4 / B * ‖x - x'‖ :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have e : 8 / B * ‖x - x'‖ = 2 * (4 / B * ‖x - x'‖) := by ring
  rw [e]
  unfold cutv
  linarith

lemma cutGrad_norm_le {B : ℝ} (hB : 0 < B) (x : E) : ‖cutGrad B x‖ ≤ 8 / B := by
  rcases le_or_gt ‖x‖ (2 * B) with h | h
  · unfold cutGrad
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / B ^ 2)]
    have h1 := dcut_abs (‖x‖ ^ 2 / B ^ 2)
    have h2 : |dcut (‖x‖ ^ 2 / B ^ 2)| * (2 / B ^ 2) * ‖x‖ ≤ 2 * (2 / B ^ 2) * (2 * B) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h (norm_nonneg _) (by positivity)
    have e : 2 * (2 / B ^ 2) * (2 * B) = 8 / B := by
      field_simp
      ring
    linarith
  · rw [cutGrad_of_ge hB h.le, norm_zero]
    positivity

lemma norm_smul_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c c' : ℝ)
    (v v' : F) : ‖c • v - c' • v'‖ ≤ |c - c'| * ‖v‖ + |c'| * ‖v - v'‖ := by
  have e : c • v - c' • v' = (c - c') • v + c' • (v - v') := by
    rw [sub_smul, smul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

lemma cutGrad_ball {B : ℝ} (hB : 0 < B) (x : E) :
    cutGrad B x = (dcut (‖ball (2 * B) x‖ ^ 2 / B ^ 2) * (2 / B ^ 2)) • ball (2 * B) x := by
  rcases le_or_gt ‖x‖ (2 * B) with h | h
  · rw [ball_of_le _ _ h]
    rfl
  · have hn := ball_norm_of_gt (by positivity : (0 : ℝ) ≤ 2 * B) h
    have h2 : (2 : ℝ) ≤ (2 * B) ^ 2 / B ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    rw [cutGrad_of_ge hB h.le, hn, dcut_of_ge h2, zero_mul, zero_smul]

lemma cutGrad_lip {B : ℝ} (hB : 0 < B) (x x' : E) :
    ‖cutGrad B x - cutGrad B x'‖ ≤ 260 / B ^ 2 * ‖x - x'‖ := by
  rw [cutGrad_ball hB x, cutGrad_ball hB x']
  have hb := ball_norm_le (2 * B) (by positivity) x
  have hb' := ball_norm_le (2 * B) (by positivity) x'
  have h3 := ball_lipschitz (2 * B) (by positivity) x x'
  have hB2 : (0 : ℝ) < 2 / B ^ 2 := by positivity
  refine (norm_smul_sub_le _ _ _ _).trans ?_
  have hd := dcut_lip (‖ball (2 * B) x‖ ^ 2 / B ^ 2) (‖ball (2 * B) x'‖ ^ 2 / B ^ 2)
  have hr := ratio_lip hB hb hb'
  have hk : |dcut (‖ball (2 * B) x‖ ^ 2 / B ^ 2) * (2 / B ^ 2) -
      dcut (‖ball (2 * B) x'‖ ^ 2 / B ^ 2) * (2 / B ^ 2)| ≤
      16 * (4 / B * ‖x - x'‖) * (2 / B ^ 2) := by
    rw [← sub_mul, abs_mul, abs_of_pos hB2]
    apply mul_le_mul_of_nonneg_right _ hB2.le
    have : 4 / B * ‖ball (2 * B) x - ball (2 * B) x'‖ ≤ 4 / B * ‖x - x'‖ :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hk2 : |dcut (‖ball (2 * B) x'‖ ^ 2 / B ^ 2) * (2 / B ^ 2)| ≤ 2 * (2 / B ^ 2) := by
    rw [abs_mul, abs_of_pos hB2]
    exact mul_le_mul_of_nonneg_right (dcut_abs _) hB2.le
  have t1 := mul_le_mul hk hb (norm_nonneg _) (by positivity)
  have t2 := mul_le_mul hk2 h3 (norm_nonneg _) (by positivity)
  have e : 16 * (4 / B * ‖x - x'‖) * (2 / B ^ 2) * (2 * B) + 2 * (2 / B ^ 2) * ‖x - x'‖ =
      260 / B ^ 2 * ‖x - x'‖ := by
    field_simp
    ring
  linarith

end Radial

lemma norm_sq_toLp {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ k, f k ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

lemma norm_sub_sq_eq {ι : Type*} [Fintype ι] (a b : EuclideanSpace ℝ ι) :
    ‖a - b‖ ^ 2 = ∑ k, (a k - b k) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma inner_toLp {ι : Type*} [Fintype ι] (f : ι → ℝ) (v : EuclideanSpace ℝ ι) :
    ⟪(WithLp.toLp 2 f : EuclideanSpace ℝ ι), v⟫ = ∑ k, f k * v k := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma norm_le_of_sq_le {ι : Type*} [Fintype ι] (a : EuclideanSpace ℝ ι) {C : ℝ} (hC : 0 ≤ C)
    (h : ∑ k, a k ^ 2 ≤ C ^ 2) : ‖a‖ ≤ C := by
  rw [← EuclideanSpace.real_norm_sq_eq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero).mp h

lemma lipschitz_of_grad_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (g : E → E) (C : ℝ) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ x, ‖g x‖ ≤ C) (x y : E) : |f x - f y| ≤ C * ‖x - y‖ := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := f) (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt)
    (fun z _ => by
      rw [(InnerProductSpace.toDual ℝ E).norm_map]
      exact hg z) (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs] at h
  exact h

end LongTails.Proofs.NcPlCut
