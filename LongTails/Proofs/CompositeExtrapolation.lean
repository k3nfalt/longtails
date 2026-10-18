import Mathlib.Analysis.Convex.Function
import LongTails.Proofs.CurvatureMetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

namespace LongTails.Proofs.CompositeExtrapolation

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma extrapolation_lower {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (y v : E) {c : ℝ} (hc : 1 ≤ c) :
    c * f v - (c - 1) * f y ≤ f (y + c • (v - y)) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hi : 0 ≤ 1 - c⁻¹ := by
    have : c⁻¹ ≤ 1 := (inv_le_one₀ hcpos).mpr hc
    linarith
  have hid : c⁻¹ • (y + c • (v - y)) + (1 - c⁻¹) • y = v := by
    calc
      _ = (c⁻¹ * c) • v + (1 - c⁻¹ * c) • y := by module
      _ = v := by rw [inv_mul_cancel₀ hcpos.ne']; simp
  have h := hf.2 (mem_univ (y + c • (v - y))) (mem_univ y)
    (inv_nonneg.mpr hcpos.le) hi (by ring : c⁻¹ + (1 - c⁻¹) = 1)
  rw [hid] at h
  simp only [smul_eq_mul] at h
  have hm := mul_le_mul_of_nonneg_left h hcpos.le
  have he : c * (c⁻¹ * f (y + c • (v - y)) + (1 - c⁻¹) * f y) =
      f (y + c • (v - y)) + (c - 1) * f y := by
    field_simp
  rw [he] at hm
  linarith

lemma weighted_lower {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, 1 ≤ c i)
    {f ψ : E → ℝ} (hf : ConvexOn ℝ univ f) (y v : E) :
    (∑ i ∈ s, w i * c i) * (f v + ψ v) -
        ((∑ i ∈ s, w i * c i) - ∑ i ∈ s, w i) * f y ≤
      (∑ i ∈ s, w i * f (y + c i • (v - y))) +
        (∑ i ∈ s, w i * c i) * ψ v := by
  have h := Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (extrapolation_lower hf y v (hc i hi)) (hw i hi)
  have he : (∑ i ∈ s, w i * (c i * f v - (c i - 1) * f y)) =
      (∑ i ∈ s, w i * c i) * f v -
        ((∑ i ∈ s, w i * c i) - ∑ i ∈ s, w i) * f y := by
    simp only [sub_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at h
  linarith

lemma segment_upper {f : E → ℝ} {C : Set E} (hf : ConvexOn ℝ C f)
    {y x : E} (hy : y ∈ C) (hx : x ∈ C) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    f (y + t • (x - y)) ≤ (1 - t) * f y + t * f x := by
  have he : y + t • (x - y) = (1 - t) • y + t • x := by module
  simpa only [he, smul_eq_mul] using
    hf.2 hy hx (sub_nonneg.mpr ht1) ht (by ring : 1 - t + t = 1)

lemma weighted_comparator {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {M : ℝ} (hM : 1 ≤ M)
    (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ M)
    {f ψ : E → ℝ} {C : Set E} (hf : ConvexOn ℝ univ f)
    (hψ : ConvexOn ℝ C ψ) {y x : E} (hy : y ∈ C) (hx : x ∈ C)
    (hfx : f x = 0) (hψx : ψ x = 0) :
    (∑ i ∈ s, w i * f (y + c i • ((y + M⁻¹ • (x - y)) - y))) +
        (∑ i ∈ s, w i * c i) * ψ (y + M⁻¹ • (x - y)) +
        ((∑ i ∈ s, w i * c i) - ∑ i ∈ s, w i) * f y ≤
      (∑ i ∈ s, w i * c i) * (1 - M⁻¹) * (f y + ψ y) := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hMi : 0 ≤ M⁻¹ := inv_nonneg.mpr hMp.le
  have hMi1 : M⁻¹ ≤ 1 := (inv_le_one₀ hMp).mpr hM
  have ha : 0 ≤ ∑ i ∈ s, w i * c i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hc i hi).1
  have hp := segment_upper hψ hy hx hMi hMi1
  rw [hψx, mul_zero, add_zero] at hp
  have hp' := mul_le_mul_of_nonneg_left hp ha
  have hs := Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left
      (segment_upper hf (mem_univ y) (mem_univ x)
        (mul_nonneg (hc i hi).1 hMi)
        (show c i * M⁻¹ ≤ 1 by
          calc
            c i * M⁻¹ ≤ M * M⁻¹ := mul_le_mul_of_nonneg_right (hc i hi).2 hMi
            _ = 1 := mul_inv_cancel₀ hMp.ne')) (hw i hi)
  simp only [hfx, mul_zero, add_zero] at hs
  have he (i : ι) : y + c i • ((y + M⁻¹ • (x - y)) - y) =
      y + (c i * M⁻¹) • (x - y) := by module
  simp only [he]
  have ht : (∑ i ∈ s, w i * ((1 - c i * M⁻¹) * f y)) =
      ((∑ i ∈ s, w i) - (∑ i ∈ s, w i * c i) * M⁻¹) * f y := by
    simp only [sub_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [ht] at hs
  nlinarith

lemma shifted_contraction {a Δ F G Gbar shift : ℝ} (ha : 0 < a)
    (hlower : a * F - shift ≤ G)
    (hcompare : Gbar + shift ≤ 2 * a * Δ / 3)
    (haccuracy : G - Gbar ≤ a * Δ / 12) : F ≤ 3 * Δ / 4 := by
  apply (mul_le_mul_iff_right₀ ha).mp
  linarith

lemma nonnegative_summand_bound {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, 0 ≤ f i)
    {a χ D : ℝ} (ha : 0 ≤ a) (hχ : 0 ≤ χ)
    (hlevel : (∑ i ∈ s, w i * f i) + a * χ ≤ D) {i : ι} (hi : i ∈ s) :
    w i * f i ≤ D := by
  have hsingle := Finset.single_le_sum (fun j hj => mul_nonneg (hw j hj) (hf j hj)) hi
  have hp := mul_nonneg ha hχ
  linarith

lemma snapshot_bound {W a φ χ Δ : ℝ} (hWa : W ≤ a) (hφ : 0 ≤ φ)
    (ha : 0 ≤ a) (hgap : φ + χ ≤ Δ) : W * φ + a * χ ≤ a * Δ := by
  have h₁ := mul_le_mul_of_nonneg_right hWa hφ
  have h₂ := mul_le_mul_of_nonneg_left hgap ha
  nlinarith only [h₁, h₂]

lemma extrapolated_contraction {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, 1 ≤ c i)
    {M : ℝ} (hM : 1 ≤ M) (hM3 : M ≤ 3) (hcM : ∀ i ∈ s, c i ≤ M)
    {f ψ : E → ℝ} {C : Set E} (hf : ConvexOn ℝ univ f) (hψ : ConvexOn ℝ C ψ)
    {y x v : E} (hy : y ∈ C) (hx : x ∈ C) (hfx : f x = 0) (hψx : ψ x = 0)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hgap : f y + ψ y ≤ Δ)
    (ha : 0 < ∑ i ∈ s, w i * c i) :
    let a := ∑ i ∈ s, w i * c i
    let G := fun u => (∑ i ∈ s, w i * f (y + c i • (u - y))) + a * ψ u
    G v - G (y + M⁻¹ • (x - y)) ≤ a * Δ / 12 → f v + ψ v ≤ 3 * Δ / 4 := by
  dsimp only
  intro haccuracy
  have hlower := weighted_lower s w c hw hc (ψ := ψ) hf y v
  have hcompare := weighted_comparator s w c hw hM
    (fun i hi => ⟨(hc i hi).trans' zero_le_one, hcM i hi⟩) hf hψ hy hx hfx hψx
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hcoef : 0 ≤ 1 - M⁻¹ := by
    have h := (inv_le_one₀ hMpos).mpr hM
    linarith
  have hcoef2 : 1 - M⁻¹ ≤ 2 / 3 := by
    have h : (3 : ℝ)⁻¹ ≤ M⁻¹ := inv_anti₀ hMpos hM3
    norm_num at h
    linarith
  have h₁ := mul_le_mul_of_nonneg_left hgap (mul_nonneg ha.le hcoef)
  have h₂ := mul_le_mul_of_nonneg_right hcoef2 (mul_nonneg ha.le hΔ)
  apply shifted_contraction ha hlower ?_ haccuracy
  nlinarith only [hcompare, h₁, h₂]

section Optimality

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

lemma composite_optimality {h ψ : V → ℝ} {C : Set V} {x g : V}
    (hψ : ConvexOn ℝ C ψ) (hx : x ∈ C) (hg : HasGradientAt h g x)
    (hm : ∀ u ∈ C, h x + ψ x ≤ h u + ψ u) {u : V} (hu : u ∈ C) :
    0 ≤ ⟪g, u - x⟫ + ψ u - ψ x := by
  let d := u - x
  let F : ℝ → ℝ := fun t => h (x + t • d) + ψ x + t * (ψ u - ψ x)
  have hline : HasDerivAt (fun t : ℝ => h (x + t • d)) ⟪g, d⟫ 0 := by
    have hg' : HasGradientAt h g (x + (0 : ℝ) • d) := by simpa using hg
    have hh := hg'.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℝ)).smul_const d |>.const_add x)
    convert hh using 1 <;> simp [Function.comp_def, InnerProductSpace.toDual_apply_apply]
  have hd : HasDerivAt F (⟪g, d⟫ + (ψ u - ψ x)) 0 := by
    convert (hline.add_const (ψ x)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (ψ u - ψ x)) using 1
    · funext t
      rfl
    · simp
  have hmin : IsMinOn F (Icc 0 1) 0 := by
    intro t ht
    have he : x + t • d = (1 - t) • x + t • u := by dsimp [d]; module
    have hmem : x + t • d ∈ C := by
      rw [he]
      exact hψ.1 hx hu (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hupper := segment_upper hψ hx hu ht.1 ht.2
    have hlow := hm _ hmem
    dsimp [F]
    simp only [zero_smul, add_zero, zero_mul]
    dsimp [d] at hlow
    nlinarith
  have htangent : (1 : ℝ) - 0 ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) 1).segment_subset (by constructor <;> norm_num)
        (by constructor <;> norm_num))
  have hh := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  have hh' : 0 ≤ ⟪g, d⟫ + (ψ u - ψ x) := by simpa using hh
  dsimp [d] at hh'
  linarith

end Optimality

section Curvature

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma adjacent_shift_upper {f : V → ℝ} (hf : ConvexOn ℝ univ f)
    {y u v d : V} {j : ℝ} (hj : 0 ≤ j) (hu : (j + 1) • u = y + j • v) :
    (j + 1) * f (u + d) ≤ f (y + (j + 1) • d) + j * f v := by
  have h := extrapolation_lower hf v (u + d) (by linarith : 1 ≤ j + 1)
  have he : v + (j + 1) • (u + d - v) = y + (j + 1) • d := by
    calc
      _ = (j + 1) • u - j • v + (j + 1) • d := by module
      _ = _ := by rw [hu]; abel
  rw [he] at h
  linarith

lemma adjacent_hessian_bound {f : V → ℝ} {A : V → V →L[ℝ] V} {H : ℝ}
    (hf : ConvexOn ℝ univ f) (hpos : ∀ x, 0 ≤ f x)
    (htaylor : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    {y u v d : V} {j : ℝ} (hj : 0 ≤ j) (hu : (j + 1) • u = y + j • v) :
    (j + 1) * ⟪d, A u d⟫ ≤ (j + 1) ^ 2 * ⟪d, A y d⟫ +
      H * ((j + 1) ^ 3 + (j + 1)) * ‖d‖ ^ 3 / 3 + 2 * f y + 2 * j * f v := by
  have hplus := adjacent_shift_upper hf (d := d) hj hu
  have hminus := adjacent_shift_upper hf (d := -d) hj hu
  simp only [smul_neg, ← sub_eq_add_neg] at hminus
  have hlu := (abs_le.mp (htaylor u d)).1
  have hhy := (abs_le.mp (htaylor y ((j + 1) • d))).2
  simp only [map_smul, real_inner_smul_left, inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ j + 1)] at hhy
  have hm := mul_le_mul_of_nonneg_left hlu (by linarith : 0 ≤ j + 1)
  have hn := mul_nonneg (by linarith : 0 ≤ j + 1) (hpos u)
  nlinarith only [hplus, hminus, hhy, hm, hn]

lemma snapshot_curvature_bound {f : V → ℝ} {A : V → V →L[ℝ] V} {H Δ t : ℝ}
    (hf : ConvexOn ℝ univ f) (hpos : ∀ x, 0 ≤ f x)
    (htaylor : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    {x y : V} (hx : f x ≤ Δ) (hy : f y ≤ Δ) (ht0 : 0 ≤ t) (ht1 : 2 * t ≤ 1) :
    t ^ 2 * ⟪y - x, A y (y - x)⟫ ≤
      2 * Δ + (4 / 3 : ℝ) * H * t ^ 3 * ‖y - x‖ ^ 3 := by
  let d := y - x
  let u := y - t • d
  have hz : f (y - (2 * t) • d) ≤ Δ := by
    have h := segment_upper hf (mem_univ y) (mem_univ x) (by linarith : 0 ≤ 2 * t) ht1
    have he : y + (2 * t) • (x - y) = y - (2 * t) • d := by dsimp [d]; module
    rw [he] at h
    have h₁ := mul_le_mul_of_nonneg_left hy (by linarith : 0 ≤ 1 - 2 * t)
    have h₂ := mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ 2 * t)
    nlinarith only [h, h₁, h₂]
  have hT := (abs_le.mp (htaylor u (t • d))).1
  have he₁ : u + t • d = y := by dsimp [u]; abel
  have he₂ : u - t • d = y - (2 * t) • d := by dsimp [u]; module
  rw [he₁, he₂, map_smul, real_inner_smul_left, inner_smul_right,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hT
  have hn := hpos u
  have hQ := LongTails.Proofs.CurvatureMetric.quadratic_perturbation (A u) (A y) d
  have hL := hLip y u
  have he₃ : y - u = t • d := by dsimp [u]; abel
  rw [he₃, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hL
  have hmul := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖d‖)
  have htransfer : ⟪d, A y d⟫ ≤ ⟪d, A u d⟫ + H * t * ‖d‖ ^ 3 := by
    nlinarith only [hQ, hmul]
  have hscale := mul_le_mul_of_nonneg_left htransfer (sq_nonneg t)
  change t ^ 2 * ⟪d, A y d⟫ ≤ 2 * Δ + (4 / 3 : ℝ) * H * t ^ 3 * ‖d‖ ^ 3
  nlinarith only [hT, hn, hz, hy, hscale]

lemma adjacent_unit_curvature {f : V → ℝ} {A : V → V →L[ℝ] V} {H r s j : ℝ}
    (hf : ConvexOn ℝ univ f) (hpos : ∀ x, 0 ≤ f x)
    (htaylor : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    (hH : 0 ≤ H) (hr : 0 < r) (hs : 1 ≤ s) (hj : 0 ≤ j)
    {y u v e : V} (hu : (j + 1) • u = y + j • v) (he : ‖e‖ = 1)
    (hy : f y ≤ H * r ^ 3) (hv : f v ≤ 2 * H * r ^ 3 * s ^ 3) :
    ⟪e, A u e⟫ ≤ (j + 1) * ⟪e, A y e⟫ + 5 * (j + 1) ^ 2 * H * r * s := by
  have hL : 0 < j + 1 := by linarith
  have hs0 : 0 < s := by linarith
  let t := s * r / (j + 1)
  have ht : 0 < t := div_pos (mul_pos hs0 hr) hL
  have hb := adjacent_hessian_bound hf hpos htaylor (d := t • e) hj hu
  simp only [map_smul, real_inner_smul_left, inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, he, mul_one] at hb
  have hv' := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * j)
  have hraw : (j + 1) * t ^ 2 * ⟪e, A u e⟫ ≤
      (j + 1) ^ 2 * t ^ 2 * ⟪e, A y e⟫ +
      H * ((j + 1) ^ 3 + (j + 1)) * t ^ 3 / 3 +
      2 * H * r ^ 3 + 4 * j * H * r ^ 3 * s ^ 3 := by
    nlinarith only [hb, hy, hv']
  have hform : H * ((j + 1) ^ 3 + (j + 1)) * t ^ 3 / 3 +
      2 * H * r ^ 3 + 4 * j * H * r ^ 3 * s ^ 3 =
      (j + 1) * t ^ 2 * (H * r *
        (((j + 1) ^ 2 + 1) * s / (3 * (j + 1)) +
          2 * (j + 1) / s ^ 2 + 4 * j * (j + 1) * s)) := by
    dsimp [t]
    field_simp
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hfrac : 2 * (j + 1) / s ^ 2 ≤ 2 * (j + 1) * s := by
    apply (div_le_iff₀ (sq_pos_of_pos hs0)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * (j + 1)) (sub_nonneg.mpr hs2)]
  have hfrac' : ((j + 1) ^ 2 + 1) * s / (3 * (j + 1)) ≤ (j + 1) * s := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * (j + 1))).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ j * (j + 2)) hs0.le]
  have hcoef : ((j + 1) ^ 2 + 1) * s / (3 * (j + 1)) +
      2 * (j + 1) / s ^ 2 + 4 * j * (j + 1) * s ≤ 5 * (j + 1) ^ 2 * s := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ (j + 1) * (j + 2)) hs0.le]
  have hmul := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hH hr.le)
  have hscale := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ (j + 1) * t ^ 2)
  have hfinal : (j + 1) * t ^ 2 * ⟪e, A u e⟫ ≤
      (j + 1) * t ^ 2 * ((j + 1) * ⟪e, A y e⟫ + 5 * (j + 1) ^ 2 * H * r * s) := by
    nlinarith only [hraw, hscale, hform]
  exact le_of_mul_le_mul_left hfinal (by positivity : 0 < (j + 1) * t ^ 2)

lemma quadratic_bound_of_unit {A B : V →L[ℝ] V} {L D : ℝ}
    (hunit : ∀ e : V, ‖e‖ = 1 → ⟪e, A e⟫ ≤ L * ⟪e, B e⟫ + D) (d : V) :
    ⟪d, A d⟫ ≤ L * ⟪d, B d⟫ + D * ‖d‖ ^ 2 := by
  by_cases hd : d = 0
  · simp [hd]
  have hn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  let e := ‖d‖⁻¹ • d
  have he : ‖e‖ = 1 := by simp [e, norm_smul, hn]
  have h := mul_le_mul_of_nonneg_left (hunit e he) (sq_nonneg ‖d‖)
  have heq : d = ‖d‖ • e := by simp [e, smul_smul, hn]
  have hA : ⟪d, A d⟫ = ‖d‖ ^ 2 * ⟪e, A e⟫ := by
    conv_lhs => rw [heq]
    simp only [map_smul, real_inner_smul_left, inner_smul_right]
    ring
  have hB : ⟪d, B d⟫ = ‖d‖ ^ 2 * ⟪e, B e⟫ := by
    conv_lhs => rw [heq]
    simp only [map_smul, real_inner_smul_left, inner_smul_right]
    ring
  rw [hA, hB]
  nlinarith only [h]

lemma adjacent_curvature {f : V → ℝ} {A : V → V →L[ℝ] V} {H r s j : ℝ}
    (hf : ConvexOn ℝ univ f) (hpos : ∀ x, 0 ≤ f x)
    (htaylor : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    (hH : 0 ≤ H) (hr : 0 < r) (hs : 1 ≤ s) (hj : 0 ≤ j)
    {y u v : V} (hu : (j + 1) • u = y + j • v)
    (hy : f y ≤ H * r ^ 3) (hv : f v ≤ 2 * H * r ^ 3 * s ^ 3) (d : V) :
    ⟪d, A u d⟫ ≤ (j + 1) * ⟪d, A y d⟫ + 5 * (j + 1) ^ 2 * H * r * s * ‖d‖ ^ 2 := by
  apply quadratic_bound_of_unit
  intro e he
  exact adjacent_unit_curvature hf hpos htaylor hH hr hs hj hu he hy hv

lemma geometric_quarter_bound (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i) ≤ 4 / 3 := by
  rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
  have h := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n
  apply (div_le_iff_of_neg (by norm_num : (1 / 4 : ℝ) - 1 < 0)).mpr
  linarith

lemma geometric_sixteenth_bound (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 16 : ℝ) ^ i) ≤ 2 := by
  rw [geom_sum_eq (by norm_num : (1 / 16 : ℝ) ≠ 1)]
  have h := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) n
  apply (div_le_iff_of_neg (by norm_num : (1 / 16 : ℝ) - 1 < 0)).mpr
  linarith

lemma weighted_curvature_bound {n : ℕ} {w a : ℕ → ℝ} {L Q δ : ℝ}
    (hL : 1 ≤ L) (hQ : 0 ≤ Q) (hδ : 0 ≤ δ)
    (hw : ∀ i ≤ n, 0 ≤ w i ∧ w i ≤ (1 / 16 : ℝ) ^ i)
    (ha : ∀ i < n, a i ≤ L * Q + 20 * L ^ 2 * δ * (4 : ℝ) ^ i)
    (htail : w n * a n ≤ w n * (L * Q) + 6 * δ) :
    (∑ i ∈ Finset.range (n + 1), w i * a i) ≤ 2 * L * Q + 256 * L ^ 2 * δ := by
  have hL0 : 0 ≤ L := by linarith
  have hterm : ∀ i ∈ Finset.range n,
      w i * a i ≤ (1 / 16 : ℝ) ^ i * (L * Q) +
        20 * L ^ 2 * δ * (1 / 4 : ℝ) ^ i := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have h₁ := mul_le_mul_of_nonneg_left (ha i hin) (hw i hin.le).1
    have h₂ := mul_le_mul_of_nonneg_right (hw i hin.le).2
      (by positivity : 0 ≤ L * Q + 20 * L ^ 2 * δ * (4 : ℝ) ^ i)
    have he : (1 / 16 : ℝ) ^ i * (4 : ℝ) ^ i = (1 / 4 : ℝ) ^ i := by
      rw [← mul_pow]; norm_num
    calc
      _ ≤ (1 / 16 : ℝ) ^ i * (L * Q + 20 * L ^ 2 * δ * (4 : ℝ) ^ i) := h₁.trans h₂
      _ = (1 / 16 : ℝ) ^ i * (L * Q) + 20 * L ^ 2 * δ * ((1 / 16 : ℝ) ^ i * 4 ^ i) := by ring
      _ = _ := by rw [he]
  have hs := Finset.sum_le_sum hterm
  have htail' := mul_le_mul_of_nonneg_right (hw n le_rfl).2 (mul_nonneg hL0 hQ)
  have hsum : (∑ i ∈ Finset.range (n + 1), w i * a i) ≤
      (∑ i ∈ Finset.range (n + 1), (1 / 16 : ℝ) ^ i) * (L * Q) +
      20 * L ^ 2 * δ * (∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i) + 6 * δ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at hs
    nlinarith only [hs, htail, htail']
  have hg₁ := mul_le_mul_of_nonneg_right (geometric_sixteenth_bound (n + 1))
    (mul_nonneg hL0 hQ)
  have hg₂ := mul_le_mul_of_nonneg_left (geometric_quarter_bound n)
    (by positivity : 0 ≤ 20 * L ^ 2 * δ)
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hd := mul_le_mul_of_nonneg_right hL2 hδ
  have hn : 0 ≤ L ^ 2 * δ := mul_nonneg (sq_nonneg L) hδ
  nlinarith only [hsum, hg₁, hg₂, hd, hn]

end Curvature

end LongTails.Proofs.CompositeExtrapolation
