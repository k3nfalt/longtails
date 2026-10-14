import LongTails.Setups.GapSmoothStrongGrowth
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma model_of_six {f : E → ℝ} {u : E} {H0 H1 : ℝ}
    (hm : GapUpperModel f u H0 H1) (x y : E)
    (hr : 6 * Real.sqrt H1 * ‖y - x‖ ≤ 1) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ +
      (H0 + H1 * (f x - f u)) * ‖y - x‖ ^ 2 := by
  apply hm
  have h3 : Real.sqrt 3 ≤ 7 / 4 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have h6 : Real.sqrt 6 ≤ 5 / 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  have hh : 2 * Real.sqrt 3 + Real.sqrt 6 ≤ 6 := by linarith
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _)) (norm_nonneg _)).trans hr

lemma gradient_self_bound {f : E → ℝ} {u : E} {H0 H1 : ℝ}
    (h0 : 0 ≤ H0) (h1 : 0 ≤ H1) (hmin : IsMinOn f univ u)
    (hm : GapUpperModel f u H0 H1) (x : E) :
    ‖gradient f x‖ ^ 2 ≤ 144 * (f x - f u) * (H0 + H1 * (f x - f u)) := by
  let F := f x - f u
  let G := ‖gradient f x‖
  have hF : 0 ≤ F := sub_nonneg.mpr (hmin (mem_univ x))
  have hG : 0 ≤ G := norm_nonneg _
  have hH : 0 ≤ H0 + H1 * F := by positivity
  change G ^ 2 ≤ 144 * F * (H0 + H1 * F)
  by_cases hz : F = 0
  · have hx : IsMinOn f univ x := by
      intro y hy
      have hfy : f u ≤ f y := hmin hy
      dsimp [F] at hz
      change f x ≤ f y
      linarith
    have hd := (hx.isLocalMin Filter.univ_mem).fderiv_eq_zero
    have hg : gradient f x = 0 := by simp [gradient, hd]
    simp [G, hg, hz]
  have hFp : 0 < F := lt_of_le_of_ne hF (Ne.symm hz)
  by_contra! hbad
  have hGp : 0 < G := by nlinarith [mul_nonneg hF hH]
  have hrad : 12 * Real.sqrt H1 * F < G := by
    have hs := Real.sq_sqrt h1
    have hsF : (Real.sqrt H1 * F) ^ 2 = H1 * F ^ 2 := by rw [mul_pow, hs]
    have hh : (12 * Real.sqrt H1 * F) ^ 2 < G ^ 2 := by
      nlinarith [mul_nonneg h0 hF, hsF]
    exact (sq_lt_sq₀ (by positivity) hG).mp hh
  let t := 2 * F / G ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hn : ‖x - t • gradient f x - x‖ = t * G := by
    rw [show x - t • gradient f x - x = -(t • gradient f x) by module]
    simp [norm_smul, abs_of_pos ht, G]
  have hr : 6 * Real.sqrt H1 * ‖x - t • gradient f x - x‖ ≤ 1 := by
    rw [hn]
    dsimp [t]
    field_simp
    nlinarith
  have hb := model_of_six hm x (x - t • gradient f x) hr
  rw [show x - t • gradient f x - x = -(t • gradient f x) by module,
    inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hb
  have hlow := hmin (mem_univ (x - t • gradient f x))
  change f (x - t • gradient f x) ≤ f x - t * G ^ 2 +
    (H0 + H1 * F) * (t * G) ^ 2 at hb
  have he1 : t * G ^ 2 = 2 * F := by dsimp [t]; field_simp
  have he2 : (t * G) ^ 2 * G ^ 2 = 4 * F ^ 2 := by dsimp [t]; field_simp; ring
  rw [he1] at hb
  have hh : F ≤ (H0 + H1 * F) * (t * G) ^ 2 := by dsimp [F] at *; linarith
  have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg G)
  have hbad' := mul_lt_mul_of_pos_left hbad hFp
  nlinarith [mul_nonneg hF hH]

lemma scaled_geometry {f : E → ℝ} {u : E} {H0 H1 A R B c : ℝ}
    (h0 : 0 ≤ H0) (h1 : 0 ≤ H1) (hA : 0 < A) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hc : 1 ≤ c) (hmin : IsMinOn f univ u) (hm : GapUpperModel f u H0 H1)
    (hscale : H0 * A + H1 * R ^ 2 ≤ B ^ 2) (x : E)
    (hgap : A * (f x - f u) ≤ c * R ^ 2) :
    A * (H0 + H1 * (f x - f u)) ≤ c * B ^ 2 ∧
    A * ‖gradient f x‖ ≤ 12 * c * R * B := by
  have hF : 0 ≤ f x - f u := sub_nonneg.mpr (hmin (mem_univ x))
  have hH : 0 ≤ H0 + H1 * (f x - f u) := by positivity
  have hcp : 0 ≤ c := by linarith
  have hcurv : A * (H0 + H1 * (f x - f u)) ≤ c * B ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hgap h1
    have hs := mul_le_mul_of_nonneg_left hscale hcp
    nlinarith [mul_nonneg (show 0 ≤ c - 1 by linarith) (mul_nonneg h0 hA.le)]
  refine ⟨hcurv, ?_⟩
  have hprod := mul_le_mul hgap hcurv (mul_nonneg hA.le hH) (by positivity : 0 ≤ c * R ^ 2)
  have hg := mul_le_mul_of_nonneg_left (gradient_self_bound h0 h1 hmin hm x) (sq_nonneg A)
  have hs : (A * ‖gradient f x‖) ^ 2 ≤ (12 * c * R * B) ^ 2 := by nlinarith
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hs

lemma model_safe_of_scaled_distance {f : E → ℝ} {u x y : E} {H0 H1 R B : ℝ}
    (hR : 0 < R) (hscale : R * Real.sqrt H1 ≤ B)
    (hd : B * ‖y - x‖ ≤ R / 6) (hm : GapUpperModel f u H0 H1) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ +
      (H0 + H1 * (f x - f u)) * ‖y - x‖ ^ 2 := by
  apply model_of_six hm x y
  have hh := mul_le_mul_of_nonneg_right hscale (norm_nonneg (y - x))
  nlinarith

lemma query_gap_bound {f : E → ℝ} {u x y : E} {H0 H1 A R B : ℝ}
    (h0 : 0 ≤ H0) (h1 : 0 ≤ H1) (hA : 0 < A) (hR : 0 < R) (hB : 0 ≤ B)
    (hmin : IsMinOn f univ u) (hm : GapUpperModel f u H0 H1)
    (hscale : H0 * A + H1 * R ^ 2 ≤ B ^ 2)
    (hscale' : R * Real.sqrt H1 ≤ B)
    (hgap : A * (f x - f u) ≤ 8 * R ^ 2)
    (hd : B * ‖y - x‖ ≤ R / 4096) :
    A * (f y - f u) ≤ 16 * R ^ 2 := by
  have hx := scaled_geometry h0 h1 hA hR.le hB (by norm_num : (1 : ℝ) ≤ 8)
    hmin hm hscale x hgap
  have hsafe : B * ‖y - x‖ ≤ R / 6 := by linarith
  have hmodel := model_safe_of_scaled_distance hR hscale' hsafe hm
  have hupper := mul_le_mul_of_nonneg_left hmodel hA.le
  have hinner := mul_le_mul_of_nonneg_left (real_inner_le_norm (gradient f x) (y - x)) hA.le
  have hgrad := mul_le_mul_of_nonneg_right hx.2 (norm_nonneg (y - x))
  have hcurv := mul_le_mul_of_nonneg_right hx.1 (sq_nonneg ‖y - x‖)
  have hd0 : 0 ≤ B * ‖y - x‖ := by positivity
  have hd2 : (B * ‖y - x‖) ^ 2 ≤ (R / 4096) ^ 2 :=
    pow_le_pow_left₀ hd0 hd 2
  have hdR := mul_le_mul_of_nonneg_left hd hR.le
  nlinarith only [hgap, hupper, hinner, hgrad, hcurv, hd2, hdR, sq_nonneg R]

end OracleTemplate.GapStrongGrowth
