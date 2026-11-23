import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace LongTails.Proofs.DistributedGrowthComparison

open OracleTemplate.Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gap_of_alignment {F G : E → ℝ} {g v : E → E} {L M J : ℝ} {z : E}
    (hF : ConvexOn ℝ Set.univ F) (hg : ∀ x, HasGradientAt F (g x) x)
    (hv : ∀ x, HasGradientAt G (v x) x)
    (hL : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hM : ∀ x y, ‖v x - v y‖ ≤ M * ‖x - y‖)
    (hmin : ∀ x, G z ≤ G x) (hJ : 0 < J)
    (halign : ∀ x, J * ‖g x‖ ^ 2 ≤ ⟪v x, g x⟫) (x : E) :
    J * (F x - F z) ≤ G x - G z := by
  by_contra! hbad
  have hd : 0 < F x - F z := by
    by_contra! hn
    linarith [mul_nonpos_of_nonneg_of_nonpos hJ.le hn, hmin x]
  let a := (J + (G x - G z) / (F x - F z)) / 2
  have hr := (div_lt_iff₀ hd).mpr hbad
  have ha : 0 < a := by dsimp [a]; positivity [div_nonneg (sub_nonneg.mpr (hmin x)) hd.le]
  have haj : a < J := by dsimp [a]; linarith
  have hax : G x - G z < a * (F x - F z) := by
    apply (div_lt_iff₀ hd).mp
    dsimp [a]
    linarith
  let B := max 1 (max L (M / (2 * (J-a))))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have hLB : L ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hMB : M ≤ 2 * (J-a) * B := by
    have hh : M / (2 * (J-a)) ≤ B := (le_max_right ..).trans (le_max_right ..)
    linarith only [(div_le_iff₀ (by linarith : 0 < 2 * (J-a))).mp hh]
  let T := fun y => y - (1/B) • g y
  have hstep (y : E) : a * (F y - F (T y)) ≤ G y - G (T y) := by
    have he : T y - y = -(1/B) • g y := by dsimp [T]; module
    have hs := convex_support hF hg y (T y)
    have hu := smooth_upper_bound hv hM y (T y)
    rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq] at hs
    rw [he, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (one_div_pos.mpr hB), mul_pow] at hu
    have h1 := mul_le_mul_of_nonneg_left (halign y) (one_div_pos.mpr hB).le
    have h2 := mul_le_mul_of_nonneg_right hMB (show 0 ≤ (1/B)^2 * ‖g y‖^2 by positivity)
    have h3 := mul_le_mul_of_nonneg_left hs ha.le
    have hid : B * (1/B)^2 = 1/B := by field_simp
    have h4 : M * ((1/B)^2 * ‖g y‖^2) ≤
        2*(J-a)*((1/B)*‖g y‖^2) := by
      calc
        _ ≤ (2*(J-a)*B) * ((1/B)^2 * ‖g y‖^2) := h2
        _ = 2*(J-a)*((B*(1/B)^2)*‖g y‖^2) := by ring
        _ = _ := by rw [hid]
    linarith only [h1, h3, hu, h4]
  have htel (k : ℕ) : a * (F x - F (T^[k] x)) ≤ G x - G (T^[k] x) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      linarith only [ih, hstep (T^[k] x)]
  let e := (a*(F x-F z) - (G x-G z))/(2*a)
  have he : 0 < e := div_pos (sub_pos.mpr hax) (by positivity)
  let k := max 1 ⌈B * ‖x-z‖^2 / (2*e)⌉₊
  have hh := gd_accuracy F g B ‖x-z‖ e x z hB (norm_nonneg _) he hF hg
    (fun y t => (hL y t).trans (mul_le_mul_of_nonneg_right hLB (norm_nonneg _)))
    le_rfl k le_rfl
  rw [execute_gd] at hh
  change F (T^[k] x) - F z ≤ e at hh
  have hed : (2*a)*e = a*(F x-F z) - (G x-G z) := by
    dsimp [e]
    field_simp
  nlinarith only [htel k, mul_le_mul_of_nonneg_left hh ha.le, hmin (T^[k] x), hed, hax]

end LongTails.Proofs.DistributedGrowthComparison
