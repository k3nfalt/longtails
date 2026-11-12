import LongTails.Proofs.CompositeAdaptiveEnergy
import LongTails.Proofs.SymmetricGeneralizedDescent
import Mathlib.Analysis.Complex.ExponentialBounds

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeAdaptive

open OracleTemplate.CompositeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma symmetric_segment_sup {g : E → E} {L0 L1 : ℝ}
    (hg : Continuous g) (hs : SymmetricSmooth g L0 L1) (x y : E) :
    ‖g x - g y‖ ≤ (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖ := by
  have hcompact : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hbounded := (hcompact.image hg.norm).bddAbove
  apply hs
  intro θ hθ
  apply le_csSup hbounded
  refine ⟨x + θ • (y - x), ?_, rfl⟩
  exact ⟨1 - θ, θ, sub_nonneg.mpr hθ.2, hθ.1, by ring, by module⟩

omit [CompleteSpace E] in
lemma shifted_symmetric {g : E → E} {L0 L1 G : ℝ}
    (hs : SymmetricSmooth g L0 L1) {xs : E} (hG : ‖g xs‖ ≤ G) :
    SymmetricSmooth (fun x => g x - g xs) (L0 + L1 * G) L1 := by
  intro x y M hM
  have hb : ∀ θ ∈ Icc (0 : ℝ) 1, ‖g (x + θ • (y - x))‖ ≤ M + G := by
    intro θ hθ
    have ht := norm_le_norm_sub_add (g (x + θ • (y - x))) (g xs)
    linarith [hM θ hθ]
  have hh := hs x y (M + G) hb
  rw [show (g x - g xs) - (g y - g xs) = g x - g y by abel]
  convert hh using 1; ring

lemma shifted_gradient {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasGradientAt f (g x) x) (xs x : E) :
    HasGradientAt (fun z => f z - ⟪g xs, z⟫) (g x - g xs) x := by
  rw [hasGradientAt_iff_hasFDerivAt, map_sub]
  exact (hf x).hasFDerivAt.sub ((toDual ℝ E (g xs)).hasFDerivAt)

omit [CompleteSpace E] in
lemma symmetric_gradient_growth {g : E → E} {L0 L1 : ℝ}
    (hg : Continuous g) (hL1 : 0 < L1) (hs : SymmetricSmooth g L0 L1) (x y : E) :
    L0 + L1 * ‖g x‖ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) :=
  LongTails.Proofs.SymmetricGeneralizedSmooth.gradient_growth hg hL1
    (symmetric_segment_sup hg hs) x y

omit [CompleteSpace E] in
lemma symmetric_gradient_difference {g : E → E} {L0 L1 : ℝ}
    (hg : Continuous g) (hL0 : 0 ≤ L0) (hL1 : 0 < L1)
    (hs : SymmetricSmooth g L0 L1) (x y : E) :
    ‖g x - g y‖ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) * ‖x - y‖ :=
  LongTails.Proofs.SymmetricGeneralizedSmooth.gradient_difference_bound hg hL0 hL1
    (symmetric_segment_sup hg hs) x y

lemma entropy_surplus {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (u y : E) (hu : g u = 0) (hy : 0 < ‖g y‖) :
    f y + ⟪g y, u - y⟫ + L0 / L1 ^ 2 *
      ((1 + L1 * ‖g y‖ / L0) * Real.log (1 + L1 * ‖g y‖ / L0) - L1 * ‖g y‖ / L0) ≤ f u := by
  set G := ‖g y‖ with hG
  set s := L1 * G / L0 with hsdef
  have hs0 : 0 < s := by positivity
  have h1s : 0 < 1 + s := by linarith
  let v : E := G⁻¹ • g y
  have hv : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, norm_inv, norm_norm, ← hG, inv_mul_cancel₀ hy.ne']
  have hi : ⟪g y, v⟫ = G := by
    dsimp only [v]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ← hG, pow_two, ← mul_assoc,
      inv_mul_cancel₀ hy.ne', one_mul]
  set T := Real.log (1 + s) / L1 with hT
  have hT0 : 0 ≤ T := div_nonneg (Real.log_nonneg (by linarith)) hL1.le
  have hgrow := LongTails.Proofs.SymmetricGeneralizedDescent.objective_ray_growth hf hg hL1
    (symmetric_segment_sup hg hs) u v hu hv hT0
  have hexp : Real.exp (L1 * T) = 1 + s := by
    rw [hT, mul_div_cancel₀ _ hL1.ne', Real.exp_log h1s]
  rw [hexp] at hgrow
  have hsupp := Gradient.convex_support hc hf y (u + T • v)
  have he : u + T • v - y = (u - y) + T • v := by abel
  rw [he, inner_add_right, real_inner_smul_right, hi] at hsupp
  have hTG : T * G = L0 / L1 ^ 2 * (s * Real.log (1 + s)) := by
    rw [hT, hsdef]
    field_simp
  have hL1T : L1 * T = Real.log (1 + s) := by rw [hT]; field_simp
  rw [hL1T] at hgrow
  change f y + ⟪g y, u - y⟫ + L0 / L1 ^ 2 * ((1 + s) * Real.log (1 + s) - s) ≤ f u
  nlinarith [hgrow, hsupp, hTG]

omit [CompleteSpace E] in
lemma shifted_convex {f : E → ℝ} (hc : ConvexOn ℝ univ f) (v : E) :
    ConvexOn ℝ univ (fun x => f x - ⟪v, x⟫) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hc.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  linarith

lemma shifted_entropy_surplus {f : E → ℝ} {g : E → E} {L0 L1 G : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (xs y : E) (hG : ‖g xs‖ ≤ G)
    (hy : 0 < ‖g y - g xs‖) :
    (L0 + L1 * G) / L1 ^ 2 *
      ((1 + L1 * ‖g y - g xs‖ / (L0 + L1 * G)) *
        Real.log (1 + L1 * ‖g y - g xs‖ / (L0 + L1 * G)) -
        L1 * ‖g y - g xs‖ / (L0 + L1 * G)) ≤
      f xs - f y - ⟪g y, xs - y⟫ := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hbar : 0 < L0 + L1 * G := by positivity
  have hh := entropy_surplus hbar hL1 (shifted_convex hc (g xs))
    (shifted_gradient hf xs) (hg.sub continuous_const) (shifted_symmetric hs hG) xs y
    (by simp) hy
  simp only [inner_sub_left, inner_sub_right] at hh ⊢
  linarith

lemma entropy_log_lower {u v : ℝ} (hv : 16 ≤ v) (hvu : v ≤ u) :
    v * Real.log (v / 16) ≤ 2 * (u * Real.log u - u + 1) := by
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := hv0.trans_le hvu
  have hlog16 : 2 ≤ Real.log 16 := by
    have hh := Real.log_two_gt_d9
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlu : 2 ≤ Real.log u := hlog16.trans (Real.log_le_log (by norm_num) (hv.trans hvu))
  have hlv : 0 ≤ Real.log (v / 16) := Real.log_nonneg (by linarith)
  have hl : Real.log (v / 16) ≤ Real.log u :=
    Real.log_le_log (by positivity) (by linarith)
  have hp := mul_le_mul hvu hl hlv hu0.le
  have hh := mul_nonneg hu0.le (sub_nonneg.mpr hlu)
  nlinarith

lemma entropy_curvature_lower {L β q S : ℝ} (hL : 0 < L) (hβ : 0 < β)
    (hS : 16 * L ≤ S) (hSq : S ≤ L + β * q) :
    S * Real.log (S / (16 * L)) ≤ 2 * β ^ 2 * (L / β ^ 2 *
      ((1 + β * q / L) * Real.log (1 + β * q / L) - β * q / L)) := by
  have hv : 16 ≤ S / L := (le_div_iff₀ hL).mpr (by linarith)
  have hvu : S / L ≤ 1 + β * q / L := by
    rw [le_div_iff₀ hL] at hv
    apply (div_le_iff₀ hL).mpr
    have he : (1 + β * q / L) * L = L + β * q := by field_simp
    rwa [he]
  have hh := mul_le_mul_of_nonneg_left (entropy_log_lower hv hvu) hL.le
  have he : S / L / 16 = S / (16 * L) := by ring
  rw [he] at hh
  have hl : L * (S / L * Real.log (S / (16 * L))) = S * Real.log (S / (16 * L)) := by
    field_simp
  rw [hl] at hh
  convert hh using 1
  field_simp
  ring

lemma logarithmic_gradient_surplus {f : E → ℝ} {g : E → E} {L0 L1 G : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (xs y : E) (hG : ‖g xs‖ ≤ G)
    (hlarge : 16 * (L0 + L1 * G) ≤ L0 + L1 * ‖g y‖) :
    (L0 + L1 * ‖g y‖) * Real.log ((L0 + L1 * ‖g y‖) / (16 * (L0 + L1 * G))) ≤
      2 * L1 ^ 2 * (f xs - f y - ⟪g y, xs - y⟫) := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hbar : 0 < L0 + L1 * G := by positivity
  have hnorm : ‖g y‖ ≤ ‖g y - g xs‖ + G := by
    have hh := norm_le_norm_sub_add (g y) (g xs)
    linarith
  have hq : 0 < ‖g y - g xs‖ := by nlinarith
  have hsbound : L0 + L1 * ‖g y‖ ≤ L0 + L1 * G + L1 * ‖g y - g xs‖ := by nlinarith
  have hb := shifted_entropy_surplus hL0 hL1 hc hf hg hs xs y hG hq
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * L1 ^ 2)
  exact (entropy_curvature_lower hbar hL1 hlarge hsbound).trans hm

lemma weighted_gradient_surplus {f : E → ℝ} {g : E → E} {L0 L1 G B : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (xs y : E) (hG : ‖g xs‖ ≤ G)
    (hB : 0 < B) (hhigh : 2 * (L0 + L1 * G) ≤ L1 * ‖g y‖)
    (hboundary : 1 / 16 ≤ B * (L0 + L1 * ‖g y‖)) :
    (L0 + L1 * ‖g y‖) * max 1 (Real.log (1 / (256 * (L0 + L1 * G) * B))) ≤
      128 * L1 ^ 2 * (f xs - f y - ⟪g y, xs - y⟫) := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hM : 0 < L0 + L1 * G := by positivity
  have hS : 0 < L0 + L1 * ‖g y‖ := by positivity
  have hD : 0 ≤ f xs - f y - ⟪g y, xs - y⟫ := by
    linarith [Gradient.convex_support hc hf y xs]
  by_cases hh : Real.log (1 / (256 * (L0 + L1 * G) * B)) ≤ 1
  · rw [max_eq_left hh, mul_one]
    exact high_gradient_surplus hL0 hL1 hc hf hg hs xs y hG hhigh
  · have hh' := le_of_not_ge hh
    rw [max_eq_right hh']
    have hratio : 1 / (256 * (L0 + L1 * G) * B) ≤
        (L0 + L1 * ‖g y‖) / (16 * (L0 + L1 * G)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hboundary hM.le]
    have hlog := Real.log_le_log (by positivity) hratio
    have hpos : 0 < Real.log ((L0 + L1 * ‖g y‖) / (16 * (L0 + L1 * G))) := by
      linarith
    have hr := (Real.log_pos_iff (by positivity)).mp hpos
    have hlarge : 16 * (L0 + L1 * G) ≤ L0 + L1 * ‖g y‖ := by
      have := (lt_div_iff₀ (by positivity : 0 < 16 * (L0 + L1 * G))).mp hr
      linarith
    have hb := logarithmic_gradient_surplus hL0 hL1 hc hf hg hs xs y hG hlarge
    have hm := mul_le_mul_of_nonneg_left hlog hS.le
    nlinarith [mul_nonneg (sq_nonneg L1) hD]

omit [CompleteSpace E] in
lemma symmetric_gradient_growth_nonneg {g : E → E} {L0 L1 : ℝ}
    (hg : Continuous g) (hL1 : 0 ≤ L1) (hs : SymmetricSmooth g L0 L1) (x y : E) :
    L0 + L1 * ‖g x‖ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) := by
  by_cases hz : L1 = 0
  · simp [hz]
  · exact symmetric_gradient_growth hg (lt_of_le_of_ne hL1 (Ne.symm hz)) hs x y

omit [CompleteSpace E] in
lemma symmetric_gradient_difference_nonneg {g : E → E} {L0 L1 : ℝ}
    (hg : Continuous g) (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hs : SymmetricSmooth g L0 L1) (x y : E) :
    ‖g x - g y‖ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) * ‖x - y‖ := by
  by_cases hz : L1 = 0
  · simpa [hz] using symmetric_segment_sup hg hs x y
  · exact symmetric_gradient_difference hg hL0 (lt_of_le_of_ne hL1 (Ne.symm hz)) hs x y

lemma symmetric_objective_upper {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hs : SymmetricSmooth g L0 L1) (x y : E) :
    f x ≤ f y + ⟪g y, x - y⟫ +
      (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) / 2 * ‖x - y‖ ^ 2 := by
  have hh := LongTails.Proofs.SymmetricGeneralizedDescent.objective_segment_upper hf y (x - y)
    (M := (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖)) (by
      intro t ht
      have hb := symmetric_gradient_difference_nonneg hg hL0 hL1 hs (y + t • (x - y)) y
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hb
      calc
        _ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * (t * ‖x - y‖)) * (t * ‖x - y‖) := hb
        _ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) * (t * ‖x - y‖) := by
          gcongr <;> nlinarith [norm_nonneg (x - y), ht.1, ht.2]
        _ = _ := by ring)
  simpa only [add_sub_cancel] using hh

end OracleTemplate.CompositeAdaptive
