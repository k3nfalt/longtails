import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace NNReal
open Set

namespace OracleTemplate.HessianNcsc

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

structure Hyp (f : E → F → ℝ) (gx : E × F → E) (gy : E × F → F)
    (Hx : E × F → (E × F →L[ℝ] E)) (Hy : E × F → (E × F →L[ℝ] F)) (L μ ρ : ℝ) : Prop where
  hgx : ∀ x y, HasGradientAt (fun x' => f x' y) (gx (x, y)) x
  hgy : ∀ x y, HasGradientAt (fun y' => f x y') (gy (x, y)) y
  dgx : ∀ z, HasFDerivAt gx (Hx z) z
  dgy : ∀ z, HasFDerivAt gy (Hy z) z
  lip : ∀ z z' : E × F, ‖gx z - gx z'‖ ^ 2 + ‖gy z - gy z'‖ ^ 2 ≤
    L ^ 2 * (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2)
  hess : ∀ (z z' : E × F) (u : E) (v : F),
    ‖(Hx z - Hx z') (u, v)‖ ^ 2 + ‖(Hy z - Hy z') (u, v)‖ ^ 2 ≤
      ρ ^ 2 * (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2)
  sc : ∀ x y y', f x y' ≤ f x y + ⟪gy (x, y), y' - y⟫ - μ / 2 * ‖y' - y‖ ^ 2
  μpos : 0 < μ
  μL : μ ≤ L
  ρnn : 0 ≤ ρ

lemma le_of_sq_le_sq_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}

namespace Hyp

variable (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma L_pos : 0 < L := lt_of_lt_of_le H.μpos H.μL

lemma gx_lip (z z' : E × F) :
    ‖gx z - gx z'‖ ≤ L * Real.sqrt (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := by
  have h := H.lip z z'
  have hs : 0 ≤ ‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2 := by positivity
  apply le_of_sq_le_sq_nonneg (mul_nonneg H.L_pos.le (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt hs]
  nlinarith [sq_nonneg ‖gy z - gy z'‖]

lemma gy_lip (z z' : E × F) :
    ‖gy z - gy z'‖ ≤ L * Real.sqrt (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := by
  have h := H.lip z z'
  have hs : 0 ≤ ‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2 := by positivity
  apply le_of_sq_le_sq_nonneg (mul_nonneg H.L_pos.le (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt hs]
  nlinarith [sq_nonneg ‖gx z - gx z'‖]

lemma gy_lip_y (x : E) (y y' : F) : ‖gy (x, y) - gy (x, y')‖ ≤ L * ‖y - y'‖ := by
  have h := H.gy_lip (x, y) (x, y')
  simpa [Real.sqrt_sq (norm_nonneg _)] using h

lemma gx_lip_y (x : E) (y y' : F) : ‖gx (x, y) - gx (x, y')‖ ≤ L * ‖y - y'‖ := by
  have h := H.gx_lip (x, y) (x, y')
  simpa [Real.sqrt_sq (norm_nonneg _)] using h

lemma gy_mono (x : E) (y y' : F) :
    ⟪gy (x, y') - gy (x, y), y' - y⟫ ≤ -(μ * ‖y' - y‖ ^ 2) := by
  have h1 := H.sc x y y'
  have h2 := H.sc x y' y
  have e1 : ⟪gy (x, y'), y - y'⟫ = -⟪gy (x, y'), y' - y⟫ := by
    rw [← inner_neg_right, neg_sub]
  have e2 : ‖y - y'‖ = ‖y' - y‖ := norm_sub_rev _ _
  rw [inner_sub_left]
  rw [e1, e2] at h2
  linarith

lemma contraction_sq (x : E) (y y' : F) :
    ‖(y + (μ / L ^ 2) • gy (x, y)) - (y' + (μ / L ^ 2) • gy (x, y'))‖ ^ 2 ≤
      (1 - μ ^ 2 / L ^ 2) * ‖y - y'‖ ^ 2 := by
  have hL := H.L_pos
  set c : ℝ := μ / L ^ 2 with hc
  have hc0 : 0 ≤ c := div_nonneg H.μpos.le (by positivity)
  have e : (y + c • gy (x, y)) - (y' + c • gy (x, y')) = (y - y') + c • (gy (x, y) - gy (x, y')) := by
    rw [smul_sub]; abel
  rw [e, norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_of_nonneg hc0]
  have hm : ⟪y - y', gy (x, y) - gy (x, y')⟫ ≤ -(μ * ‖y - y'‖ ^ 2) := by
    have := H.gy_mono x y' y
    rw [real_inner_comm] at this
    exact this
  have hl := H.gy_lip_y x y y'
  have hl2 : ‖gy (x, y) - gy (x, y')‖ ^ 2 ≤ L ^ 2 * ‖y - y'‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg _) hl
    nlinarith [this]
  have key : c * (L ^ 2 * c) = μ ^ 2 / L ^ 2 := by
    rw [hc]; field_simp
  have key2 : 2 * c * μ = 2 * (μ ^ 2 / L ^ 2) := by
    rw [hc]; field_simp
  have : (c * ‖gy (x, y) - gy (x, y')‖) ^ 2 ≤ c ^ 2 * (L ^ 2 * ‖y - y'‖ ^ 2) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hl2 (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ 2 * c)]

lemma exists_root (x : E) : ∃ y, gy (x, y) = 0 := by
  have hL := H.L_pos
  have hμ := H.μpos
  set a : ℝ := 1 - μ ^ 2 / L ^ 2 with ha
  have ha0 : 0 ≤ a := by
    rw [ha, sub_nonneg, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hμ.le H.μL 2
  have ha1 : a < 1 := by
    rw [ha]; have : 0 < μ ^ 2 / L ^ 2 := by positivity
    linarith
  set K : ℝ≥0 := ⟨Real.sqrt a, Real.sqrt_nonneg _⟩ with hK
  have hK1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    show Real.sqrt a < 1
    rw [Real.sqrt_lt' one_pos]; simpa using ha1
  let T : F → F := fun y => y + (μ / L ^ 2) • gy (x, y)
  have hT : ContractingWith K T := by
    refine ⟨hK1, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    show ‖T y - T y'‖ ≤ Real.sqrt a * ‖y - y'‖
    apply le_of_sq_le_sq_nonneg (by positivity)
    rw [mul_pow, Real.sq_sqrt ha0]
    exact H.contraction_sq x y y'
  have hfix := hT.fixedPoint_isFixedPt (f := T)
  refine ⟨ContractingWith.fixedPoint T hT, ?_⟩
  have h : T (ContractingWith.fixedPoint T hT) = ContractingWith.fixedPoint T hT := hfix
  have hc : (μ / L ^ 2) ≠ 0 := by positivity
  have h2 : (μ / L ^ 2) • gy (x, ContractingWith.fixedPoint T hT) = 0 := by
    have := congrArg (fun v => v - ContractingWith.fixedPoint T hT) h
    simpa [T] using this
  exact (smul_eq_zero.mp h2).resolve_left hc

end Hyp

noncomputable def ystar (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : F :=
  Classical.choose (H.exists_root x)

namespace Hyp

variable (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma gy_ystar (x : E) : gy (x, ystar H x) = 0 := Classical.choose_spec (H.exists_root x)

lemma ystar_quad (x : E) (y : F) : f x y ≤ f x (ystar H x) - μ / 2 * ‖y - ystar H x‖ ^ 2 := by
  have h := H.sc x (ystar H x) y
  rw [H.gy_ystar x, inner_zero_left] at h
  linarith

lemma ystar_max (x : E) (y : F) : f x y ≤ f x (ystar H x) := by
  have h := H.ystar_quad x y
  have : 0 ≤ μ / 2 * ‖y - ystar H x‖ ^ 2 := mul_nonneg (by linarith [H.μpos]) (by positivity)
  linarith

lemma ystar_unique (x : E) (y : F) (hy : ∀ y', f x y' ≤ f x y) : y = ystar H x := by
  have h := H.ystar_quad x y
  have h2 := hy (ystar H x)
  have hq : μ / 2 * ‖y - ystar H x‖ ^ 2 ≤ 0 := by linarith
  have hμ2 : 0 < μ / 2 := by linarith [H.μpos]
  have : ‖y - ystar H x‖ ^ 2 ≤ 0 := by
    by_contra hc; push Not at hc; nlinarith
  have : ‖y - ystar H x‖ = 0 := by
    have := sq_nonneg ‖y - ystar H x‖; nlinarith [norm_nonneg (y - ystar H x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma ystar_lip (a b : E) : ‖ystar H a - ystar H b‖ ≤ (L / μ) * ‖a - b‖ := by
  have hμ := H.μpos
  set d := ystar H a - ystar H b
  have hm := H.gy_mono a (ystar H b) (ystar H a)
  rw [H.gy_ystar a, zero_sub, inner_neg_left] at hm
  have hl := H.gy_lip (a, ystar H b) (b, ystar H b)
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, Real.sqrt_sq (norm_nonneg _)] at hl
  rw [H.gy_ystar b, sub_zero] at hl
  have hci : ⟪gy (a, ystar H b), d⟫ ≤ ‖gy (a, ystar H b)‖ * ‖d‖ := real_inner_le_norm _ _
  have h1 : μ * ‖d‖ ^ 2 ≤ L * ‖a - b‖ * ‖d‖ := by
    have := mul_le_mul_of_nonneg_right hl (norm_nonneg d)
    linarith
  by_cases hd : ‖d‖ = 0
  · rw [hd]; exact mul_nonneg (div_nonneg H.L_pos.le hμ.le) (norm_nonneg _)
  · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    nlinarith

end Hyp

end OracleTemplate.HessianNcsc

namespace OracleTemplate.HessianNcsc

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}

def sq (d : E × F) : ℝ := ‖d.1‖ ^ 2 + ‖d.2‖ ^ 2

omit [InnerProductSpace ℝ E] [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma sq_nonneg' (d : E × F) : 0 ≤ sq d := by unfold sq; positivity

lemma small_t_le {a b c : ℝ} (hc : 0 ≤ c) (h : ∀ t : ℝ, 0 < t → a ≤ b + c * t) : a ≤ b := by
  by_contra hab
  push Not at hab
  by_cases hc0 : c = 0
  · have := h 1 one_pos; rw [hc0] at this; linarith
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have := h ((a - b) / (2 * c)) (by positivity)
    have e : c * ((a - b) / (2 * c)) = (a - b) / 2 := by field_simp
    rw [e] at this; linarith


omit [CompleteSpace E] [CompleteSpace F] in
lemma sq_smul (t : ℝ) (d : E × F) : sq (t • d) = t ^ 2 * sq d := by
  simp only [sq, Prod.smul_fst, Prod.smul_snd, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

namespace Hyp

variable (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma hessx_diff (z z' d : E × F) :
    ‖(Hx z - Hx z') d‖ ≤ ρ * Real.sqrt (sq (z - z')) * Real.sqrt (sq d) := by
  have h := H.hess z z' d.1 d.2
  have hd : d = (d.1, d.2) := rfl
  rw [← hd] at h
  have h1 : ‖(Hx z - Hx z') d‖ ^ 2 ≤ ρ ^ 2 * sq (z - z') * sq d := by
    have := sq_nonneg ‖(Hy z - Hy z') d‖
    simp only [sq, Prod.fst_sub, Prod.snd_sub]; linarith
  apply le_of_sq_le_sq_nonneg
    (mul_nonneg (mul_nonneg H.ρnn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  rw [mul_pow, mul_pow, Real.sq_sqrt (sq_nonneg' _), Real.sq_sqrt (sq_nonneg' _)]
  exact h1

lemma hessy_diff (z z' d : E × F) :
    ‖(Hy z - Hy z') d‖ ≤ ρ * Real.sqrt (sq (z - z')) * Real.sqrt (sq d) := by
  have h := H.hess z z' d.1 d.2
  have hd : d = (d.1, d.2) := rfl
  rw [← hd] at h
  have h1 : ‖(Hy z - Hy z') d‖ ^ 2 ≤ ρ ^ 2 * sq (z - z') * sq d := by
    have := sq_nonneg ‖(Hx z - Hx z') d‖
    simp only [sq, Prod.fst_sub, Prod.snd_sub]; linarith
  apply le_of_sq_le_sq_nonneg
    (mul_nonneg (mul_nonneg H.ρnn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  rw [mul_pow, mul_pow, Real.sq_sqrt (sq_nonneg' _), Real.sq_sqrt (sq_nonneg' _)]
  exact h1

lemma taylor_aux {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : E × F → V) (Dg : E × F → (E × F →L[ℝ] V)) (hg : ∀ z, HasFDerivAt g (Dg z) z)
    (hD : ∀ z z' d, ‖(Dg z - Dg z') d‖ ≤ ρ * Real.sqrt (sq (z - z')) * Real.sqrt (sq d))
    (z d : E × F) : ‖g (z + d) - g z - Dg z d‖ ≤ ρ * sq d := by
  let φ : ℝ → V := fun t => g (z + t • d) - t • Dg z d
  have hφ : ∀ t, HasDerivAt φ (Dg (z + t • d) d - Dg z d) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => z + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add z
    have h2 := (hg (z + t • d)).comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t • Dg z d) (Dg z d) t := by
      simpa using (hasDerivAt_id t).smul_const (Dg z d)
    exact h2.sub h3
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖Dg (z + t • d) d - Dg z d‖ ≤ ρ * sq d := by
    intro t ht
    have e : Dg (z + t • d) d - Dg z d = (Dg (z + t • d) - Dg z) d := by
      simp []
    rw [e]
    refine (hD _ _ _).trans ?_
    have hz : (z + t • d) - z = t • d := by abel
    rw [hz, sq_smul, Real.sqrt_mul (sq_nonneg (t)), Real.sqrt_sq_eq_abs, abs_of_nonneg ht.1]
    have hs := Real.mul_self_sqrt (sq_nonneg' d)
    have ht1 : t ≤ 1 := ht.2.le
    calc ρ * (t * Real.sqrt (sq d)) * Real.sqrt (sq d) = ρ * t * (Real.sqrt (sq d) * Real.sqrt (sq d)) := by ring
      _ = ρ * t * sq d := by rw [hs]
      _ ≤ ρ * 1 * sq d := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg' d)
        exact mul_le_mul_of_nonneg_left ht1 H.ρnn
      _ = ρ * sq d := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := φ) (fun t _ => (hφ t).hasDerivWithinAt) hbound
  have e1 : φ 1 - φ 0 = g (z + d) - g z - Dg z d := by
    simp only [φ, one_smul, zero_smul, add_zero, sub_zero]; abel
  rw [e1] at key
  exact key

lemma taylor_x (z d : E × F) : ‖gx (z + d) - gx z - Hx z d‖ ≤ ρ * sq d :=
  H.taylor_aux gx Hx H.dgx H.hessx_diff z d

lemma taylor_y (z d : E × F) : ‖gy (z + d) - gy z - Hy z d‖ ≤ ρ * sq d :=
  H.taylor_aux gy Hy H.dgy H.hessy_diff z d

lemma hessx_bound (z d : E × F) : ‖Hx z d‖ ≤ L * Real.sqrt (sq d) := by
  apply small_t_le (mul_nonneg H.ρnn (sq_nonneg' d))
  intro t ht
  have h1 := H.taylor_x z (t • d)
  have h2 := H.gx_lip (z + t • d) z
  have hz : (z + t • d) - z = t • d := by abel
  have hs : Real.sqrt (‖(z + t • d).1 - z.1‖ ^ 2 + ‖(z + t • d).2 - z.2‖ ^ 2) = t * Real.sqrt (sq d) := by
    have : ‖(z + t • d).1 - z.1‖ ^ 2 + ‖(z + t • d).2 - z.2‖ ^ 2 = sq (t • d) := by
      simp only [sq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_sub_cancel_left]
    rw [this, sq_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  rw [hs] at h2
  rw [sq_smul] at h1
  have e : Hx z (t • d) = t • Hx z d := by simp
  rw [e] at h1
  have h3 : ‖t • Hx z d‖ ≤ ‖gx (z + t • d) - gx z‖ + ρ * (t ^ 2 * sq d) := by
    have := norm_sub_le (gx (z + t • d) - gx z) (gx (z + t • d) - gx z - t • Hx z d)
    have e2 : gx (z + t • d) - gx z - (gx (z + t • d) - gx z - t • Hx z d) = t • Hx z d := by abel
    rw [e2] at this; linarith
  rw [norm_smul, Real.norm_of_nonneg ht.le] at h3
  have h4 : t * ‖Hx z d‖ ≤ t * (L * Real.sqrt (sq d) + ρ * sq d * t) := by nlinarith
  exact le_of_mul_le_mul_left h4 ht

lemma hessy_bound (z d : E × F) : ‖Hy z d‖ ≤ L * Real.sqrt (sq d) := by
  apply small_t_le (mul_nonneg H.ρnn (sq_nonneg' d))
  intro t ht
  have h1 := H.taylor_y z (t • d)
  have h2 := H.gy_lip (z + t • d) z
  have hz : (z + t • d) - z = t • d := by abel
  have hs : Real.sqrt (‖(z + t • d).1 - z.1‖ ^ 2 + ‖(z + t • d).2 - z.2‖ ^ 2) = t * Real.sqrt (sq d) := by
    have : ‖(z + t • d).1 - z.1‖ ^ 2 + ‖(z + t • d).2 - z.2‖ ^ 2 = sq (t • d) := by
      simp only [sq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_sub_cancel_left]
    rw [this, sq_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  rw [hs] at h2
  rw [sq_smul] at h1
  have e : Hy z (t • d) = t • Hy z d := by simp
  rw [e] at h1
  have h3 : ‖t • Hy z d‖ ≤ ‖gy (z + t • d) - gy z‖ + ρ * (t ^ 2 * sq d) := by
    have := norm_sub_le (gy (z + t • d) - gy z) (gy (z + t • d) - gy z - t • Hy z d)
    have e2 : gy (z + t • d) - gy z - (gy (z + t • d) - gy z - t • Hy z d) = t • Hy z d := by abel
    rw [e2] at this; linarith
  rw [norm_smul, Real.norm_of_nonneg ht.le] at h3
  have h4 : t * ‖Hy z d‖ ≤ t * (L * Real.sqrt (sq d) + ρ * sq d * t) := by nlinarith
  exact le_of_mul_le_mul_left h4 ht

end Hyp

end OracleTemplate.HessianNcsc

namespace OracleTemplate.HessianNcsc

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}

noncomputable def zs (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : E × F := (x, ystar H x)

noncomputable def Gs (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : E := gx (zs H x)

noncomputable def Jb (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : F →L[ℝ] F :=
  (Hy (zs H x)).comp (ContinuousLinearMap.inr ℝ E F)

noncomputable def Bb (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : F →L[ℝ] E :=
  (Hx (zs H x)).comp (ContinuousLinearMap.inr ℝ E F)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma sq_inr (v : F) : sq ((0 : E), v) = ‖v‖ ^ 2 := by simp [sq]

namespace Hyp

variable (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma lin_y (x : E) (e : F) : ‖gy (x, ystar H x + e) - Jb H x e‖ ≤ ρ * ‖e‖ ^ 2 := by
  have h := H.taylor_y (zs H x) ((0 : E), e)
  have hz : zs H x + ((0 : E), e) = (x, ystar H x + e) := by simp [zs]
  rw [hz, sq_inr] at h
  have h0 : gy (zs H x) = 0 := H.gy_ystar x
  rw [h0, sub_zero] at h
  simpa [Jb] using h

lemma lin_x (x : E) (e : F) : ‖gx (x, ystar H x + e) - Gs H x - Bb H x e‖ ≤ ρ * ‖e‖ ^ 2 := by
  have h := H.taylor_x (zs H x) ((0 : E), e)
  have hz : zs H x + ((0 : E), e) = (x, ystar H x + e) := by simp [zs]
  rw [hz, sq_inr] at h
  simpa [Jb, Bb, Gs] using h

lemma Jb_norm (x : E) (v : F) : ‖Jb H x v‖ ≤ L * ‖v‖ := by
  have h := H.hessy_bound (zs H x) ((0 : E), v)
  rw [sq_inr, Real.sqrt_sq (norm_nonneg _)] at h
  simpa [Jb] using h

lemma Bb_norm (x : E) (v : F) : ‖Bb H x v‖ ≤ L * ‖v‖ := by
  have h := H.hessx_bound (zs H x) ((0 : E), v)
  rw [sq_inr, Real.sqrt_sq (norm_nonneg _)] at h
  simpa [Bb] using h

lemma Jb_inner (x : E) (v : F) : ⟪Jb H x v, v⟫ ≤ -(μ * ‖v‖ ^ 2) := by
  apply small_t_le (mul_nonneg H.ρnn (by positivity : (0:ℝ) ≤ ‖v‖ ^ 3))
  intro t ht
  have h1 := H.lin_y x (t • v)
  have h2 := H.gy_mono x (ystar H x) (ystar H x + t • v)
  rw [H.gy_ystar x, sub_zero, add_sub_cancel_left] at h2
  have hJ : Jb H x (t • v) = t • Jb H x v := by simp
  rw [hJ] at h1
  set R := gy (x, ystar H x + t • v) - t • Jb H x v
  have hR : ‖R‖ ≤ ρ * (t ^ 2 * ‖v‖ ^ 2) := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, mul_pow] at h1; exact h1
  have e1 : gy (x, ystar H x + t • v) = t • Jb H x v + R := by simp [R]
  rw [e1, inner_add_left, inner_smul_left, inner_smul_right, inner_smul_right] at h2
  simp only [RCLike.conj_to_real] at h2
  rw [norm_smul, Real.norm_of_nonneg ht.le, mul_pow] at h2
  have hRi : |⟪R, v⟫| ≤ ‖R‖ * ‖v‖ := abs_real_inner_le_norm R v
  have hRi' : -(ρ * (t ^ 2 * ‖v‖ ^ 2) * ‖v‖) ≤ ⟪R, v⟫ := by
    have := neg_abs_le ⟪R, v⟫
    nlinarith [mul_le_mul_of_nonneg_right hR (norm_nonneg v)]
  have ht2 : 0 < t ^ 2 := by positivity
  have key : t ^ 2 * ⟪Jb H x v, v⟫ ≤ t ^ 2 * (-(μ * ‖v‖ ^ 2) + ρ * ‖v‖ ^ 3 * t) := by
    nlinarith
  exact le_of_mul_le_mul_left key ht2

lemma Jb_lower (x : E) (v : F) : μ * ‖v‖ ≤ ‖Jb H x v‖ := by
  have h := H.Jb_inner x v
  have hc : -‖Jb H x v‖ * ‖v‖ ≤ ⟪Jb H x v, v⟫ := by
    have := real_inner_le_norm (-(Jb H x v)) v
    rw [inner_neg_left, norm_neg] at this; linarith
  by_cases hv : ‖v‖ = 0
  · rw [hv, mul_zero]; exact norm_nonneg _
  · have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith

lemma Jb_injective (x : E) : Function.Injective (Jb H x) := by
  intro v w hvw
  have h := H.Jb_lower x (v - w)
  rw [map_sub, hvw, sub_self, norm_zero] at h
  have : ‖v - w‖ = 0 := by
    have := norm_nonneg (v - w)
    nlinarith [H.μpos]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Hyp

noncomputable def Jinv [FiniteDimensional ℝ F] (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : F ≃ₗ[ℝ] F :=
  LinearEquiv.ofInjectiveEndo ((Jb H x : F →L[ℝ] F) : F →ₗ[ℝ] F) (H.Jb_injective x)

noncomputable def Mm [FiniteDimensional ℝ F] (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) (w : F) : E :=
  Bb H x ((Jinv H x).symm w)

namespace Hyp

variable [FiniteDimensional ℝ F] (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma Jinv_apply (x : E) (v : F) : (Jinv H x) v = Jb H x v := rfl

lemma Jb_Jinv (x : E) (w : F) : Jb H x ((Jinv H x).symm w) = w := by
  have h1 := (Jinv H x).apply_symm_apply w
  rw [H.Jinv_apply] at h1
  exact h1

lemma Jinv_Jb (x : E) (v : F) : (Jinv H x).symm (Jb H x v) = v := by
  have h1 := (Jinv H x).symm_apply_apply v
  rw [H.Jinv_apply] at h1
  exact h1

lemma Jinv_norm (x : E) (w : F) : ‖(Jinv H x).symm w‖ ≤ ‖w‖ / μ := by
  have h := H.Jb_lower x ((Jinv H x).symm w)
  rw [H.Jb_Jinv x w] at h
  rw [le_div_iff₀ H.μpos]; linarith

lemma Mm_norm (x : E) (w : F) : ‖Mm H x w‖ ≤ (L / μ) * ‖w‖ := by
  have h1 := H.Bb_norm x ((Jinv H x).symm w)
  have h2 := H.Jinv_norm x w
  calc ‖Mm H x w‖ ≤ L * ‖(Jinv H x).symm w‖ := h1
    _ ≤ L * (‖w‖ / μ) := mul_le_mul_of_nonneg_left h2 H.L_pos.le
    _ = (L / μ) * ‖w‖ := by ring

lemma Mm_Jb (x : E) (v : F) : Mm H x (Jb H x v) = Bb H x v := by
  simp [Mm, H.Jinv_Jb x v]

lemma Mm_add (x : E) (v w : F) : Mm H x (v + w) = Mm H x v + Mm H x w := by
  simp [Mm, map_add]

lemma Mm_smul (x : E) (c : ℝ) (v : F) : Mm H x (c • v) = c • Mm H x v := by
  simp [Mm, map_smul]

lemma Mm_sub (x : E) (v w : F) : Mm H x (v - w) = Mm H x v - Mm H x w := by
  simp [Mm, map_sub]

end Hyp

end OracleTemplate.HessianNcsc

namespace OracleTemplate.HessianNcsc

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}

namespace Hyp

variable (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma zs_sq (a b : E) : sq (zs H a - zs H b) ≤ (1 + (L / μ) ^ 2) * ‖a - b‖ ^ 2 := by
  have h := H.ystar_lip a b
  have h2 : ‖ystar H a - ystar H b‖ ^ 2 ≤ (L / μ) ^ 2 * ‖a - b‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [sq, zs, Prod.fst_sub, Prod.snd_sub]
  nlinarith

lemma Gs_lip (a b : E) : ‖Gs H a - Gs H b‖ ≤ L * Real.sqrt (sq (zs H a - zs H b)) := by
  have h := H.gx_lip (zs H a) (zs H b)
  simpa [Gs, sq] using h

lemma Bb_diff (a b : E) (v : F) :
    ‖Bb H a v - Bb H b v‖ ≤ ρ * Real.sqrt (sq (zs H a - zs H b)) * ‖v‖ := by
  have h := H.hessx_diff (zs H a) (zs H b) ((0 : E), v)
  rw [sq_inr, Real.sqrt_sq (norm_nonneg _)] at h
  simpa [Bb, sub_apply] using h

lemma Jb_diff (a b : E) (v : F) :
    ‖Jb H a v - Jb H b v‖ ≤ ρ * Real.sqrt (sq (zs H a - zs H b)) * ‖v‖ := by
  have h := H.hessy_diff (zs H a) (zs H b) ((0 : E), v)
  rw [sq_inr, Real.sqrt_sq (norm_nonneg _)] at h
  simpa [Jb, sub_apply] using h

omit H in
omit [CompleteSpace E] [CompleteSpace F] in
lemma weighted_taylor {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : E × F → V) (Dg : E × F → (E × F →L[ℝ] V))
    (hT : ∀ z d, ‖g (z + d) - g z - Dg z d‖ ≤ ρ * sq d)
    (z1 z2 : E × F) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖(1 - α) • g z1 + α • g z2 - g ((1 - α) • z1 + α • z2)‖ ≤ ρ * (α * (1 - α)) * sq (z1 - z2) := by
  set zb := (1 - α) • z1 + α • z2
  set d1 := α • (z1 - z2)
  set d2 := -((1 - α) • (z1 - z2))
  have e1 : zb + d1 = z1 := by simp only [zb, d1, smul_sub, sub_smul, one_smul]; abel
  have e2 : zb + d2 = z2 := by simp only [zb, d2, smul_sub, sub_smul, one_smul]; abel
  have h1 := hT zb d1
  have h2 := hT zb d2
  rw [e1] at h1
  rw [e2] at h2
  have hs1 : sq d1 = α ^ 2 * sq (z1 - z2) := by simp only [d1]; exact sq_smul α _
  have hs2 : sq d2 = (1 - α) ^ 2 * sq (z1 - z2) := by
    have : sq d2 = sq ((1 - α) • (z1 - z2)) := by simp [d2, sq, norm_neg]
    rw [this, sq_smul]
  rw [hs1] at h1
  rw [hs2] at h2
  have hlin : (1 - α) • Dg zb d1 + α • Dg zb d2 = 0 := by
    simp only [d1, d2, map_neg, map_smul, smul_neg]
    rw [smul_smul, smul_smul, mul_comm]; abel
  have e3 : (1 - α) • g z1 + α • g z2 - g zb =
      (1 - α) • (g z1 - g zb - Dg zb d1) + α • (g z2 - g zb - Dg zb d2) := by
    have : (1 - α) • g z1 + α • g z2 - g zb =
        (1 - α) • (g z1 - g zb - Dg zb d1) + α • (g z2 - g zb - Dg zb d2) +
          ((1 - α) • Dg zb d1 + α • Dg zb d2) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [this, hlin, add_zero]
  rw [e3]
  have ha1 : 0 ≤ 1 - α := by linarith
  calc ‖(1 - α) • (g z1 - g zb - Dg zb d1) + α • (g z2 - g zb - Dg zb d2)‖
      ≤ (1 - α) * ‖g z1 - g zb - Dg zb d1‖ + α * ‖g z2 - g zb - Dg zb d2‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha1, Real.norm_of_nonneg hα0]
    _ ≤ (1 - α) * (ρ * (α ^ 2 * sq (z1 - z2))) + α * (ρ * ((1 - α) ^ 2 * sq (z1 - z2))) := by
        gcongr
    _ = ρ * (α * (1 - α)) * sq (z1 - z2) := by ring

lemma ystar_affine (a c : E) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖ystar H ((1 - α) • a + α • c) - ((1 - α) • ystar H a + α • ystar H c)‖ ≤
      (ρ / μ) * (α * (1 - α)) * sq (zs H a - zs H c) := by
  set p := (1 - α) • a + α • c
  set yb := (1 - α) • ystar H a + α • ystar H c
  have hw := OracleTemplate.HessianNcsc.Hyp.weighted_taylor gy Hy H.taylor_y (zs H a) (zs H c) hα0 hα1
  have hzb : (1 - α) • zs H a + α • zs H c = (p, yb) := by simp [zs, p, yb]
  rw [hzb] at hw
  simp only [zs, H.gy_ystar, smul_zero, add_zero, zero_sub, norm_neg] at hw
  have hm := H.gy_mono p (ystar H p) yb
  rw [H.gy_ystar p, sub_zero] at hm
  have hci : ⟪gy (p, yb), yb - ystar H p⟫ ≥ -(‖gy (p, yb)‖ * ‖yb - ystar H p‖) := by
    have := abs_real_inner_le_norm (gy (p, yb)) (yb - ystar H p)
    linarith [neg_abs_le ⟪gy (p, yb), yb - ystar H p⟫]
  have key : μ * ‖yb - ystar H p‖ ^ 2 ≤ ‖gy (p, yb)‖ * ‖yb - ystar H p‖ := by linarith
  have key2 : μ * ‖yb - ystar H p‖ ≤ ‖gy (p, yb)‖ := by
    by_cases h0 : ‖yb - ystar H p‖ = 0
    · rw [h0, mul_zero]; exact norm_nonneg _
    · have hp : 0 < ‖yb - ystar H p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  rw [norm_sub_rev]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ H.μpos]
  have : ‖gy (p, yb)‖ ≤ ρ * (α * (1 - α)) * sq (zs H a - zs H c) := by simpa [zs] using hw
  nlinarith

lemma Gs_defect (a c : E) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖(1 - α) • Gs H a + α • Gs H c - Gs H ((1 - α) • a + α • c)‖ ≤
      ρ * (1 + L / μ) * (α * (1 - α)) * sq (zs H a - zs H c) := by
  set p := (1 - α) • a + α • c
  set yb := (1 - α) • ystar H a + α • ystar H c
  have hw := OracleTemplate.HessianNcsc.Hyp.weighted_taylor gx Hx H.taylor_x (zs H a) (zs H c) hα0 hα1
  have hzb : (1 - α) • zs H a + α • zs H c = (p, yb) := by simp [zs, p, yb]
  rw [hzb] at hw
  have hy := H.ystar_affine a c hα0 hα1
  have hl := H.gx_lip_y p yb (ystar H p)
  have e : (1 - α) • Gs H a + α • Gs H c - Gs H p =
      ((1 - α) • gx (zs H a) + α • gx (zs H c) - gx (p, yb)) + (gx (p, yb) - gx (p, ystar H p)) := by
    simp [Gs, zs]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hS : 0 ≤ (α * (1 - α)) * sq (zs H a - zs H c) :=
    mul_nonneg (mul_nonneg hα0 (by linarith)) (sq_nonneg' _)
  have h3 : L * ‖yb - ystar H p‖ ≤ L * ((ρ / μ) * (α * (1 - α)) * sq (zs H a - zs H c)) := by
    rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hy H.L_pos.le
  have e4 : ρ * (1 + L / μ) * (α * (1 - α)) * sq (zs H a - zs H c) =
      ρ * (α * (1 - α)) * sq (zs H a - zs H c) + L * ((ρ / μ) * (α * (1 - α)) * sq (zs H a - zs H c)) := by
    field_simp
  rw [e4]
  exact add_le_add hw (hl.trans h3)

end Hyp

namespace Hyp

variable [FiniteDimensional ℝ F] (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma Mm_diff (a b : E) (w : F) :
    ‖Mm H a w - Mm H b w‖ ≤ (ρ / μ) * (1 + L / μ) * Real.sqrt (sq (zs H a - zs H b)) * ‖w‖ := by
  set s := Real.sqrt (sq (zs H a - zs H b))
  set u := (Jinv H a).symm w
  have hu : ‖u‖ ≤ ‖w‖ / μ := H.Jinv_norm a w
  have hwJ : Jb H a u = w := H.Jb_Jinv a w
  have e1 : (Jinv H a).symm w - (Jinv H b).symm w = (Jinv H b).symm (Jb H b u - Jb H a u) := by
    rw [map_sub, H.Jinv_Jb b u, hwJ]
  have e2 : Mm H a w - Mm H b w = (Bb H a u - Bb H b u) + Bb H b ((Jinv H a).symm w - (Jinv H b).symm w) := by
    simp only [Mm, map_sub]; abel
  rw [e2, e1]
  have h1 := H.Bb_diff a b u
  have h2 := H.Bb_norm b ((Jinv H b).symm (Jb H b u - Jb H a u))
  have h3 := H.Jinv_norm b (Jb H b u - Jb H a u)
  have h4 : ‖Jb H b u - Jb H a u‖ ≤ ρ * s * ‖u‖ := by
    rw [norm_sub_rev]; exact H.Jb_diff a b u
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hμ := H.μpos
  have hL := H.L_pos
  have hρ := H.ρnn
  calc ‖(Bb H a u - Bb H b u) + Bb H b ((Jinv H b).symm (Jb H b u - Jb H a u))‖
      ≤ ρ * s * ‖u‖ + L * (‖Jb H b u - Jb H a u‖ / μ) := by
        refine (norm_add_le _ _).trans (add_le_add h1 (h2.trans ?_))
        exact mul_le_mul_of_nonneg_left h3 hL.le
    _ ≤ ρ * s * ‖u‖ + L * (ρ * s * ‖u‖ / μ) := by gcongr
    _ = (ρ * s * ‖u‖) * (1 + L / μ) := by field_simp
    _ ≤ (ρ * s * (‖w‖ / μ)) * (1 + L / μ) := by gcongr
    _ = (ρ / μ) * (1 + L / μ) * s * ‖w‖ := by field_simp

lemma mismatch (p q : E) (v : F) :
    ‖Bb H p v - Mm H q (Jb H p v)‖ ≤ ρ * (1 + L / μ) * Real.sqrt (sq (zs H p - zs H q)) * ‖v‖ := by
  set s := Real.sqrt (sq (zs H p - zs H q))
  have e : Bb H p v - Mm H q (Jb H p v) = (Bb H p v - Bb H q v) - Mm H q (Jb H p v - Jb H q v) := by
    rw [H.Mm_sub, H.Mm_Jb]; abel
  rw [e]
  have h1 := H.Bb_diff p q v
  have h2 := H.Mm_norm q (Jb H p v - Jb H q v)
  have h3 := H.Jb_diff p q v
  have hμ := H.μpos
  have hL := H.L_pos
  calc ‖(Bb H p v - Bb H q v) - Mm H q (Jb H p v - Jb H q v)‖
      ≤ ρ * s * ‖v‖ + (L / μ) * (ρ * s * ‖v‖) := by
        refine (norm_sub_le _ _).trans (add_le_add h1 (h2.trans ?_))
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ρ * (1 + L / μ) * s * ‖v‖ := by ring

end Hyp

end OracleTemplate.HessianNcsc
