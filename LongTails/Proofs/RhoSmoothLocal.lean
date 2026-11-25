import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped RealInnerProductSpace

namespace LongTails.Proofs.RhoSmoothLocal

noncomputable def curv (L0 L1 ρ s : ℝ) : ℝ := L0 + L1 * s ^ ρ

lemma curv_pos {L0 L1 ρ : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) {s : ℝ} (hs : 0 ≤ s) :
    0 < curv L0 L1 ρ s := by
  unfold curv
  have := Real.rpow_nonneg hs ρ
  positivity

lemma curv_mono {L0 L1 ρ : ℝ} (hL1 : 0 ≤ L1) (hρ : 0 ≤ ρ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    curv L0 L1 ρ s ≤ curv L0 L1 ρ t := by
  unfold curv
  have := Real.rpow_le_rpow hs hst hρ
  nlinarith

structure Hyp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (L0 L1 ρ : ℝ) : Prop where
  L0_pos : 0 < L0
  L1_pos : 0 < L1
  ρ_nonneg : 0 ≤ ρ
  convex : ConvexOn ℝ Set.univ f
  grad : ∀ x, HasGradientAt f (g x) x
  diff : Differentiable ℝ g
  hess : ∀ x, ‖fderiv ℝ g x‖ ≤ curv L0 L1 ρ ‖g x‖

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {g : E → E} {L0 L1 ρ : ℝ}

lemma segment_bound (H : Hyp f g L0 L1 ρ) (x v : E) {a : ℝ} (ha : 0 < a) (hx : ‖g x‖ ≤ a)
    (hv : 2 * curv L0 L1 ρ (2 * a) * ‖v‖ ≤ a) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g (x + t • v) - g x‖ ≤ t * (2 * curv L0 L1 ρ (2 * a) * ‖v‖) := by
  set C := 2 * curv L0 L1 ρ (2 * a) * ‖v‖ with hC
  have hcpos : 0 < curv L0 L1 ρ (2 * a) := curv_pos H.L0_pos H.L1_pos.le (by linarith)
  by_cases hv0 : v = 0
  · intro t _
    subst hv0
    simp [hC]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let c : ℝ → E := fun t => x + t • v
  have hc (t : ℝ) : HasDerivAt c v t := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    simpa [c] using h1.const_add x
  let G : ℝ → E := fun t => g (c t)
  have hG (t : ℝ) : HasDerivAt G (fderiv ℝ g (c t) v) t :=
    (H.diff (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * C) C t := by
    intro t
    simpa using (hasDerivAt_id t).mul_const C
  refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary
    (f := fun t => G t - g x) (f' := fun t => fderiv ℝ g (c t) v)
    (B := fun t => t * C) (B' := fun _ => C) ?_ ?_ ?_ hB ?_
  · exact (continuous_iff_continuousAt.mpr fun t => ((hG t).sub_const (g x)).continuousAt).continuousOn
  · intro t _
    exact ((hG t).sub_const (g x)).hasDerivWithinAt
  · simp [G, c]
  · intro t ht heq
    have hGle : ‖G t‖ ≤ 2 * a := by
      have h1 : ‖G t‖ ≤ ‖G t - g x‖ + ‖g x‖ := by
        have := norm_add_le (G t - g x) (g x)
        simpa using this
      have h2 : t * C ≤ C := by
        have : 0 ≤ C := by positivity
        nlinarith [ht.1, ht.2]
      have h3 : ‖G t - g x‖ = t * C := heq
      linarith
    have h3 : ‖fderiv ℝ g (c t)‖ ≤ curv L0 L1 ρ (2 * a) :=
      (H.hess (c t)).trans (curv_mono H.L1_pos.le H.ρ_nonneg (norm_nonneg _) hGle)
    have h4 : ‖fderiv ℝ g (c t) v‖ ≤ curv L0 L1 ρ (2 * a) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg v))
    have h5 : curv L0 L1 ρ (2 * a) * ‖v‖ < C := by
      rw [hC]
      have : 0 < curv L0 L1 ρ (2 * a) * ‖v‖ := by positivity
      linarith
    linarith

lemma segment_norm (H : Hyp f g L0 L1 ρ) (x v : E) {a : ℝ} (ha : 0 < a) (hx : ‖g x‖ ≤ a)
    (hv : 2 * curv L0 L1 ρ (2 * a) * ‖v‖ ≤ a) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖g (x + t • v)‖ ≤ 2 * a := by
  have h := segment_bound H x v ha hx hv t ht
  have h1 : ‖g (x + t • v)‖ ≤ ‖g (x + t • v) - g x‖ + ‖g x‖ := by
    have := norm_add_le (g (x + t • v) - g x) (g x)
    simpa using this
  have h2 : t * (2 * curv L0 L1 ρ (2 * a) * ‖v‖) ≤ a := by
    have : 0 ≤ 2 * curv L0 L1 ρ (2 * a) * ‖v‖ := by
      have := curv_pos (ρ := ρ) H.L0_pos H.L1_pos.le (show (0 : ℝ) ≤ 2 * a by linarith)
      positivity
    nlinarith [ht.1, ht.2]
  linarith

lemma upper (H : Hyp f g L0 L1 ρ) (x v : E) {a : ℝ} (ha : 0 < a) (hx : ‖g x‖ ≤ a)
    (hv : 2 * curv L0 L1 ρ (2 * a) * ‖v‖ ≤ a) :
    f (x + v) ≤ f x + ⟪g x, v⟫ + curv L0 L1 ρ (2 * a) * ‖v‖ ^ 2 := by
  set C := 2 * curv L0 L1 ρ (2 * a) * ‖v‖ with hC
  have hfence := segment_bound H x v ha hx hv
  let c : ℝ → E := fun t => x + t • v
  have hc (t : ℝ) : HasDerivAt c v t := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    simpa [c] using h1.const_add x
  have hfc (t : ℝ) : HasDerivAt (fun t => f (c t)) ⟪g (c t), v⟫ t := by
    have h := (H.grad (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)
    refine h.congr_deriv ?_
    rfl
  let φ : ℝ → ℝ := fun t => f (c t) - t * ⟪g x, v⟫ - C * ‖v‖ * t ^ 2 / 2
  have hφ (t : ℝ) : HasDerivAt φ (⟪g (c t), v⟫ - ⟪g x, v⟫ - C * ‖v‖ * t) t := by
    have h1 : HasDerivAt (fun t : ℝ => t * ⟪g x, v⟫) ⟪g x, v⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪g x, v⟫
    have h2 : HasDerivAt (fun t : ℝ => C * ‖v‖ * t ^ 2 / 2) (C * ‖v‖ * t) t := by
      have h := ((hasDerivAt_pow 2 t).const_mul (C * ‖v‖)).div_const 2
      refine h.congr_deriv ?_
      simp only [Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, pow_one]
      ring
    exact ((hfc t).sub h1).sub h2
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr fun t => (hφ t).continuousAt).continuousOn
    · exact fun t _ => (hφ t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφ t).deriv]
      have hf := hfence t ⟨ht.1.le, ht.2.le⟩
      have e : ⟪g (c t), v⟫ - ⟪g x, v⟫ = ⟪g (c t) - g x, v⟫ := by rw [inner_sub_left]
      have hcs : ⟪g (c t) - g x, v⟫ ≤ ‖g (c t) - g x‖ * ‖v‖ := real_inner_le_norm _ _
      have h7 : ‖g (c t) - g x‖ * ‖v‖ ≤ t * C * ‖v‖ :=
        mul_le_mul_of_nonneg_right hf (norm_nonneg v)
      rw [e]
      nlinarith
  have h01 := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  have e0 : φ 0 = f x := by simp [φ, c]
  have e1 : φ 1 = f (x + v) - ⟪g x, v⟫ - C * ‖v‖ / 2 := by
    simp only [φ, c, one_smul, one_mul, one_pow, mul_one]
  rw [e0, e1] at h01
  have e2 : C * ‖v‖ / 2 = curv L0 L1 ρ (2 * a) * ‖v‖ ^ 2 := by rw [hC]; ring
  linarith

lemma convex_lower (H : Hyp f g L0 L1 ρ) (x y : E) : f x + ⟪g x, y - x⟫ ≤ f y := by
  have hconv := H.convex.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) (g x))
      ((AffineMap.lineMap x y) (0 : ℝ)) := by
    simpa using (H.grad x).hasFDerivAt
  have hline : HasDerivAt (f ∘ AffineMap.lineMap x y) ⟪g x, y - x⟫ (0 : ℝ) := by
    simpa using hd.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have h := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simp) (by simp) (by norm_num) hline
  have h2 : ⟪g x, y - x⟫ ≤ f y - f x := by simpa [slope_def_field] using h
  linarith

lemma gradient_zero (H : Hyp f g L0 L1 ρ) {u : E} (hu : IsMinOn f Set.univ u) : g u = 0 := by
  have hloc : IsLocalMin f u := hu.isLocalMin Filter.univ_mem
  have h := hloc.hasFDerivAt_eq_zero (H.grad u).hasFDerivAt
  simpa using h

lemma gap_lower (H : Hyp f g L0 L1 ρ) {u : E} (hu : IsMinOn f Set.univ u) (y : E) :
    3 * ‖g y‖ ^ 2 / (16 * curv L0 L1 ρ (2 * ‖g y‖)) ≤ f y - f u := by
  by_cases hg0 : g y = 0
  · have : f u ≤ f y := hu (Set.mem_univ y)
    simp [hg0]
    linarith
  set a := ‖g y‖ with ha
  have hapos : 0 < a := norm_pos_iff.mpr hg0
  have hcpos : 0 < curv L0 L1 ρ (2 * a) := curv_pos H.L0_pos H.L1_pos.le (by linarith)
  set K := curv L0 L1 ρ (2 * a)
  set v : E := -(1 / (4 * K)) • g y with hvdef
  have hvn : ‖v‖ = a / (4 * K) := by
    rw [hvdef, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity), ← ha]
    field_simp
  have hv : 2 * K * ‖v‖ ≤ a := by
    rw [hvn]
    have : 2 * K * (a / (4 * K)) = a / 2 := by field_simp; ring
    linarith
  have hup := upper H y v hapos le_rfl hv
  have hinner : ⟪g y, v⟫ = -(a ^ 2 / (4 * K)) := by
    rw [hvdef, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hmin : f u ≤ f (y + v) := hu (Set.mem_univ _)
  rw [hinner, hvn] at hup
  have e : K * (a / (4 * K)) ^ 2 = a ^ 2 / (16 * K) := by field_simp; ring
  rw [e] at hup
  have e2 : 3 * a ^ 2 / (16 * K) = a ^ 2 / (4 * K) - a ^ 2 / (16 * K) := by field_simp; ring
  rw [e2]
  linarith

lemma growth (H : Hyp f g L0 L1 ρ) {u : E} (hu : IsMinOn f Set.univ u) (v : E) {a : ℝ}
    (ha : 0 < a) (hv : 2 * curv L0 L1 ρ (2 * a) * ‖v‖ ≤ a) :
    f (u + v) ≤ f u + curv L0 L1 ρ (2 * a) * ‖v‖ ^ 2 := by
  have h0 := gradient_zero H hu
  have h := upper H u v ha (by rw [h0, norm_zero]; exact ha.le) hv
  rw [h0, inner_zero_left, add_zero] at h
  exact h

lemma deep_cut (H : Hyp f g L0 L1 ρ) {u : E} (hu : IsMinOn f Set.univ u) (y : E) {G : ℝ}
    (hG : 0 < G) (hy : G ≤ ‖g y‖) :
    G / (4 * curv L0 L1 ρ (2 * G)) * ‖g y‖ ≤ ⟪g y, y - u⟫ := by
  set K := curv L0 L1 ρ (2 * G)
  have hK : 0 < K := curv_pos H.L0_pos H.L1_pos.le (by linarith)
  have hgpos : 0 < ‖g y‖ := lt_of_lt_of_le hG hy
  set t := G / (2 * K) with htdef
  have htpos : 0 < t := by positivity
  set v : E := (t / ‖g y‖) • g y with hvdef
  have hvn : ‖v‖ = t := by
    rw [hvdef, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hv : 2 * K * ‖v‖ ≤ G := by
    rw [hvn, htdef]
    have : 2 * K * (G / (2 * K)) = G := by field_simp
    linarith
  have hgrow := growth H hu v hG hv
  have hconv := convex_lower H y (u + v)
  have hmin : f u ≤ f y := hu (Set.mem_univ y)
  have hinner : ⟪g y, u + v - y⟫ = ⟪g y, u - y⟫ + t * ‖g y‖ := by
    have e : u + v - y = (u - y) + v := by abel
    rw [e, inner_add_right, hvdef, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [hinner] at hconv
  rw [hvn] at hgrow
  have hsym : ⟪g y, y - u⟫ = -⟪g y, u - y⟫ := by
    rw [← inner_neg_right, neg_sub]
  have hKt : K * t ^ 2 = t * (G / 2) := by rw [htdef]; field_simp
  have key : t * ‖g y‖ - t * (G / 2) ≤ ⟪g y, y - u⟫ := by nlinarith
  have hfin : G / (4 * K) * ‖g y‖ = t * ‖g y‖ / 2 := by rw [htdef]; field_simp; ring
  rw [hfin]
  nlinarith

lemma deep_cut_step (H : Hyp f g L0 L1 ρ) {u : E} (hu : IsMinOn f Set.univ u) (y : E) {G : ℝ}
    (hG : 0 < G) (hy : G ≤ ‖g y‖) :
    ‖(y - (G / (4 * curv L0 L1 ρ (2 * G)) / ‖g y‖) • g y) - u‖ ^ 2 ≤
      ‖y - u‖ ^ 2 - (G / (4 * curv L0 L1 ρ (2 * G))) ^ 2 := by
  set D := G / (4 * curv L0 L1 ρ (2 * G))
  have hgpos : 0 < ‖g y‖ := lt_of_lt_of_le hG hy
  have hcut := deep_cut H hu y hG hy
  have e : (y - (D / ‖g y‖) • g y) - u = (y - u) - (D / ‖g y‖) • g y := by abel
  rw [e, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg (by
    have : 0 < curv L0 L1 ρ (2 * G) := curv_pos H.L0_pos H.L1_pos.le (by linarith)
    positivity)]
  have h1 : D / ‖g y‖ * ‖g y‖ = D := by field_simp
  rw [real_inner_comm, mul_pow, show (D / ‖g y‖) ^ 2 * ‖g y‖ ^ 2 = (D / ‖g y‖ * ‖g y‖) ^ 2 by ring, h1]
  have h2 : D * ‖g y‖ ≤ ⟪g y, y - u⟫ := hcut
  have h3 : 2 * (D / ‖g y‖ * ⟪g y, y - u⟫) ≥ 2 * D ^ 2 := by
    have hDn : 0 ≤ D / ‖g y‖ := by
      have : 0 < curv L0 L1 ρ (2 * G) := curv_pos H.L0_pos H.L1_pos.le (by linarith)
      positivity
    have := mul_le_mul_of_nonneg_left h2 hDn
    have e3 : D / ‖g y‖ * (D * ‖g y‖) = D ^ 2 := by field_simp
    linarith
  linarith

lemma cocoercive (H : Hyp f g L0 L1 ρ) (y z : E) {b : ℝ} (hb : 0 < b) (hy : ‖g y‖ ≤ b)
    (hz : ‖g z‖ ≤ b) :
    f z + ⟪g z, y - z⟫ + 3 / (16 * curv L0 L1 ρ (2 * b)) * ‖g y - g z‖ ^ 2 ≤ f y := by
  set K := curv L0 L1 ρ (2 * b)
  have hK : 0 < K := curv_pos H.L0_pos H.L1_pos.le (by linarith)
  set w := g y - g z with hw
  have hwn : ‖w‖ ≤ 2 * b := by
    have := norm_sub_le (g y) (g z)
    linarith
  set v : E := -(1 / (4 * K)) • w with hvdef
  have hvn : ‖v‖ = ‖w‖ / (4 * K) := by
    rw [hvdef, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    field_simp
  have hv : 2 * K * ‖v‖ ≤ b := by
    rw [hvn]
    have e : 2 * K * (‖w‖ / (4 * K)) = ‖w‖ / 2 := by field_simp; ring
    rw [e]
    linarith
  have hup := upper H y v hb hy hv
  have hconv := convex_lower H z (y + v)
  have hinner : ⟪g y, v⟫ - ⟪g z, v⟫ = -(‖w‖ ^ 2 / (4 * K)) := by
    rw [← inner_sub_left, ← hw, hvdef, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hzv : ⟪g z, y + v - z⟫ = ⟪g z, y - z⟫ + ⟪g z, v⟫ := by
    rw [show y + v - z = (y - z) + v by abel, inner_add_right]
  rw [hzv] at hconv
  rw [hvn] at hup
  have e : K * (‖w‖ / (4 * K)) ^ 2 = ‖w‖ ^ 2 / (16 * K) := by field_simp; ring
  rw [e] at hup
  have e2 : 3 / (16 * K) * ‖w‖ ^ 2 = ‖w‖ ^ 2 / (4 * K) - ‖w‖ ^ 2 / (16 * K) := by
    field_simp; ring
  rw [e2]
  linarith

end LongTails.Proofs.RhoSmoothLocal
