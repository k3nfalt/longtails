import LongTails.Proofs.RhoSmoothLocal
import LongTails.Proofs.CompactConjugate
import LongTails.Proofs.GeneralizedSmoothHardDual
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set
open scoped RealInnerProductSpace Topology

namespace LongTails.Proofs.RhoSmoothHardDual

open LongTails.Proofs.RhoSmoothLocal CompactConjugate
open GeneralizedSmoothHardDual (feasible feasible_zero)

noncomputable def slope (A G ρ r : ℝ) : ℝ := A * (1 - (1 + max r 0 / G) ^ (1 - ρ))

noncomputable def penalty (A G ρ r : ℝ) : ℝ := ∫ t in (0 : ℝ)..r, slope A G ρ t

noncomputable def dual {m : ℕ} (A G ρ : ℝ) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ i, penalty A G ρ (z i)

lemma power_sum_le (ρ s : ℝ) (hρ : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hs : 0 ≤ s) :
    (1 + s) ^ ρ ≤ 2 * (1 + s ^ ρ) := by
  have hc := (convexOn_rpow hρ).2 (show (1 : ℝ) ∈ Ici 0 by simp) (show s ∈ Ici 0 from hs)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, Real.one_rpow] at hc
  have he : (1 / 2 : ℝ) * 1 + 1 / 2 * s = (1 + s) / 2 := by ring
  rw [he, Real.div_rpow (by linarith) (by norm_num)] at hc
  have h2 : (2 : ℝ) ^ ρ ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hρ2
    norm_num at this
    linarith
  have h2p : 0 < (2 : ℝ) ^ ρ := by positivity
  have hp : 0 ≤ (1 + s) ^ ρ := Real.rpow_nonneg (by linarith) _
  rw [div_le_iff₀ h2p] at hc
  nlinarith [Real.rpow_nonneg hs ρ]

section

variable (A G ρ : ℝ) (hA : 0 < A) (hG : 0 < G) (hρ : 1 < ρ)

include hA hG hρ

omit hA hρ in
lemma slope_continuous : Continuous (slope A G ρ) := by
  unfold slope
  apply continuous_const.mul
  apply continuous_const.sub
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    left
    have : 0 ≤ max x 0 / G := div_nonneg (le_max_right _ _) hG.le
    linarith

omit hA hρ in
lemma base_ge_one (r : ℝ) : 1 ≤ 1 + max r 0 / G := by
  have : 0 ≤ max r 0 / G := div_nonneg (le_max_right _ _) hG.le
  linarith

lemma slope_nonneg (r : ℝ) : 0 ≤ slope A G ρ r := by
  unfold slope
  have h := Real.rpow_le_one_of_one_le_of_nonpos (base_ge_one G hG r) (show 1 - ρ ≤ 0 by linarith)
  have : 0 ≤ 1 - (1 + max r 0 / G) ^ (1 - ρ) := by linarith
  positivity

omit hρ in
lemma slope_le (r : ℝ) : slope A G ρ r ≤ A := by
  unfold slope
  have h : 0 ≤ (1 + max r 0 / G) ^ (1 - ρ) :=
    Real.rpow_nonneg (by linarith [base_ge_one G hG r]) _
  nlinarith

omit hρ in
lemma slope_hasDerivAt (r : ℝ) (hr : 0 < r) :
    HasDerivAt (slope A G ρ) (A * (ρ - 1) / G * (1 + r / G) ^ (-ρ)) r := by
  have hb : 0 < 1 + r / G := by have := div_pos hr hG; linarith
  have h1 : HasDerivAt (fun y : ℝ => 1 + y / G) (1 / G) r := by
    simpa using ((hasDerivAt_id r).div_const G).const_add 1
  have h2 := h1.rpow_const (p := 1 - ρ) (Or.inl hb.ne')
  have h3 := (h2.const_sub 1).const_mul A
  have he : slope A G ρ =ᶠ[𝓝 r] fun y => A * (1 - (1 + y / G) ^ (1 - ρ)) := by
    filter_upwards [eventually_gt_nhds hr] with y hy
    simp only [slope, max_eq_left hy.le]
  refine (h3.congr_of_eventuallyEq he).congr_deriv ?_
  have hx : (1 - ρ - 1 : ℝ) = -ρ := by ring
  rw [hx]
  field_simp
  ring

omit hA in
lemma slope_deriv_lower (L₀ L₁ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hρ2 : ρ ≤ 2)
    (hAG : A * (ρ - 1) = 2 * G / L₀) (hGL : G ^ ρ * L₁ = L₀) (r T : ℝ) (hr : 0 ≤ r)
    (hrT : r ≤ T) :
    1 / curv L₀ L₁ ρ T ≤ A * (ρ - 1) / G * (1 + r / G) ^ (-ρ) := by
  have hs : 0 ≤ r / G := div_nonneg hr hG.le
  have hb : 0 < 1 + r / G := by linarith
  have hp := power_sum_le ρ (r / G) hρ.le hρ2 hs
  have hpos : 0 < (1 + r / G) ^ ρ := Real.rpow_pos_of_pos hb _
  rw [hAG, Real.rpow_neg hb.le]
  have hcurv : L₀ * (1 + (r / G) ^ ρ) ≤ curv L₀ L₁ ρ T := by
    unfold curv
    rw [Real.div_rpow hr hG.le]
    have hGρ : 0 < G ^ ρ := Real.rpow_pos_of_pos hG _
    have hrT' : r ^ ρ ≤ T ^ ρ := Real.rpow_le_rpow hr hrT (by linarith)
    have e : L₀ * (1 + r ^ ρ / G ^ ρ) = L₀ + L₁ * r ^ ρ := by
      rw [← hGL]; field_simp
    rw [e]
    nlinarith
  have hc : 0 < curv L₀ L₁ ρ T := by
    have := hcurv
    have : 0 < L₀ * (1 + (r / G) ^ ρ) := by
      have := Real.rpow_nonneg hs ρ
      positivity
    linarith
  rw [div_le_iff₀ hc]
  have e : 2 * G / L₀ / G * ((1 + r / G) ^ ρ)⁻¹ * curv L₀ L₁ ρ T =
      2 * curv L₀ L₁ ρ T / (L₀ * (1 + r / G) ^ ρ) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith

omit hA hρ in
lemma penalty_hasDerivAt (r : ℝ) : HasDerivAt (penalty A G ρ) (slope A G ρ r) r :=
  ((slope_continuous A G ρ hG).integral_hasStrictDerivAt 0 r).hasDerivAt

omit hA hρ in
lemma penalty_differentiable : Differentiable ℝ (penalty A G ρ) :=
  fun r => (penalty_hasDerivAt A G ρ hG r).differentiableAt

omit hA hρ in
lemma penalty_continuous : Continuous (penalty A G ρ) :=
  (penalty_differentiable A G ρ hG).continuous

omit hA hG hρ in
lemma penalty_zero : penalty A G ρ 0 = 0 := by simp [penalty]

lemma penalty_monotone : Monotone (penalty A G ρ) := by
  apply monotone_of_deriv_nonneg (penalty_differentiable A G ρ hG)
  intro r
  rw [(penalty_hasDerivAt A G ρ hG r).deriv]
  exact slope_nonneg A G ρ hA hG hρ r

omit hρ in
lemma penalty_sub_le {a b : ℝ} (hab : a ≤ b) :
    penalty A G ρ b - penalty A G ρ a ≤ A * (b - a) := by
  have hm : Monotone (fun r => A * r - penalty A G ρ r) := by
    apply monotone_of_deriv_nonneg
    · exact ((differentiable_id.const_mul A)).sub (penalty_differentiable A G ρ hG)
    · intro r
      have hd : HasDerivAt (fun r => A * r - penalty A G ρ r) (A * 1 - slope A G ρ r) r :=
        ((hasDerivAt_id r).const_mul A).sub (penalty_hasDerivAt A G ρ hG r)
      rw [hd.deriv]
      have := slope_le A G ρ hA hG r
      simp only [mul_one]
      linarith
  have := hm hab
  simp only at this
  linarith

lemma penalty_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ penalty A G ρ r := by
  have := penalty_monotone A G ρ hA hG hρ hr
  rwa [penalty_zero] at this

omit hρ in
lemma penalty_le {r : ℝ} (hr : 0 ≤ r) : penalty A G ρ r ≤ A * r := by
  have := penalty_sub_le A G ρ hA hG hr
  rwa [penalty_zero, sub_zero, sub_zero] at this

lemma penalty_segment (L₀ L₁ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hρ2 : ρ ≤ 2)
    (hAG : A * (ρ - 1) = 2 * G / L₀) (hGL : G ^ ρ * L₁ = L₀) (a b T : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haT : a ≤ T) (hbT : b ≤ T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    penalty A G ρ ((1 - t) * a + t * b) ≤
      (1 - t) * penalty A G ρ a + t * penalty A G ρ b -
        (b - a) ^ 2 / (2 * curv L₀ L₁ ρ T) * t * (1 - t) := by
  by_cases hab : a = b
  · subst hab
    have e : (1 - t) * a + t * a = a := by ring
    rw [e]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      zero_mul, sub_zero]
    ring_nf
    exact le_rfl
  have hpos (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < a + s * (b - a) := by
    rcases lt_or_gt_of_ne hab with h | h
    · nlinarith [hs.1, hs.2]
    · nlinarith [hs.1, hs.2]
  have hc : 0 < curv L₀ L₁ ρ T := curv_pos hL₀ hL₁.le (ha.trans haT)
  have key := strong_segment_of_second_derivative
    (fun s => penalty A G ρ (a + s * (b - a)))
    (fun s => slope A G ρ (a + s * (b - a)) * (b - a))
    (fun s => A * (ρ - 1) / G * (1 + (a + s * (b - a)) / G) ^ (-ρ) * (b - a) ^ 2)
    ((b - a) ^ 2 / curv L₀ L₁ ρ T)
    ((penalty_continuous A G ρ hG).comp (by fun_prop)).continuousOn
    (fun s _ => by
      have h1 : HasDerivAt (fun s : ℝ => a + s * (b - a)) (b - a) s := by
        simpa using ((hasDerivAt_id s).mul_const (b - a)).const_add a
      exact (penalty_hasDerivAt A G ρ hG _).comp s h1)
    (fun s hs => by
      have h1 : HasDerivAt (fun s : ℝ => a + s * (b - a)) (b - a) s := by
        simpa using ((hasDerivAt_id s).mul_const (b - a)).const_add a
      have h2 := ((slope_hasDerivAt A G ρ hA hG _ (hpos s hs)).comp s h1).mul_const (b - a)
      refine h2.congr_deriv ?_
      ring)
    (fun s hs => by
      have hl := slope_deriv_lower A G ρ hG hρ L₀ L₁ hL₀ hL₁ hρ2 hAG hGL (a + s * (b - a)) T
        (hpos s hs).le (by nlinarith [hs.1, hs.2])
      rw [div_eq_mul_one_div ((b - a) ^ 2)]
      have hsq : 0 ≤ (b - a) ^ 2 := sq_nonneg _
      nlinarith)
    t ht
  have e1 : a + t * (b - a) = (1 - t) * a + t * b := by ring
  have e0 : a + 0 * (b - a) = a := by ring
  have e2 : a + 1 * (b - a) = b := by ring
  simp only [e1, e0, e2] at key
  have e3 : (b - a) ^ 2 / curv L₀ L₁ ρ T / 2 * t * (1 - t) =
      (b - a) ^ 2 / (2 * curv L₀ L₁ ρ T) * t * (1 - t) := by
    field_simp
  linarith

end

lemma feasible_segment {m : ℕ} (W : Fin m → ℝ) (hW : ∀ i, 0 < W i)
    (u v : EuclideanSpace ℝ (Fin m)) (hu : u ∈ feasible W) (hv : v ∈ feasible W)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (1 - t) • u + t • v ∈ feasible W := by
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  refine ⟨fun i => ?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith [hu.1 i, hv.1 i, ht.1]
  · have he : ∑ i, ((1 - t) • u + t • v) i / W i =
        (1 - t) * ∑ i, u i / W i + t * ∑ i, v i / W i := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hW i).ne']
    rw [he]
    nlinarith [hu.2, hv.2, ht.1]

section

variable {m : ℕ} (A G ρ L₀ L₁ : ℝ) (hA : 0 < A) (hG : 0 < G) (hρ : 1 < ρ) (hρ2 : ρ ≤ 2)
  (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hAG : A * (ρ - 1) = 2 * G / L₀) (hGL : G ^ ρ * L₁ = L₀)

omit hA hρ in
include hG in
lemma dual_continuous : Continuous (dual (m := m) A G ρ) := by
  unfold dual
  exact continuous_finsetSum _ (fun i _ => (penalty_continuous A G ρ hG).comp (by fun_prop))

include hA hG hρ hρ2 hL₀ hL₁ hAG hGL in
lemma dual_segment (u v : EuclideanSpace ℝ (Fin m)) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (T : ℝ) (huT : ‖u‖ ≤ T) (hvT : ‖v‖ ≤ T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    dual A G ρ ((1 - t) • u + t • v) ≤ (1 - t) * dual A G ρ u + t * dual A G ρ v -
      ‖u - v‖ ^ 2 / (2 * curv L₀ L₁ ρ T) * t * (1 - t) := by
  have hcoord (i : Fin m) := penalty_segment A G ρ hA hG hρ L₀ L₁ hL₀ hL₁ hρ2 hAG hGL (u i) (v i) T
    (hu i) (hv i) ((le_abs_self _).trans ((PiLp.norm_apply_le u i).trans huT))
    ((le_abs_self _).trans ((PiLp.norm_apply_le v i).trans hvT)) t ht
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
  have hn : ‖u - v‖ ^ 2 = ∑ i, (v i - u i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [PiLp.sub_apply]
    ring
  unfold dual
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hn, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact hs

include hA hG hρ hρ2 hL₀ hL₁ hAG hGL in
lemma dual_growth (W : Fin m → ℝ) (hW : ∀ i, 0 < W i) (a u v : EuclideanSpace ℝ (Fin m))
    (hu : u ∈ feasible W) (hv : v ∈ feasible W)
    (hopt : IsMaxOn (fun w => ⟪a, w⟫ - dual A G ρ w) (feasible W) u) :
    ⟪a, v⟫ - dual A G ρ v + ‖u - v‖ ^ 2 / (2 * curv L₀ L₁ ρ (max ‖u‖ ‖v‖)) ≤
      ⟪a, u⟫ - dual A G ρ u := by
  apply maximizer_growth_of_segment
  · intro t ht
    have h := dual_segment A G ρ L₀ L₁ hA hG hρ hρ2 hL₀ hL₁ hAG hGL u v hu.1 hv.1 (max ‖u‖ ‖v‖)
      (le_max_left _ _) (le_max_right _ _) t ht
    linarith
  · intro t ht
    exact hopt (feasible_segment W hW u v hu hv t ht)

end

end LongTails.Proofs.RhoSmoothHardDual
