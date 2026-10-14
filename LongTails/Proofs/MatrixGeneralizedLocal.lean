import LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact

open Set Filter InnerProductSpace
open scoped RealInnerProductSpace Topology

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

variable {d : ℕ}

structure Geometry (H : Point d →L[ℝ] Point d) : Prop where
  symm : ∀ v w, ⟪H v, w⟫ = ⟪v, H w⟫
  coercive : ∃ μ, 0 < μ ∧ ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪H v, v⟫
  upper : ∀ v, ⟪H v, v⟫ ≤ ‖v‖ ^ 2

noncomputable def hnorm (H : Point d →L[ℝ] Point d) (v : Point d) : ℝ :=
  Real.sqrt ⟪H v, v⟫

section Geometry

variable {H : Point d →L[ℝ] Point d} (hG : Geometry H)
include hG

lemma quad_nonneg (v : Point d) : 0 ≤ ⟪H v, v⟫ := by
  obtain ⟨μ, hμ, h⟩ := hG.coercive
  exact (mul_nonneg hμ.le (sq_nonneg _)).trans (h v)

lemma hnorm_sq (v : Point d) : hnorm H v ^ 2 = ⟪H v, v⟫ :=
  Real.sq_sqrt (quad_nonneg hG v)

omit hG in
lemma hnorm_nonneg' (v : Point d) : 0 ≤ hnorm H v := Real.sqrt_nonneg _

lemma hnorm_le_norm (v : Point d) : hnorm H v ≤ ‖v‖ := by
  rw [hnorm, Real.sqrt_le_left (norm_nonneg _)]
  exact hG.upper v

lemma eq_zero_of_quad (v : Point d) (h : ⟪H v, v⟫ = 0) : v = 0 := by
  obtain ⟨μ, hμ, hc⟩ := hG.coercive
  have h1 := hc v
  rw [h] at h1
  have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])

omit hG in
lemma quad_smul (c : ℝ) (v : Point d) : ⟪H (c • v), c • v⟫ = c ^ 2 * ⟪H v, v⟫ := by
  rw [ContinuousLinearMap.map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

lemma quad_add (v w : Point d) :
    ⟪H (v + w), v + w⟫ = ⟪H v, v⟫ + 2 * ⟪H v, w⟫ + ⟪H w, w⟫ := by
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hG.symm w v,
    real_inner_comm (H v) w]
  ring

lemma inner_H_sq_le (v w : Point d) : ⟪H v, w⟫ ^ 2 ≤ ⟪H v, v⟫ * ⟪H w, w⟫ := by
  by_cases hv : ⟪H v, v⟫ = 0
  · rw [eq_zero_of_quad hG v hv]
    simp
  · have ha : 0 < ⟪H v, v⟫ := lt_of_le_of_ne (quad_nonneg hG v) (Ne.symm hv)
    set a := ⟪H v, v⟫
    set b := ⟪H v, w⟫
    set c := ⟪H w, w⟫
    set t := b / a
    have h := quad_nonneg hG ((-t) • v + w)
    rw [quad_add hG, quad_smul , ContinuousLinearMap.map_smul, real_inner_smul_left] at h
    have ht : t * a = b := div_mul_cancel₀ _ (ne_of_gt ha)
    have h2 : 0 ≤ c - t * b := by
      have e1 : (-t) ^ 2 * a = t * b := by rw [neg_sq, sq, mul_assoc, ht]
      nlinarith
    have h3 : 0 ≤ a * (c - t * b) := mul_nonneg ha.le h2
    have h4 : a * (t * b) = b * b := by rw [← mul_assoc, mul_comm a t, ht]
    nlinarith

lemma inner_H_le (v w : Point d) : ⟪H v, w⟫ ≤ hnorm H v * hnorm H w := by
  have h := inner_H_sq_le hG v w
  have h' : |⟪H v, w⟫| ≤ hnorm H v * hnorm H w := by
    rw [hnorm, hnorm, ← Real.sqrt_mul (quad_nonneg hG v)]
    exact Real.abs_le_sqrt h
  exact (le_abs_self _).trans h'

omit hG in
lemma hnorm_smul (c : ℝ) (v : Point d) : hnorm H (c • v) = |c| * hnorm H v := by
  rw [hnorm, quad_smul , Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rfl

omit hG in
lemma hnorm_neg (v : Point d) : hnorm H (-v) = hnorm H v := by
  have := hnorm_smul (H := H) (-1) v
  simpa using this

lemma hnorm_add (v w : Point d) : hnorm H (v + w) ≤ hnorm H v + hnorm H w := by
  have hv := hnorm_nonneg' (H := H) v
  have hw := hnorm_nonneg' (H := H) w
  rw [hnorm, Real.sqrt_le_left (by positivity), quad_add hG]
  have h := inner_H_le hG v w
  have h1 := hnorm_sq hG v
  have h2 := hnorm_sq hG w
  nlinarith

omit hG in
lemma hnorm_sub_comm (v w : Point d) : hnorm H (v - w) = hnorm H (w - v) := by
  rw [← neg_sub, hnorm_neg (H := H)]

lemma norm_H_le (v : Point d) : ‖H v‖ ≤ hnorm H v := by
  have h := inner_H_le hG v (H v)
  have h2 := hnorm_le_norm hG (H v)
  have hv := hnorm_nonneg' (H := H) v
  rw [real_inner_self_eq_norm_sq] at h
  by_cases hz : ‖H v‖ = 0
  · rw [hz]; exact hv
  · have hp : 0 < ‖H v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have : ‖H v‖ ^ 2 ≤ hnorm H v * ‖H v‖ :=
      h.trans (mul_le_mul_of_nonneg_left h2 hv)
    nlinarith

lemma norm_le_hnorm : ∃ μ, 0 < μ ∧ ∀ v : Point d, Real.sqrt μ * ‖v‖ ≤ hnorm H v := by
  obtain ⟨μ, hμ, hc⟩ := hG.coercive
  refine ⟨μ, hμ, fun v => ?_⟩
  rw [hnorm, ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul hμ.le]
  exact Real.sqrt_le_sqrt (hc v)

end Geometry

noncomputable def dnorm (H : Point d →L[ℝ] Point d) (g : Point d) : ℝ :=
  sSup ((fun w => ⟪g, w⟫) '' {w | ⟪H w, w⟫ ≤ 1})

section Dual

variable {H : Point d →L[ℝ] Point d} (hG : Geometry H)
include hG

lemma unitBall_compact : IsCompact {w : Point d | ⟪H w, w⟫ ≤ 1} := by
  obtain ⟨μ, hμ, hc⟩ := hG.coercive
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by fun_prop) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt (1 / μ), fun w hw => ?_⟩
    simp only [Set.mem_ofPred_eq] at hw
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hμ]
    nlinarith [hc w]

lemma dnorm_attained (g : Point d) :
    ∃ w, ⟪H w, w⟫ ≤ 1 ∧ ⟪g, w⟫ = dnorm H g := by
  have hK := (unitBall_compact hG).image (f := fun w => ⟪g, w⟫) (by fun_prop)
  have hne : ((fun w => ⟪g, w⟫) '' {w : Point d | ⟪H w, w⟫ ≤ 1}).Nonempty :=
    ⟨_, ⟨0, by simp, rfl⟩⟩
  obtain ⟨w, hw, he⟩ := hK.sSup_mem hne
  exact ⟨w, hw, he⟩

lemma bdd_dual (g : Point d) :
    BddAbove ((fun w => ⟪g, w⟫) '' {w : Point d | ⟪H w, w⟫ ≤ 1}) :=
  ((unitBall_compact hG).image (f := fun w => ⟪g, w⟫) (by fun_prop)).bddAbove

lemma dnorm_nonneg (g : Point d) : 0 ≤ dnorm H g :=
  le_csSup (bdd_dual hG g) ⟨0, by simp, by simp⟩

lemma inner_le_dnorm (g w : Point d) : ⟪g, w⟫ ≤ dnorm H g * hnorm H w := by
  by_cases hw : ⟪H w, w⟫ = 0
  · rw [eq_zero_of_quad hG w hw]
    simp [hnorm]
  · have hq : 0 < ⟪H w, w⟫ := lt_of_le_of_ne (quad_nonneg hG w) (Ne.symm hw)
    have hn : 0 < hnorm H w := Real.sqrt_pos.mpr hq
    set w' := (1 / hnorm H w) • w
    have hw' : ⟪H w', w'⟫ ≤ 1 := by
      have e : ⟪H w', w'⟫ = (1 / hnorm H w) ^ 2 * hnorm H w ^ 2 := by
        rw [quad_smul , hnorm_sq hG]
      rw [e, ← mul_pow, one_div, inv_mul_cancel₀ (ne_of_gt hn), one_pow]
    have h := le_csSup (bdd_dual hG g) (Set.mem_image_of_mem (fun w => ⟪g, w⟫) hw')
    change ⟪g, w'⟫ ≤ dnorm H g at h
    rw [real_inner_smul_right] at h
    have h2 := mul_le_mul_of_nonneg_left h hn.le
    have e : hnorm H w * (1 / hnorm H w * ⟪g, w⟫) = ⟪g, w⟫ := by field_simp
    rw [e] at h2
    linarith

omit hG in
lemma dnorm_le_of {g : Point d} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ w, ⟪g, w⟫ ≤ c * hnorm H w) : dnorm H g ≤ c := by
  apply csSup_le ((Set.nonempty_of_mem
    (show (0 : Point d) ∈ {w : Point d | ⟪H w, w⟫ ≤ 1} by simp)).image _)
  rintro _ ⟨w, hw, rfl⟩
  have h1 : hnorm H w ≤ 1 := by
    rw [hnorm, Real.sqrt_le_one]
    exact hw
  calc ⟪g, w⟫ ≤ c * hnorm H w := h w
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left h1 hc
    _ = c := mul_one c

lemma certifies_dnorm (g : Point d) : Certifies H g (dnorm H g) :=
  ⟨dnorm_nonneg hG g, fun w => inner_le_dnorm hG g w⟩

omit hG in
lemma dnorm_le_of_certifies {g : Point d} {c : ℝ} (h : Certifies H g c) :
    dnorm H g ≤ c :=
  dnorm_le_of h.1 h.2

lemma certifies_of_dnorm_le {g : Point d} {c : ℝ} (h : dnorm H g ≤ c) : Certifies H g c :=
  ⟨(dnorm_nonneg hG g).trans h, fun w =>
    (inner_le_dnorm hG g w).trans (mul_le_mul_of_nonneg_right h (hnorm_nonneg' (H := H) w))⟩

lemma norm_le_dnorm (g : Point d) : ‖g‖ ≤ dnorm H g := by
  have h := inner_le_dnorm hG g g
  have h2 := hnorm_le_norm hG g
  rw [real_inner_self_eq_norm_sq] at h
  by_cases hz : ‖g‖ = 0
  · rw [hz]; exact dnorm_nonneg hG g
  · have hp : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have : ‖g‖ ^ 2 ≤ dnorm H g * ‖g‖ :=
      h.trans (mul_le_mul_of_nonneg_left h2 (dnorm_nonneg hG g))
    nlinarith

lemma dnorm_add_le (a b : Point d) : dnorm H (a + b) ≤ dnorm H a + dnorm H b := by
  apply dnorm_le_of (add_nonneg (dnorm_nonneg hG a) (dnorm_nonneg hG b))
  intro w
  rw [inner_add_left, add_mul]
  exact add_le_add (inner_le_dnorm hG a w) (inner_le_dnorm hG b w)

lemma dnorm_neg (a : Point d) : dnorm H (-a) = dnorm H a := by
  apply le_antisymm
  · apply dnorm_le_of (dnorm_nonneg hG a)
    intro w
    have h := inner_le_dnorm hG a (-w)
    rw [inner_neg_right, hnorm_neg (H := H)] at h
    rw [inner_neg_left]
    exact h
  · apply dnorm_le_of (dnorm_nonneg hG (-a))
    intro w
    have h := inner_le_dnorm hG (-a) (-w)
    rw [inner_neg_right, hnorm_neg (H := H), inner_neg_left, neg_neg] at h
    exact h

lemma dnorm_sub_le_dnorm_sub (a b : Point d) :
    dnorm H a ≤ dnorm H b + dnorm H (a - b) := by
  have h := dnorm_add_le hG b (a - b)
  rwa [add_sub_cancel] at h

lemma dnorm_le_norm : ∃ C, 0 ≤ C ∧ ∀ g : Point d, dnorm H g ≤ C * ‖g‖ := by
  obtain ⟨μ, hμ, hc⟩ := norm_le_hnorm hG
  refine ⟨1 / Real.sqrt μ, by positivity, fun g => ?_⟩
  apply dnorm_le_of (by positivity)
  intro w
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hw : ‖w‖ ≤ hnorm H w / Real.sqrt μ := by
    rw [le_div_iff₀ hs, mul_comm]; exact hc w
  calc ⟪g, w⟫ ≤ ‖g‖ * ‖w‖ := real_inner_le_norm g w
    _ ≤ ‖g‖ * (hnorm H w / Real.sqrt μ) := mul_le_mul_of_nonneg_left hw (norm_nonneg g)
    _ = 1 / Real.sqrt μ * ‖g‖ * hnorm H w := by ring

lemma continuous_dnorm : Continuous (dnorm H) := by
  obtain ⟨C, hC, hle⟩ := dnorm_le_norm hG
  apply Metric.continuous_iff.mpr
  intro b ε hε
  refine ⟨ε / (C + 1), by positivity, fun a hab => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h1 := dnorm_sub_le_dnorm_sub hG a b
  have h2 := dnorm_sub_le_dnorm_sub hG b a
  have h3 := hle (a - b)
  have h4 := hle (b - a)
  rw [dist_eq_norm] at hab
  have h5 : C * ‖a - b‖ < ε := by
    have : C * ‖a - b‖ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hab.le hC
    have : C * (ε / (C + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  rw [norm_sub_rev] at h4
  constructor <;> linarith

end Dual

noncomputable def curv (H : Point d →L[ℝ] Point d) (L0 L1 : ℝ) (g : Point d) : ℝ :=
  L0 + L1 * dnorm H g

def HessBound (f : Point d → ℝ) (H : Point d →L[ℝ] Point d) (L0 L1 : ℝ) : Prop :=
  ∀ x c, Certifies H (gradient f x) c → ∀ v w,
    ⟪fderiv ℝ (gradient f) x v, w⟫ ≤ (L0 + L1 * c) * hnorm H v * hnorm H w

lemma HessBound.mono {f : Point d → ℝ} {H : Point d →L[ℝ] Point d} {L0 L1 L1' : ℝ}
     (hB : HessBound f H L0 L1) (hL : L1 ≤ L1') :
    HessBound f H L0 L1' := by
  intro x c hc v w
  have h := hB x c hc v w
  have hv := hnorm_nonneg' (H := H) v
  have hw := hnorm_nonneg' (H := H) w
  have h1 : L1 * c ≤ L1' * c := mul_le_mul_of_nonneg_right hL hc.1
  have h2 : 0 ≤ hnorm H v * hnorm H w := mul_nonneg hv hw
  nlinarith

section Local

variable {f : Point d → ℝ} {H : Point d →L[ℝ] Point d} {L0 L1 : ℝ}
  (hG : Geometry H) (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
  (hg : ∀ x, HasGradientAt f (gradient f x) x) (hd : Differentiable ℝ (gradient f))
  (hB : HessBound f H L0 L1)

include hg in
lemma hasDerivAt_line (x v : Point d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪gradient f (x + t • v), v⟫ t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have h2 := (hg (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
  simpa [Function.comp_def] using h2

include hd in
lemma hasDerivAt_inner_gradient (x v w : Point d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪gradient f (x + s • v), w⟫)
      ⟪fderiv ℝ (gradient f) (x + t • v) v, w⟫ t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have h2 := (hd (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
  have h3 := (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t h2
  simp only [Function.comp_def, innerSL_apply_apply] at h3
  convert h3 using 1
  · ext s; exact real_inner_comm _ _
  · exact real_inner_comm _ _

include hG hL0 hL1 hd hB in
lemma segment_difference (x v : Point d) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, dnorm H (gradient f (x + t • v)) ≤ S) :
    dnorm H (gradient f (x + v) - gradient f x) ≤ (L0 + L1 * S) * hnorm H v := by
  have hc0 : 0 ≤ (L0 + L1 * S) * hnorm H v :=
    mul_nonneg (by nlinarith [hL0.le]) (hnorm_nonneg' (H := H) v)
  apply dnorm_le_of hc0
  intro w
  let φ := fun s : ℝ => ⟪gradient f (x + s • v), w⟫
  have hder := fun t => hasDerivAt_inner_gradient hd x v w t
  have hmv := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (f := φ) (C := (L0 + L1 * S) * hnorm H v * hnorm H w)
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t _ => (hder t).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hder t).deriv]
      have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
      exact hB _ S (certifies_of_dnorm_le hG (hS t ht')) v w)
    0 (by simp) 1 (by simp) zero_le_one
  simp only [φ, one_smul, zero_smul, add_zero, sub_zero, mul_one] at hmv
  rw [inner_sub_left]
  linarith

include hG hL0 hL1 hd hB in
lemma segment_max (x v : Point d) (hv : L1 * hnorm H v ≤ 1 / 2) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      dnorm H (gradient f (x + t • v)) ≤ 2 * (dnorm H (gradient f x) + L0 * hnorm H v) := by
  have hcont : ContinuousOn (fun t : ℝ => dnorm H (gradient f (x + t • v))) (Icc 0 1) :=
    ((continuous_dnorm hG).comp (hd.continuous.comp (by fun_prop))).continuousOn
  obtain ⟨t0, ht0, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hcont
  set S := dnorm H (gradient f (x + t0 • v))
  have hS0 : 0 ≤ S := dnorm_nonneg hG _
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, dnorm H (gradient f (x + τ • (t0 • v))) ≤ S := by
    intro τ hτ
    have hmem : τ * t0 ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hτ.1 ht0.1, by nlinarith [hτ.1, hτ.2, ht0.1, ht0.2]⟩
    have h := hmax hmem
    simp only [Set.mem_ofPred_eq] at h
    rwa [smul_smul]
  have hdiff := segment_difference hG hL0 hL1 hd hB x (t0 • v) hS0 hseg
  have hn : hnorm H (t0 • v) ≤ hnorm H v := by
    rw [hnorm_smul (H := H), abs_of_nonneg ht0.1]
    exact mul_le_of_le_one_left (hnorm_nonneg' (H := H) v) ht0.2
  have htri := dnorm_sub_le_dnorm_sub hG (gradient f (x + t0 • v)) (gradient f x)
  have hS : S ≤ dnorm H (gradient f x) + (L0 + L1 * S) * hnorm H v := by
    have : (L0 + L1 * S) * hnorm H (t0 • v) ≤ (L0 + L1 * S) * hnorm H v :=
      mul_le_mul_of_nonneg_left hn (by nlinarith [hL0.le])
    linarith
  intro t ht
  have h1 := hmax ht
  simp only [Set.mem_ofPred_eq] at h1
  have hvn := hnorm_nonneg' (H := H) v
  nlinarith

include hG hL0 hL1 hd hB in
lemma segment_difference_local (x v : Point d) (hv : L1 * hnorm H v ≤ 1 / 2) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dnorm H (gradient f (x + t • v) - gradient f x) ≤
      2 * curv H L0 L1 (gradient f x) * (t * hnorm H v) := by
  have hmax := segment_max hG hL0 hL1 hd hB x v hv
  set S := 2 * (dnorm H (gradient f x) + L0 * hnorm H v)
  have hS0 : 0 ≤ S := by
    have := dnorm_nonneg hG (gradient f x); have := hnorm_nonneg' (H := H) v; positivity
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, dnorm H (gradient f (x + τ • (t • v))) ≤ S := by
    intro τ hτ
    rw [smul_smul]
    exact hmax _ ⟨mul_nonneg hτ.1 ht.1, by nlinarith [hτ.1, hτ.2, ht.1, ht.2]⟩
  have h := segment_difference hG hL0 hL1 hd hB x (t • v) hS0 hseg
  rw [hnorm_smul (H := H), abs_of_nonneg ht.1] at h
  have hcoef : L0 + L1 * S ≤ 2 * curv H L0 L1 (gradient f x) := by
    unfold curv
    have hvn := hnorm_nonneg' (H := H) v
    simp only [S]
    nlinarith
  have hp : 0 ≤ t * hnorm H v := mul_nonneg ht.1 (hnorm_nonneg' (H := H) v)
  exact h.trans (mul_le_mul_of_nonneg_right hcoef hp)

include hG hL0 hL1 hg hd hB in
lemma local_descent (x v : Point d) (hv : L1 * hnorm H v ≤ 1 / 2) :
    f (x + v) ≤ f x + ⟪gradient f x, v⟫ + curv H L0 L1 (gradient f x) * hnorm H v ^ 2 := by
  set M := curv H L0 L1 (gradient f x)
  set ℓ := hnorm H v
  let ψ := fun t : ℝ => f (x + t • v) - t * ⟪gradient f x, v⟫ - M * ℓ ^ 2 * t ^ 2
  have hder : ∀ t, HasDerivAt ψ
      (⟪gradient f (x + t • v), v⟫ - ⟪gradient f x, v⟫ - M * ℓ ^ 2 * (2 * t)) t := by
    intro t
    have h1 := hasDerivAt_line hg x v t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, v⟫) ⟪gradient f x, v⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, v⟫
    have h3 : HasDerivAt (fun s : ℝ => M * ℓ ^ 2 * s ^ 2) (M * ℓ ^ 2 * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (M * ℓ ^ 2)
    exact (h1.sub h2).sub h3
  have hmv := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le (f := ψ) (C := 0)
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t _ => (hder t).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hder t).deriv]
      have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
      have hdl := segment_difference_local hG hL0 hL1 hd hB x v hv t ht'
      have hin := inner_le_dnorm hG (gradient f (x + t • v) - gradient f x) v
      rw [inner_sub_left] at hin
      have hℓ : 0 ≤ ℓ := hnorm_nonneg' (H := H) v
      have : dnorm H (gradient f (x + t • v) - gradient f x) * ℓ ≤ 2 * M * (t * ℓ) * ℓ :=
        mul_le_mul_of_nonneg_right hdl hℓ
      nlinarith)
    0 (by simp) 1 (by simp) zero_le_one
  simp only [ψ, one_smul, zero_smul, add_zero, sub_zero, one_mul, one_pow,
    zero_mul, mul_one] at hmv
  ring_nf at hmv ⊢
  linarith

include hG hL0 hL1 hg hd hB in
lemma dnorm_sq_le {xstar : Point d}
    (hmin : IsMinOn f Set.univ xstar) (x : Point d) :
    dnorm H (gradient f x) ^ 2 ≤ 4 * curv H L0 L1 (gradient f x) * (f x - f xstar) := by
  set N := dnorm H (gradient f x)
  set M := curv H L0 L1 (gradient f x)
  have hN := dnorm_nonneg hG (gradient f x)
  have hM : 0 < M := by unfold M curv; nlinarith
  have hMN : L1 * N ≤ M := by unfold M curv; linarith
  obtain ⟨w, hw, hwe⟩ := dnorm_attained hG (gradient f x)
  set t := N / (2 * M)
  have ht : 0 ≤ t := by positivity
  have hwn : hnorm H w ≤ 1 := by rw [hnorm, Real.sqrt_le_one]; exact hw
  have hv : L1 * hnorm H ((-t) • w) ≤ 1 / 2 := by
    rw [hnorm_smul (H := H), abs_neg, abs_of_nonneg ht]
    have h1 : L1 * (t * hnorm H w) ≤ L1 * t := by
      have := mul_le_of_le_one_right ht hwn
      exact mul_le_mul_of_nonneg_left this hL1
    have h2 : L1 * t ≤ 1 / 2 := by
      simp only [t]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hdesc := local_descent hG hL0 hL1 hg hd hB x ((-t) • w) hv
  have hlow := hmin (Set.mem_univ (x + (-t) • w))
  simp only [Set.mem_ofPred_eq] at hlow
  rw [inner_smul_right, hwe, hnorm_smul (H := H), abs_neg, abs_of_nonneg ht] at hdesc
  have hq : (t * hnorm H w) ^ 2 ≤ t ^ 2 := by
    have h0 := mul_nonneg ht (hnorm_nonneg' (H := H) w)
    have : t * hnorm H w ≤ t := mul_le_of_le_one_right ht hwn
    exact pow_le_pow_left₀ h0 this 2
  have hkey : f xstar ≤ f x - t * N + M * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hq hM.le
    linarith
  have hval : t * N - M * t ^ 2 = N ^ 2 / (4 * M) := by
    simp only [t]; field_simp; ring
  have : N ^ 2 / (4 * M) ≤ f x - f xstar := by linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at this

lemma dnorm_le_of_sq {N F L0 L1 : ℝ} (hF : 0 ≤ F) (hL0 : 0 ≤ L0)
    (hL1 : 0 ≤ L1) (h : N ^ 2 ≤ 4 * (L0 + L1 * N) * F) :
    N ≤ 4 * L1 * F + 2 * Real.sqrt (L0 * F) := by
  set s := Real.sqrt (L0 * F)
  have hs : s ^ 2 = L0 * F := Real.sq_sqrt (mul_nonneg hL0 hF)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg (L0 * F)
  by_contra hc
  rw [not_le] at hc
  have hA : 0 < N - (4 * L1 * F + 2 * s) := sub_pos.mpr hc
  have hB : 0 ≤ N - 2 * s := by nlinarith [mul_nonneg hL1 hF]
  have h1 : 0 < N * (N - (4 * L1 * F + 2 * s)) := mul_pos (by linarith [mul_nonneg hL1 hF]) hA
  have h2 : 0 ≤ s * (N - 2 * s) := mul_nonneg hs0 hB
  nlinarith

end Local

end OracleTemplate.MatrixGeneralizedZO
