import LongTails.Setups.MinimaxLmo
import LongTails.Proofs.NormBallGeometry
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open MeasureTheory Filter Topology Asymptotics
open scoped RealInnerProductSpace

namespace OracleTemplate.MinimaxLmo

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO)
open LongTails.Setups.MinimaxLmo (GeneralizedMinimax)
open OracleTemplate.NormBallLMO

section Descent

variable {d : ℕ} {N : Seminorm ℝ (Space d)} {R : ℝ}

lemma dualNorm_neg_le (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u : Space d) :
    dualNorm N (-u) ≤ dualNorm N u := by
  refine dualNorm_le_of fun v hv => ?_
  rw [inner_neg_left, ← inner_neg_right]
  exact inner_le_dualNorm hR u (by rwa [map_neg_eq_map])

lemma dualNorm_neg (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u : Space d) : dualNorm N (-u) = dualNorm N u :=
  le_antisymm (dualNorm_neg_le hR u) (by simpa using dualNorm_neg_le hR (-u))

lemma dualNorm_sub_comm (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u w : Space d) :
    dualNorm N (u - w) = dualNorm N (w - u) := by
  rw [← dualNorm_neg hR, neg_sub]

lemma anchored_descent (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    {φ : Space d → ℝ} {g : Space d → Space d} (hg : ∀ z, HasGradientAt φ (g z) z)
    {x h : Space d} {M : ℝ} (hM : ∀ t ∈ Set.Ioo (0 : ℝ) 1, dualNorm N (g (x + t • h) - g x) ≤ M * (t * N h)) :
    φ (x + h) ≤ φ x + ⟪g x, h⟫ + M / 2 * N h ^ 2 ∧
      φ x + ⟪g x, h⟫ - M / 2 * N h ^ 2 ≤ φ (x + h) := by
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • h) h t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hφt : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (x + t • h)) ⟪g (x + t • h), h⟫ t := by
    intro t
    have hf := (hg (x + t • h)).hasFDerivAt.comp_hasDerivAt t (hline t)
    convert hf using 1
    · rfl
    · rw [InnerProductSpace.toDual_apply_apply]
  have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * ⟪g x, h⟫) ⟪g x, h⟫ t := fun t => by
    simpa using (hasDerivAt_id t).mul_const ⟪g x, h⟫
  have h3 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => M / 2 * t ^ 2 * N h ^ 2) (M / 2 * (2 * t) * N h ^ 2) t :=
    fun t => by
      have := ((hasDerivAt_pow 2 t).const_mul (M / 2)).mul_const (N h ^ 2)
      simpa using this
  have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |⟪g (x + t • h), h⟫ - ⟪g x, h⟫| ≤ M * t * N h ^ 2 := by
    intro t ht
    have hN := apply_nonneg N h
    have e : ⟪g (x + t • h), h⟫ - ⟪g x, h⟫ = ⟪g (x + t • h) - g x, h⟫ := by rw [inner_sub_left]
    rw [e, abs_le]
    have hu := inner_le_dualNorm_mul hR hdef (g (x + t • h) - g x) h
    have hl := inner_le_dualNorm_mul hR hdef (-(g (x + t • h) - g x)) h
    rw [inner_neg_left, dualNorm_neg hR] at hl
    have hm := mul_le_mul_of_nonneg_right (hM t ht) hN
    constructor <;> nlinarith
  constructor
  · let ψ : ℝ → ℝ := fun t => φ (x + t • h) - t * ⟪g x, h⟫ - M / 2 * t ^ 2 * N h ^ 2
    have hψ : ∀ t, HasDerivAt ψ (⟪g (x + t • h), h⟫ - ⟪g x, h⟫ - M / 2 * (2 * t) * N h ^ 2) t :=
      fun t => ((hφt t).sub (h2 t)).sub (h3 t)
    have hmono : AntitoneOn ψ (Set.Icc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
      · exact fun t _ => (hψ t).continuousAt.continuousWithinAt
      · intro t _; exact (hψ t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hψ t).deriv]
        have := (abs_le.mp (hbound t ht)).2
        nlinarith
    have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    simp only [ψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_pow, mul_one, one_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h01
    linarith
  · let ψ : ℝ → ℝ := fun t => φ (x + t • h) - t * ⟪g x, h⟫ + M / 2 * t ^ 2 * N h ^ 2
    have hψ : ∀ t, HasDerivAt ψ (⟪g (x + t • h), h⟫ - ⟪g x, h⟫ + M / 2 * (2 * t) * N h ^ 2) t :=
      fun t => ((hφt t).sub (h2 t)).add (h3 t)
    have hmono : MonotoneOn ψ (Set.Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · exact fun t _ => (hψ t).continuousAt.continuousWithinAt
      · intro t _; exact (hψ t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hψ t).deriv]
        have := (abs_le.mp (hbound t ht)).1
        nlinarith
    have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    simp only [ψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_pow, mul_one, one_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h01
    linarith

end Descent

section Structure

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p)
include H

lemma gy_mono (x : Space d₁) (y y' : Space d₂) :
    ⟪gy x y' - gy x y, y' - y⟫ ≤ -(μ * ‖y' - y‖ ^ 2) := by
  have h1 := H.strongly_concave x y y'
  have h2 := H.strongly_concave x y' y
  have e1 : ⟪gy x y', y - y'⟫ = -⟪gy x y', y' - y⟫ := by rw [← inner_neg_right, neg_sub]
  have e2 : ‖y - y'‖ = ‖y' - y‖ := norm_sub_rev _ _
  rw [inner_sub_left]
  rw [e1, e2] at h2
  linarith

lemma exists_max (hμ : 0 < μ) (x : Space d₁) : ∃ y, ∀ y', f x y' ≤ f x y := by
  set g0 := gy x 0
  set r := 2 * ‖g0‖ / μ + 1
  have hcont : Continuous (f x) := continuous_iff_continuousAt.mpr fun y => (H.grad_y x y).continuousAt
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall (0 : Space d₂) r).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self (by positivity)⟩ hcont.continuousOn
  refine ⟨y, fun y' => ?_⟩
  by_cases hy' : y' ∈ Metric.closedBall (0 : Space d₂) r
  · exact hmax hy'
  · have h0 : f x 0 ≤ f x y := hmax (Metric.mem_closedBall_self (by positivity))
    have hsc := H.strongly_concave x 0 y'
    rw [sub_zero] at hsc
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy'
    have hci := real_inner_le_norm g0 y'
    have hr : 2 * ‖g0‖ / μ < ‖y'‖ := by linarith
    have hq : ‖g0‖ * ‖y'‖ ≤ μ / 2 * ‖y'‖ ^ 2 := by
      rw [div_lt_iff₀ hμ] at hr
      nlinarith [norm_nonneg y', norm_nonneg g0]
    linarith

noncomputable def ystar (hμ : 0 < μ) (x : Space d₁) : Space d₂ :=
  Classical.choose (exists_max H hμ x)

lemma ystar_max (hμ : 0 < μ) (x : Space d₁) (y : Space d₂) : f x y ≤ f x (ystar H hμ x) :=
  Classical.choose_spec (exists_max H hμ x) y

lemma gy_ystar (hμ : 0 < μ) (x : Space d₁) : gy x (ystar H hμ x) = 0 := by
  have hloc : IsLocalMax (f x) (ystar H hμ x) :=
    Filter.Eventually.of_forall fun y => ystar_max H hμ x y
  have hz := hloc.hasFDerivAt_eq_zero (H.grad_y x (ystar H hμ x)).hasFDerivAt
  have := congrArg (InnerProductSpace.toDual ℝ (Space d₂)).symm hz
  simpa using this

lemma ystar_quad (hμ : 0 < μ) (x : Space d₁) (y : Space d₂) :
    f x y ≤ f x (ystar H hμ x) - μ / 2 * ‖y - ystar H hμ x‖ ^ 2 := by
  have h := H.strongly_concave x (ystar H hμ x) y
  rw [gy_ystar H hμ x, inner_zero_left] at h
  linarith

lemma ystar_unique (hμ : 0 < μ) (x : Space d₁) (y : Space d₂) (hy : ∀ y', f x y' ≤ f x y) :
    y = ystar H hμ x := by
  have h := ystar_quad H hμ x y
  have h2 := hy (ystar H hμ x)
  have hq : ‖y - ystar H hμ x‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖y - ystar H hμ x‖ = 0 := by nlinarith [norm_nonneg (y - ystar H hμ x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma dist_le_grad (hμ : 0 < μ) (x : Space d₁) (y : Space d₂) :
    μ * ‖y - ystar H hμ x‖ ≤ ‖gy x y‖ := by
  have hm := gy_mono H x y (ystar H hμ x)
  rw [gy_ystar H hμ x, zero_sub, inner_neg_left] at hm
  have hci := real_inner_le_norm (gy x y) (ystar H hμ x - y)
  rw [norm_sub_rev] at hci
  by_cases hd : ‖y - ystar H hμ x‖ = 0
  · rw [hd, mul_zero]; exact norm_nonneg _
  · have hpos : 0 < ‖y - ystar H hμ x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have e : ‖ystar H hμ x - y‖ = ‖y - ystar H hμ x‖ := norm_sub_rev _ _
    rw [e] at hm
    have : μ * ‖y - ystar H hμ x‖ * ‖y - ystar H hμ x‖ ≤ ‖gy x y‖ * ‖y - ystar H hμ x‖ := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma inner_grad_le (hμ : 0 < μ) (x : Space d₁) (y : Space d₂) :
    ⟪gy x y, y - ystar H hμ x⟫ ≤ -(μ * ‖y - ystar H hμ x‖ ^ 2) := by
  have hm := gy_mono H x (ystar H hμ x) y
  rwa [gy_ystar H hμ x, sub_zero] at hm

lemma grad_y_near (hμ : 0 < μ) (x : Space d₁) (y : Space d₂) (hD : L₁ * ‖y - ystar H hμ x‖ ≤ 1) :
    ‖gy x y‖ ≤ L₀ * ‖y - ystar H hμ x‖ := by
  have h := H.smooth_y x (ystar H hμ x) x y (by simpa [norm_sub_rev] using hD)
  rw [gy_ystar H hμ x, norm_zero, mul_zero, add_zero, zero_sub, norm_neg, sub_self, map_zero,
    zero_add, norm_sub_rev] at h
  exact h

lemma ystar_lip (hμ : 0 < μ) (x x' : Space d₁) (hx : L₁ * N (x - x') ≤ 1) :
    ‖ystar H hμ x - ystar H hμ x'‖ ≤ L₀ / μ * N (x - x') := by
  have h := H.smooth_y x (ystar H hμ x) x' (ystar H hμ x) (by simpa using hx)
  rw [gy_ystar H hμ x, norm_zero, mul_zero, add_zero, zero_sub, norm_neg, sub_self, norm_zero,
    add_zero] at h
  have h2 := dist_le_grad H hμ x' (ystar H hμ x)
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  linarith

end Structure

section Primal

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)} {R : ℝ}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)

noncomputable def Phi (x : Space d₁) : ℝ := f x (ystar H hμ x)

noncomputable def gPhi (x : Space d₁) : Space d₁ := gx x (ystar H hμ x)

include H hμ

variable (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
include hR

lemma bias_bound (x : Space d₁) (y : Space d₂) (hD : L₁ * ‖y - ystar H hμ x‖ ≤ 1) :
    dualNorm N (gx x y - gPhi H hμ x) ≤
      (L₀ + L₁ * dualNorm N (gPhi H hμ x)) * ‖y - ystar H hμ x‖ := by
  have h := H.smooth_x x (ystar H hμ x) x y (by simpa [norm_sub_rev] using hD)
  rw [sub_self, map_zero, zero_add, norm_sub_rev] at h
  rw [dualNorm_sub_comm hR]
  exact h

include hL₀ hL₁ in
lemma gPhi_smooth (hκ : 1 ≤ 1 + L₀ / μ) (x x' : Space d₁)
    (hx : L₁ * ((1 + L₀ / μ) * N (x' - x)) ≤ 1) :
    dualNorm N (gPhi H hμ x' - gPhi H hμ x) ≤
      (1 + L₀ / μ) * (L₀ + L₁ * dualNorm N (gPhi H hμ x)) * N (x' - x) := by
  have hN := apply_nonneg N (x' - x)
  have hL1N : L₁ * N (x - x') ≤ 1 := by
    rw [← map_neg_eq_map, neg_sub]
    nlinarith
  have hy := ystar_lip H hμ x x' hL1N
  have hdist : N (x - x') + ‖ystar H hμ x - ystar H hμ x'‖ ≤ (1 + L₀ / μ) * N (x' - x) := by
    rw [← map_neg_eq_map N (x - x'), neg_sub] at hy ⊢
    nlinarith
  have hloc : L₁ * (N (x - x') + ‖ystar H hμ x - ystar H hμ x'‖) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hdist hL₁).trans hx
  have h := H.smooth_x x (ystar H hμ x) x' (ystar H hμ x') hloc
  rw [dualNorm_sub_comm hR]
  have hG : 0 ≤ L₀ + L₁ * dualNorm N (gPhi H hμ x) :=
    add_nonneg hL₀ (mul_nonneg hL₁ (dualNorm_nonneg hR _))
  calc dualNorm N (gPhi H hμ x - gPhi H hμ x') ≤
        (L₀ + L₁ * dualNorm N (gPhi H hμ x)) * (N (x - x') + ‖ystar H hμ x - ystar H hμ x'‖) := h
    _ ≤ (L₀ + L₁ * dualNorm N (gPhi H hμ x)) * ((1 + L₀ / μ) * N (x' - x)) :=
        mul_le_mul_of_nonneg_left hdist hG
    _ = _ := by ring

include hL₀ hL₁ in
lemma G_growth (hκ : 1 ≤ 1 + L₀ / μ) (x x' : Space d₁) (hx : L₁ * ((1 + L₀ / μ) * N (x' - x)) ≤ 1) :
    dualNorm N (gPhi H hμ x') ≤ dualNorm N (gPhi H hμ x) +
      (1 + L₀ / μ) * (L₀ + L₁ * dualNorm N (gPhi H hμ x)) * N (x' - x) :=
  (dualNorm_sub_le hR _ _).trans (add_le_add le_rfl (gPhi_smooth H hμ hR hL₀ hL₁ hκ x x' hx))

include hdef hL₀ hL₁ in
lemma Phi_hasGradient (x : Space d₁) : HasGradientAt (Phi H hμ) (gPhi H hμ x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  set G := dualNorm N (gPhi H hμ x)
  set κ := L₀ / μ
  have hκ : 0 ≤ κ := div_nonneg hL₀ hμ.le
  have hG : 0 ≤ G := dualNorm_nonneg hR _
  set S := ∑ i, N (EuclideanSpace.single i (1 : ℝ))
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => apply_nonneg N _
  set r := 1 / (L₁ * (1 + κ) + 1)
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hrL : L₁ * (1 + κ) * r ≤ 1 := by
    rw [show L₁ * (1 + κ) * r = (L₁ * (1 + κ)) / (L₁ * (1 + κ) + 1) by simp [r]; ring]
    rw [div_le_one (by positivity)]; linarith
  set C := (L₀ + L₁ * (G + (L₀ + L₁ * G) * κ)) / 2 + (L₀ + L₁ * G) * κ + (L₀ + L₁ * G) / 2
  have hC : 0 ≤ C := by positivity
  have hb : ∀ h : Space d₁, N h ≤ r →
      |Phi H hμ (x + h) - Phi H hμ x - ⟪gPhi H hμ x, h⟫| ≤ C * N h ^ 2 := by
    intro h hh
    have hN := apply_nonneg N h
    have hL1r : L₁ * r ≤ 1 := by nlinarith [mul_nonneg (mul_nonneg hL₁ hκ) hr.le]
    have hL1h : L₁ * N h ≤ 1 := (mul_le_mul_of_nonneg_left hh hL₁).trans hL1r
    have hL1h' : L₁ * N (x - (x + h)) ≤ 1 := by
      rwa [show x - (x + h) = -h by abel, map_neg_eq_map]
    set y' := ystar H hμ (x + h)
    have hy' : ‖y' - ystar H hμ x‖ ≤ κ * N h := by
      have := ystar_lip H hμ (x + h) x (by rwa [add_sub_cancel_left])
      simpa [y', κ, add_sub_cancel_left] using this
    have hyN : L₁ * ‖y' - ystar H hμ x‖ ≤ 1 := by
      have h1 : L₁ * ‖y' - ystar H hμ x‖ ≤ L₁ * (κ * N h) := mul_le_mul_of_nonneg_left hy' hL₁
      have h2 : L₁ * (κ * N h) ≤ L₁ * (κ * r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hκ) hL₁
      nlinarith
    have hbias := bias_bound H hμ hR x y' hyN
    have hdual : dualNorm N (gx x y') ≤ G + (L₀ + L₁ * G) * κ := by
      have h1 := dualNorm_sub_le hR (gx x y') (gPhi H hμ x)
      have h2 : (L₀ + L₁ * G) * ‖y' - ystar H hμ x‖ ≤ (L₀ + L₁ * G) * κ := by
        have : κ * N h ≤ κ := by nlinarith
        have h3 : 0 ≤ L₀ + L₁ * G := by positivity
        nlinarith
      linarith
    have hup := (anchored_descent hR hdef (φ := fun z => f z y') (g := fun z => gx z y')
      (fun z => H.grad_x z y') (x := x) (h := h) (M := L₀ + L₁ * dualNorm N (gx x y'))
      (fun t ht => by
        have hloc : L₁ * (N (x - (x + t • h)) + ‖y' - y'‖) ≤ 1 := by
          rw [sub_self, norm_zero, add_zero, show x - (x + t • h) = -(t • h) by abel, map_neg_eq_map,
            map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht.1]
          have := mul_le_mul_of_nonneg_left (le_of_lt ht.2) (mul_nonneg hL₁ hN)
          nlinarith
        have := H.smooth_x x y' (x + t • h) y' hloc
        rw [dualNorm_sub_comm hR, sub_self, norm_zero, add_zero,
          show x - (x + t • h) = -(t • h) by abel, map_neg_eq_map, map_smul_eq_mul,
          Real.norm_eq_abs, abs_of_pos ht.1] at this
        exact this)).1
    have hlow := (anchored_descent hR hdef (φ := fun z => f z (ystar H hμ x))
      (g := fun z => gx z (ystar H hμ x)) (fun z => H.grad_x z _) (x := x) (h := h) (M := L₀ + L₁ * G)
      (fun t ht => by
        have hloc : L₁ * (N (x - (x + t • h)) + ‖ystar H hμ x - ystar H hμ x‖) ≤ 1 := by
          rw [sub_self, norm_zero, add_zero, show x - (x + t • h) = -(t • h) by abel, map_neg_eq_map,
            map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht.1]
          have := mul_le_mul_of_nonneg_left (le_of_lt ht.2) (mul_nonneg hL₁ hN)
          nlinarith
        have := H.smooth_x x (ystar H hμ x) (x + t • h) (ystar H hμ x) hloc
        rw [dualNorm_sub_comm hR, sub_self, norm_zero, add_zero,
          show x - (x + t • h) = -(t • h) by abel, map_neg_eq_map, map_smul_eq_mul,
          Real.norm_eq_abs, abs_of_pos ht.1] at this
        exact this)).2
    have hmax1 : f x y' ≤ Phi H hμ x := ystar_max H hμ x y'
    have hmax2 : f (x + h) (ystar H hμ x) ≤ Phi H hμ (x + h) := ystar_max H hμ (x + h) _
    have hinner : ⟪gx x y', h⟫ ≤ ⟪gPhi H hμ x, h⟫ + (L₀ + L₁ * G) * κ * N h ^ 2 := by
      have e : ⟪gx x y', h⟫ = ⟪gPhi H hμ x, h⟫ + ⟪gx x y' - gPhi H hμ x, h⟫ := by
        rw [inner_sub_left]; ring
      have hci := inner_le_dualNorm_mul hR hdef (gx x y' - gPhi H hμ x) h
      have : dualNorm N (gx x y' - gPhi H hμ x) * N h ≤ (L₀ + L₁ * G) * κ * N h ^ 2 := by
        have h4 := mul_le_mul_of_nonneg_right hbias hN
        have h5 : (L₀ + L₁ * G) * ‖y' - ystar H hμ x‖ * N h ≤ (L₀ + L₁ * G) * (κ * N h) * N h := by
          have : 0 ≤ L₀ + L₁ * G := by positivity
          gcongr
        nlinarith
      linarith
    have hMup : (L₀ + L₁ * dualNorm N (gx x y')) / 2 * N h ^ 2 ≤
        (L₀ + L₁ * (G + (L₀ + L₁ * G) * κ)) / 2 * N h ^ 2 := by gcongr
    have hPx : Phi H hμ (x + h) = f (x + h) y' := rfl
    have hCexp : C * N h ^ 2 = (L₀ + L₁ * (G + (L₀ + L₁ * G) * κ)) / 2 * N h ^ 2 +
        (L₀ + L₁ * G) * κ * N h ^ 2 + (L₀ + L₁ * G) / 2 * N h ^ 2 := by simp only [C]; ring
    have hn1 : 0 ≤ (L₀ + L₁ * (G + (L₀ + L₁ * G) * κ)) / 2 * N h ^ 2 := by positivity
    have hn2 : 0 ≤ (L₀ + L₁ * G) * κ * N h ^ 2 := by positivity
    have hn3 : 0 ≤ (L₀ + L₁ * G) / 2 * N h ^ 2 := by positivity
    have hgP : gPhi H hμ x = gx x (ystar H hμ x) := rfl
    have hPh : Phi H hμ x = f x (ystar H hμ x) := rfl
    rw [abs_le]
    constructor
    · rw [hPx, hPh, hgP]
      have : f (x + h) (ystar H hμ x) ≤ f (x + h) y' := hmax2
      linarith
    · rw [hPx]
      linarith
  have hbig : (fun h : Space d₁ => Phi H hμ (x + h) - Phi H hμ x -
      (InnerProductSpace.toDual ℝ (Space d₁) (gPhi H hμ x)) h) =O[𝓝 0] (fun h : Space d₁ => ‖h‖ ^ 2) := by
    refine IsBigO.of_bound (C * S ^ 2) ?_
    have hball : Metric.ball (0 : Space d₁) (r / (S + 1)) ∈ 𝓝 (0 : Space d₁) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hball] with h hh
    rw [Metric.mem_ball, dist_zero_right] at hh
    have hNh := seminorm_le_norm N h
    have hNr : N h ≤ r := by
      have : S * ‖h‖ ≤ r := by
        rw [lt_div_iff₀ (by positivity)] at hh
        nlinarith [norm_nonneg h]
      linarith
    rw [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖h‖ ^ 2)]
    refine (hb h hNr).trans ?_
    have h0 := apply_nonneg N h
    have : N h ^ 2 ≤ (S * ‖h‖) ^ 2 := pow_le_pow_left₀ h0 hNh 2
    nlinarith
  have hlit : (fun h : Space d₁ => ‖h‖ ^ 2) =o[𝓝 0] (fun h : Space d₁ => h) := by
    have h0 := (isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)).comp_tendsto
      (tendsto_norm_zero (E := Space d₁))
    exact isLittleO_norm_right.mp h0
  exact hbig.trans_isLittleO hlit

omit hR in
lemma Phi_gap (x : Space d₁) : Phi H hμ x₁ - Phi H hμ x ≤ Δ := by
  obtain ⟨y', hy'⟩ := H.gap x (ystar H hμ x₁)
  have := ystar_max H hμ x y'
  simp only [Phi]
  linarith

include hdef hL₀ hL₁ in
lemma Phi_descent (x d : Space d₁) (hd : L₁ * ((1 + L₀ / μ) * N d) ≤ 1) :
    Phi H hμ (x + d) ≤ Phi H hμ x + ⟪gPhi H hμ x, d⟫ +
      (1 + L₀ / μ) * (L₀ + L₁ * dualNorm N (gPhi H hμ x)) / 2 * N d ^ 2 := by
  have hκ : 1 ≤ 1 + L₀ / μ := by have := div_nonneg hL₀ hμ.le; linarith
  have h := (anchored_descent hR hdef (φ := Phi H hμ) (g := gPhi H hμ)
    (fun z => Phi_hasGradient H hμ hR hdef hL₀ hL₁ z) (x := x) (h := d)
    (M := (1 + L₀ / μ) * (L₀ + L₁ * dualNorm N (gPhi H hμ x)))
    (fun t ht => by
      have hN := apply_nonneg N d
      have hloc : L₁ * ((1 + L₀ / μ) * N (x + t • d - x)) ≤ 1 := by
        rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht.1]
        have h1 : 0 ≤ L₁ * ((1 + L₀ / μ) * N d) := by positivity
        have : L₁ * ((1 + L₀ / μ) * (t * N d)) = t * (L₁ * ((1 + L₀ / μ) * N d)) := by ring
        rw [this]; nlinarith [ht.2]
      have := gPhi_smooth H hμ hR hL₀ hL₁ hκ x (x + t • d) hloc
      rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht.1] at this
      exact this)).1
  have e : (1 + L₀ / μ) * (L₀ + L₁ * dualNorm N (gPhi H hμ x)) / 2 * N d ^ 2 =
      (1 + L₀ / μ) * (L₀ + L₁ * dualNorm N (gPhi H hμ x)) / 2 * N d ^ 2 := rfl
  linarith

include hdef hL₀ hL₁ in
lemma G_initial {t : ℝ} (ht : 0 < t) (htL : 2 * (1 + L₀ / μ) * L₁ * t ≤ 1) :
    dualNorm N (gPhi H hμ x₁) ≤ 4 / 3 * (Δ / t + (1 + L₀ / μ) * L₀ * t / 2) := by
  set G := dualNorm N (gPhi H hμ x₁)
  set K := 1 + L₀ / μ
  have hK : 1 ≤ K := by have := div_nonneg hL₀ hμ.le; simp only [K]; linarith
  have hG : 0 ≤ G := dualNorm_nonneg hR _
  have hB : G ≤ Δ / t + K * (L₀ + L₁ * G) * t / 2 := by
    refine dualNorm_le_of fun v hv => ?_
    have hNv := apply_nonneg N v
    have hNd : N (-(t • v)) = t * N v := by
      rw [map_neg_eq_map, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht]
    have hloc : L₁ * (K * N (-(t • v))) ≤ 1 := by
      rw [hNd]
      have : L₁ * (K * (t * N v)) ≤ L₁ * (K * t) := by
        have : 0 ≤ L₁ * K := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hv (mul_nonneg this ht.le)]
      nlinarith
    have hd := Phi_descent H hμ hR hdef hL₀ hL₁ x₁ (-(t • v)) hloc
    have hgap := Phi_gap H hμ (x₁ + -(t • v))
    rw [hNd, inner_neg_right, inner_smul_right] at hd
    have hNv2 : (t * N v) ^ 2 ≤ t ^ 2 := by
      rw [mul_pow]; nlinarith [pow_le_one₀ (n := 2) hNv hv]
    have hcoef : 0 ≤ K * (L₀ + L₁ * G) / 2 := by positivity
    have h1 : t * ⟪gPhi H hμ x₁, v⟫ ≤ Δ + K * (L₀ + L₁ * G) / 2 * t ^ 2 := by
      have := mul_le_mul_of_nonneg_left hNv2 hcoef
      linarith
    rw [div_add_div _ _ ht.ne' (by norm_num : (2 : ℝ) ≠ 0), le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : G * (1 - K * L₁ * t / 2) ≤ Δ / t + K * L₀ * t / 2 := by nlinarith
  have h3 : 3 / 4 ≤ 1 - K * L₁ * t / 2 := by nlinarith
  nlinarith

end Primal

end OracleTemplate.MinimaxLmo
