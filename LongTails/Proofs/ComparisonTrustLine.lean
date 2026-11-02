import LongTails.Proofs.ComparisonTrustTaylor
import Mathlib.Analysis.Calculus.MeanValue

namespace LongTails.Proofs.ComparisonTrustLine

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion LongTails.Proofs.ComparisonTrustTaylor
  LongTails.Proofs.ComparisonTrustPlans
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → ℝ} {L ρ : ℝ}

def slope (f : E → ℝ) (x u : E) (t : ℝ) : ℝ := -⟪gradient f (x - t • u), u⟫

lemma line_hasDerivAt (h : Smooth f L ρ) (x u : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => f (x - t • u)) (slope f x u t) t := by
  have hline : HasDerivAt (fun t : ℝ => x - t • u) (-u) t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_sub x
  have := (h.hf (x - t • u)).comp_hasDerivAt t hline
  have e : (innerSL ℝ (gradient f (x - t • u))) (-u) = slope f x u t := by
    rw [innerSL_apply_apply, inner_neg_right]
    rfl
  rw [e] at this
  exact this

lemma slope_lip (h : Smooth f L ρ) {x u : E} (hu : ‖u‖ = 1) (t₁ t₂ : ℝ) :
    |slope f x u t₂ - slope f x u t₁| ≤ L * |t₂ - t₁| := by
  unfold slope
  rw [neg_sub_neg, ← inner_sub_left]
  calc _ ≤ ‖gradient f (x - t₁ • u) - gradient f (x - t₂ • u)‖ * ‖u‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ L * ‖(x - t₁ • u) - (x - t₂ • u)‖ * 1 := by rw [hu]; gcongr; exact h.lip _ _
    _ = L * |t₂ - t₁| := by
      rw [show (x - t₁ • u) - (x - t₂ • u) = (t₂ - t₁) • u by module, norm_smul, hu,
        Real.norm_eq_abs]
      ring

lemma slope_taylor (h : Smooth f L ρ) {x u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    |slope f x u t - (-⟪gradient f x, u⟫ + t * ⟪u, fderiv ℝ (gradient f) x u⟫)| ≤
      ρ * t ^ 2 / 2 := by
  have ht := h.grad_taylor x (-(t • u))
  rw [norm_neg, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs] at ht
  unfold slope
  have heq : -⟪gradient f (x - t • u), u⟫ - (-⟪gradient f x, u⟫ + t * ⟪u,
      fderiv ℝ (gradient f) x u⟫) = -⟪gradient f (x + -(t • u)) - gradient f x -
        fderiv ℝ (gradient f) x (-(t • u)), u⟫ := by
    rw [← sub_eq_add_neg]
    simp only [map_neg, map_smul, inner_sub_left, inner_neg_left, real_inner_smul_left]
    rw [real_inner_comm (fderiv ℝ (gradient f) x u) u]
    ring
  rw [heq, abs_neg]
  calc _ ≤ ‖gradient f (x + -(t • u)) - gradient f x - fderiv ℝ (gradient f) x (-(t • u))‖ *
        ‖u‖ := abs_real_inner_le_norm _ _
    _ ≤ ρ * t ^ 2 / 2 := by rw [hu, mul_one]; exact ht

lemma slope_mono (h : Smooth f L ρ) (hρ : 0 ≤ ρ) {x u : E} (hu : ‖u‖ = 1) {r t₁ t₂ : ℝ}
    (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2r : t₂ ≤ r) :
    (t₂ - t₁) * (⟪u, fderiv ℝ (gradient f) x u⟫ - ρ * r) ≤
      slope f x u t₂ - slope f x u t₁ := by
  set y := x - t₁ • u
  have hy : x - t₂ • u = y + -((t₂ - t₁) • u) := by simp only [y]; module
  have ht := h.grad_taylor y (-((t₂ - t₁) • u))
  rw [norm_neg, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs] at ht
  have hH : |⟪u, fderiv ℝ (gradient f) y u⟫ - ⟪u, fderiv ℝ (gradient f) x u⟫| ≤ ρ * t₁ := by
    have e : ⟪u, (fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x) u⟫ =
        ⟪u, fderiv ℝ (gradient f) y u⟫ - ⟪u, fderiv ℝ (gradient f) x u⟫ := by
      rw [FunLike.coe_sub, Pi.sub_apply, inner_sub_right]
    rw [← e]
    calc _ ≤ ‖u‖ * ‖(fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x) u‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ 1 * (‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x‖ * 1) := by
          rw [hu]; gcongr
          have := (fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x).le_opNorm u
          rwa [hu] at this
      _ ≤ ρ * t₁ := by
          rw [one_mul, mul_one]
          refine (h.hess y x).trans ?_
          rw [show y - x = -(t₁ • u) by simp [y], norm_neg, norm_smul, hu, mul_one,
            Real.norm_eq_abs, abs_of_nonneg h0]
  have hrest : slope f x u t₂ - slope f x u t₁ = (t₂ - t₁) * ⟪u, fderiv ℝ (gradient f) y u⟫ -
      ⟪gradient f (y + -((t₂ - t₁) • u)) - gradient f y -
        fderiv ℝ (gradient f) y (-((t₂ - t₁) • u)), u⟫ := by
    unfold slope
    rw [hy]
    simp only [map_neg, map_smul, inner_sub_left, inner_neg_left, real_inner_smul_left]
    rw [real_inner_comm (fderiv ℝ (gradient f) y u) u]
    ring
  have hin : ⟪gradient f (y + -((t₂ - t₁) • u)) - gradient f y -
      fderiv ℝ (gradient f) y (-((t₂ - t₁) • u)), u⟫ ≤ ρ * (t₂ - t₁) ^ 2 / 2 := by
    refine (real_inner_le_norm _ _).trans ?_
    rw [hu, mul_one]
    exact ht
  rw [hrest]
  have hd : 0 ≤ t₂ - t₁ := by linarith
  have := (abs_le.mp hH).1
  have e1 : (t₂ - t₁) * (⟪u, fderiv ℝ (gradient f) x u⟫ - ρ * t₁) ≤
      (t₂ - t₁) * ⟪u, fderiv ℝ (gradient f) y u⟫ := mul_le_mul_of_nonneg_left (by linarith) hd
  have e2 : ρ * (t₂ - t₁) ^ 2 / 2 ≤ (t₂ - t₁) * (ρ * (r - t₁)) := by
    have : t₂ - t₁ ≤ r - t₁ := by linarith
    nlinarith [mul_nonneg hρ hd]
  nlinarith [mul_nonneg hρ hd]

lemma cmp_slope (h : Smooth f L ρ) {x u : E} {r κ m₁ m₂ : ℝ} (hκ : 0 < κ)
    (hmono : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ r → κ * (t₂ - t₁) ≤ slope f x u t₂ - slope f x u t₁)
    (h0 : 0 ≤ m₁) (h12 : m₁ < m₂) (h2 : m₂ ≤ r) :
    (f (x - m₁ • u) ≤ f (x - m₂ • u) → 0 ≤ slope f x u m₂) ∧
      (¬ f (x - m₁ • u) ≤ f (x - m₂ • u) → slope f x u m₁ ≤ 0) := by
  have hcont : ContinuousOn (fun t : ℝ => f (x - t • u)) (Set.Icc m₁ m₂) := fun t _ =>
    (line_hasDerivAt h x u t).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => f (x - t • u))
    (slope f x u) h12 hcont (fun t _ => line_hasDerivAt h x u t)
  have hpos : 0 < m₂ - m₁ := by linarith
  have hdiff : f (x - m₂ • u) - f (x - m₁ • u) = slope f x u ξ * (m₂ - m₁) := by
    rw [hξeq]
    field_simp
  constructor
  · intro hle
    by_contra hneg
    push Not at hneg
    have := hmono ξ m₂ (by linarith [hξ.1]) hξ.2.le h2
    have hsξ : slope f x u ξ < 0 := by nlinarith [hξ.2]
    have : f (x - m₂ • u) - f (x - m₁ • u) < 0 := by rw [hdiff]; nlinarith
    linarith
  · intro hlt
    push Not at hlt
    by_contra hpos'
    push Not at hpos'
    have := hmono m₁ ξ h0 hξ.1.le (by linarith [hξ.2])
    have hsξ : 0 < slope f x u ξ := by nlinarith [hξ.1]
    have : 0 < f (x - m₂ • u) - f (x - m₁ • u) := by rw [hdiff]; nlinarith
    linarith

def ternaryPure (f : E → ℝ) (x u : E) (mt : ℕ) (r : ℝ) : ℝ × ℝ :=
  loopPure (fun _ lh => if decide (f (x - (lh.1 + (lh.2 - lh.1) / 3) • u) ≤
      f (x - (lh.2 - (lh.2 - lh.1) / 3) • u)) then (lh.1, lh.2 - (lh.2 - lh.1) / 3)
    else (lh.1 + (lh.2 - lh.1) / 3, lh.2)) mt 0 (0, r)

omit [FiniteDimensional ℝ E] in
lemma eval_ternaryPlan (t : Tuning) (x u : E) :
    QueryPlan.eval (fun q : E × E => decide (f q.1 ≤ f q.2)) (ternaryPlan t x u) =
      ternaryPure f x u t.mt t.r := by
  simp only [ternaryPlan, eval_loop, ternaryStep, QueryPlan.eval_map, eval_cmpPlan, ternaryPure]
  rfl

lemma ternary_spec (h : Smooth f L ρ) {x u : E} {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hmono : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ r → κ * (t₂ - t₁) ≤ slope f x u t₂ - slope f x u t₁)
    (hs0 : slope f x u 0 ≤ 0) (hsr : 0 ≤ slope f x u r) (mt : ℕ) :
    let lh := ternaryPure f x u mt r
    0 ≤ lh.1 ∧ lh.1 ≤ lh.2 ∧ lh.2 ≤ r ∧ lh.2 - lh.1 = r * (2 / 3) ^ mt ∧
      slope f x u lh.1 ≤ 0 ∧ 0 ≤ slope f x u lh.2 := by
  have key := loopPure_induction
    (fun _ lh => if decide (f (x - (lh.1 + (lh.2 - lh.1) / 3) • u) ≤
      f (x - (lh.2 - (lh.2 - lh.1) / 3) • u)) then (lh.1, lh.2 - (lh.2 - lh.1) / 3)
      else (lh.1 + (lh.2 - lh.1) / 3, lh.2))
    (fun k lh => 0 ≤ lh.1 ∧ lh.1 ≤ lh.2 ∧ lh.2 ≤ r ∧ lh.2 - lh.1 = r * (2 / 3) ^ k ∧
      slope f x u lh.1 ≤ 0 ∧ 0 ≤ slope f x u lh.2)
    (0, r) ⟨le_rfl, hr.le, le_rfl, by simp, hs0, hsr⟩
    (fun k lh ⟨h1, h2, h3, h4, h5, h6⟩ => by
      have hw : 0 < lh.2 - lh.1 := by rw [h4]; positivity
      have hm : lh.1 + (lh.2 - lh.1) / 3 < lh.2 - (lh.2 - lh.1) / 3 := by linarith
      obtain ⟨c1, c2⟩ := cmp_slope h hκ hmono (by linarith) hm (by linarith)
      have hp : r * (2 / 3) ^ (k + 1) = (lh.2 - lh.1) * (2 / 3) := by rw [pow_succ, h4]; ring
      by_cases hc : f (x - (lh.1 + (lh.2 - lh.1) / 3) • u) ≤ f (x - (lh.2 - (lh.2 - lh.1) / 3) • u)
      · simp only [hc, decide_true, ↓reduceIte]
        exact ⟨h1, by linarith, by linarith, by rw [hp]; ring, h5, c1 hc⟩
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by linarith, by linarith, h3, by rw [hp]; ring, c2 hc, h6⟩) mt
  exact key

omit [FiniteDimensional ℝ E] in
lemma inner_unit_gap {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    1 - ⟪u, v⟫ = ‖u - v‖ ^ 2 / 2 := by
  rw [norm_sub_sq_real, hu, hv]
  ring

set_option maxHeartbeats 800000 in
theorem radial_estimate (h : Smooth f L ρ) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) {x u : E} {c δ0 r : ℝ}
    (hc : ‖gradient f x‖ = c) (hcpos : 0 < c) (hu : ‖u‖ = 1)
    (hδ0 : ‖u - c⁻¹ • gradient f x‖ ≤ δ0) (hδ1 : δ0 ≤ 1) (hr : 0 < r)
    (hρr : ρ * r ^ 2 ≤ c / 16)
    (hcurved : 4 * c / r ≤ ⟪u, fderiv ℝ (gradient f) x u⟫) (mt : ℕ) :
    let hi := (ternaryPure f x u mt r).2
    c / (2 * L + ρ * r) ≤ hi ∧ hi ≤ 16 / 63 * r + r * (2 / 3) ^ mt ∧
      |c / hi - ⟪u, fderiv ℝ (gradient f) x u⟫| ≤
        (c * δ0 ^ 2 / 2 + L * (r * (2 / 3) ^ mt)) / hi + ρ * hi / 2 := by
  intro hi
  have hhi : hi = (ternaryPure f x u mt r).2 := rfl
  clear_value hi
  set hu' := ⟪u, fderiv ℝ (gradient f) x u⟫ with hhu
  set g := gradient f x with hgdef
  set ν := c⁻¹ • g
  have hν : ‖ν‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos, hc, inv_mul_cancel₀ hcpos.ne']
  have hgu : ⟪g, u⟫ = c * ⟪ν, u⟫ := by
    rw [show g = c • ν by rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul], real_inner_smul_left]
  have hgap := inner_unit_gap hν hu
  have hνu : ‖ν - u‖ ≤ δ0 := by rw [norm_sub_rev]; exact hδ0
  have hcg : 0 ≤ c - ⟪g, u⟫ ∧ c - ⟪g, u⟫ ≤ c * δ0 ^ 2 / 2 := by
    rw [hgu]
    constructor
    · have : 0 ≤ 1 - ⟪ν, u⟫ := by rw [hgap]; positivity
      nlinarith
    · have : 1 - ⟪ν, u⟫ ≤ δ0 ^ 2 / 2 := by
        rw [hgap]
        have := pow_le_pow_left₀ (norm_nonneg _) hνu 2
        linarith
      nlinarith
  have hgu_pos : c / 2 ≤ ⟪g, u⟫ := by
    have : c * δ0 ^ 2 / 2 ≤ c / 2 := by
      have : δ0 ^ 2 ≤ 1 := by nlinarith [abs_nonneg δ0, norm_nonneg (ν - u)]
      nlinarith
    linarith [hcg.2]
  have hκ : (63 / 16) * c / r ≤ hu' - ρ * r := by
    have : ρ * r ≤ c / (16 * r) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have : c / (16 * r) = (1 / 16) * (c / r) := by field_simp
    have : 4 * c / r = 4 * (c / r) := by ring
    have : 63 / 16 * c / r = (63 / 16) * (c / r) := by ring
    linarith
  have hκpos : 0 < hu' - ρ * r := lt_of_lt_of_le (by positivity) hκ
  have hmono : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ r →
      (hu' - ρ * r) * (t₂ - t₁) ≤ slope f x u t₂ - slope f x u t₁ := by
    intro t₁ t₂ h0 h12 h2
    have := slope_mono (x := x) h hρ hu h0 h12 h2
    linarith [mul_comm (t₂ - t₁) (hu' - ρ * r)]
  have hs0 : slope f x u 0 ≤ 0 := by
    simp only [slope, zero_smul, sub_zero]
    linarith
  have hsr : 0 ≤ slope f x u r := by
    have h1 := hmono 0 r le_rfl hr.le le_rfl
    have : slope f x u 0 = -⟪g, u⟫ := by simp only [slope, zero_smul, sub_zero]; rfl
    have : (63 / 16) * c ≤ (hu' - ρ * r) * r := by
      have := mul_le_mul_of_nonneg_right hκ hr.le
      rwa [div_mul_cancel₀ _ hr.ne'] at this
    have : ⟪g, u⟫ ≤ c := by linarith [hcg.1]
    nlinarith
  obtain ⟨hl0, hlh, hhr, hw, hsl, hsh⟩ := ternary_spec h hr hκpos hmono hs0 hsr mt
  rw [← hhi] at hlh hhr hw hsh
  have hlo : (ternaryPure f x u mt r).1 ≤ 16 / 63 * r := by
    by_contra hcon
    push Not at hcon
    have h1 := hmono 0 _ le_rfl hl0 (by linarith)
    have : slope f x u 0 = -⟪g, u⟫ := by simp only [slope, zero_smul, sub_zero]; rfl
    have : c < (hu' - ρ * r) * (ternaryPure f x u mt r).1 := by
      have h2 : (63 / 16) * c / r * (16 / 63 * r) = c := by field_simp
      have h3 := mul_le_mul_of_nonneg_left hcon.le hκpos.le
      nlinarith
    have : ⟪g, u⟫ ≤ c := by linarith [hcg.1]
    nlinarith
  have hsl_hi : slope f x u hi ≤ L * (r * (2 / 3) ^ mt) := by
    have := slope_lip (x := x) h hu (ternaryPure f x u mt r).1 hi
    rw [abs_of_nonneg (by linarith : 0 ≤ hi - (ternaryPure f x u mt r).1), hw] at this
    have := (abs_le.mp this).2
    linarith
  have htay := slope_taylor (x := x) h hu hi
  rw [← hhu, ← hgdef] at htay
  have hhi_pos : 0 < hi := by
    by_contra hcon
    push Not at hcon
    have : hi = 0 := le_antisymm hcon (by linarith)
    rw [this] at hsh
    have e0 : slope f x u 0 = -⟪g, u⟫ := by simp only [slope, zero_smul, sub_zero]; rfl
    rw [e0] at hsh
    linarith
  have hu'_le : hu' ≤ L := by
    have := abs_real_inner_le_norm u (fderiv ℝ (gradient f) x u)
    have h2 : ‖fderiv ℝ (gradient f) x u‖ ≤ L * ‖u‖ :=
      ((fderiv ℝ (gradient f) x).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (h.hess_norm hL x) (norm_nonneg u))
    rw [hu] at this h2
    linarith [(abs_le.mp this).2]
  refine ⟨?_, by linarith, ?_⟩
  · have h4c : 0 < 4 * c / r := by positivity
    have hpos2 : 0 < 2 * L + ρ * r := by nlinarith [mul_nonneg hρ hr.le]
    rw [div_le_iff₀ hpos2]
    have ht2 := (abs_le.mp htay).2
    have h5 : hi * hu' ≤ hi * L := mul_le_mul_of_nonneg_left hu'_le hhi_pos.le
    have h6 : ρ * hi * hi ≤ ρ * hi * r := mul_le_mul_of_nonneg_left hhr (mul_nonneg hρ hhi_pos.le)
    linarith
  · have heq : c / hi - hu' = ((c - ⟪g, u⟫) - slope f x u hi +
        (slope f x u hi - (-⟪g, u⟫ + hi * hu'))) / hi := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hhi_pos]
    have hnum : |(c - ⟪g, u⟫) - slope f x u hi + (slope f x u hi - (-⟪g, u⟫ + hi * hu'))| ≤
        c * δ0 ^ 2 / 2 + L * (r * (2 / 3) ^ mt) + ρ * hi ^ 2 / 2 := by
      have := abs_add_le ((c - ⟪g, u⟫) - slope f x u hi) (slope f x u hi - (-⟪g, u⟫ + hi * hu'))
      have : |(c - ⟪g, u⟫) - slope f x u hi| ≤ c * δ0 ^ 2 / 2 + L * (r * (2 / 3) ^ mt) := by
        rw [abs_le]
        constructor <;> linarith [hcg.1, hcg.2]
      linarith
    calc _ ≤ (c * δ0 ^ 2 / 2 + L * (r * (2 / 3) ^ mt) + ρ * hi ^ 2 / 2) / hi :=
          div_le_div_of_nonneg_right hnum hhi_pos.le
      _ = _ := by
        rw [add_div, div_div, show ρ * hi ^ 2 / (2 * hi) = ρ * hi / 2 by
          rw [div_eq_iff (by positivity)]; ring]

end

end LongTails.Proofs.ComparisonTrustLine
