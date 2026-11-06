import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HessianStableNewton

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def qf (H : E →L[ℝ] E) (v : E) : ℝ := ⟪H v, v⟫

lemma polarization {Δ H : E →L[ℝ] E} {κ : ℝ}
    (hΔ : ∀ u v, ⟪Δ u, v⟫ = ⟪u, Δ v⟫) (hH : ∀ v, 0 ≤ qf H v)
    (hb : ∀ v, |qf Δ v| ≤ κ * qf H v) (u v : E) :
    ⟪Δ u, v⟫ ≤ κ * Real.sqrt (qf H u) * Real.sqrt (qf H v) := by
  have hκ : 0 ≤ κ ∨ ∀ w, qf H w = 0 := by
    by_cases h : ∃ w, 0 < qf H w
    · obtain ⟨w, hw⟩ := h
      left
      have := (abs_nonneg _).trans (hb w)
      exact nonneg_of_mul_nonneg_left this hw
    · right
      intro w
      exact le_antisymm (not_lt.mp fun hw => h ⟨w, hw⟩) (hH w)
  have key : ∀ t : ℝ, 0 < t → 4 * ⟪Δ u, v⟫ ≤ 2 * κ * (t ^ 2 * qf H u + qf H v / t ^ 2) := by
    intro t ht
    have e1 : 4 * ⟪Δ u, v⟫ = qf Δ (t • u + t⁻¹ • v) - qf Δ (t • u - t⁻¹ • v) := by
      unfold qf
      simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right, real_inner_smul_left, real_inner_smul_right]
      rw [hΔ v u, real_inner_comm (Δ u) v]
      field_simp
      ring
    have e2 : qf H (t • u + t⁻¹ • v) + qf H (t • u - t⁻¹ • v) =
        2 * (t ^ 2 * qf H u + qf H v / t ^ 2) := by
      unfold qf
      simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right, real_inner_smul_left, real_inner_smul_right]
      field_simp
      ring
    have h1 := hb (t • u + t⁻¹ • v)
    have h2 := hb (t • u - t⁻¹ • v)
    have h1' := le_abs_self (qf Δ (t • u + t⁻¹ • v))
    have h2' := neg_abs_le (qf Δ (t • u - t⁻¹ • v))
    have e3 : κ * qf H (t • u + t⁻¹ • v) + κ * qf H (t • u - t⁻¹ • v) =
        2 * κ * (t ^ 2 * qf H u + qf H v / t ^ 2) := by
      rw [← mul_add, e2]; ring
    rw [e1]
    linarith
  generalize hxd : ⟪Δ u, v⟫ = x at key ⊢
  set A := qf H u
  set B := qf H v
  have hA : 0 ≤ A := hH u
  have hB : 0 ≤ B := hH v
  rcases hκ with hκ | hz
  · rcases eq_or_lt_of_le hA with hA0 | hA0
    · rw [← hA0, Real.sqrt_zero, mul_zero, zero_mul]
      by_contra hx
      have hx' : 0 < x := lt_of_not_ge hx
      rcases eq_or_lt_of_le (mul_nonneg hκ hB) with h0 | h0
      · have := key 1 one_pos
        rw [← hA0] at this
        nlinarith
      · have ht : 0 < Real.sqrt (κ * B / x) := Real.sqrt_pos.mpr (by positivity)
        have := key _ ht
        rw [← hA0, Real.sq_sqrt (by positivity)] at this
        have hκ0 : κ ≠ 0 := fun h => by rw [h, zero_mul] at h0; exact lt_irrefl _ h0
        have hB0' : B ≠ 0 := fun h => by rw [h, mul_zero] at h0; exact lt_irrefl _ h0
        have e : 2 * κ * (κ * B / x * 0 + B / (κ * B / x)) = 2 * x := by
          field_simp
          ring
        rw [e] at this
        linarith
    · rcases eq_or_lt_of_le hB with hB0 | hB0
      · rw [← hB0, Real.sqrt_zero, mul_zero]
        by_contra hx
        have hx' : 0 < x := lt_of_not_ge hx
        rcases eq_or_lt_of_le (mul_nonneg hκ hA) with h0 | h0
        · have := key 1 one_pos
          rw [← hB0] at this
          nlinarith
        · have ht : 0 < Real.sqrt (x / (κ * A)) := Real.sqrt_pos.mpr (by positivity)
          have := key _ ht
          rw [← hB0, Real.sq_sqrt (by positivity)] at this
          have hκ0 : κ ≠ 0 := fun h => by rw [h, zero_mul] at h0; exact lt_irrefl _ h0
          have hA0' : A ≠ 0 := fun h => by rw [h, mul_zero] at h0; exact lt_irrefl _ h0
          have e : 2 * κ * (x / (κ * A) * A + 0 / (x / (κ * A))) = 2 * x := by
            field_simp
            ring
          rw [e] at this
          linarith
      · have hsA := Real.sqrt_pos.mpr hA0
        have hsB := Real.sqrt_pos.mpr hB0
        have ht : 0 < Real.sqrt (Real.sqrt B / Real.sqrt A) :=
          Real.sqrt_pos.mpr (div_pos hsB hsA)
        have := key _ ht
        rw [Real.sq_sqrt (div_pos hsB hsA).le] at this
        have e : Real.sqrt B / Real.sqrt A * A + B / (Real.sqrt B / Real.sqrt A) =
            2 * (Real.sqrt A * Real.sqrt B) := by
          have hA' : A = Real.sqrt A ^ 2 := (Real.sq_sqrt hA).symm
          have hB' : B = Real.sqrt B ^ 2 := (Real.sq_sqrt hB).symm
          rw [hA', hB']
          rw [Real.sqrt_sq hsA.le, Real.sqrt_sq hsB.le]
          field_simp
          ring
        rw [e] at this
        nlinarith
  · have hAz : A = 0 := hz u
    have hBz : B = 0 := hz v
    rw [hAz, Real.sqrt_zero, mul_zero, zero_mul]
    have h := hb (u + v)
    have h' := hb (u - v)
    have e1 : 4 * ⟪Δ u, v⟫ = qf Δ (u + v) - qf Δ (u - v) := by
      unfold qf
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hΔ v u, real_inner_comm (Δ u) v]
      ring
    rw [hxd] at e1
    rw [hz (u + v)] at h
    rw [hz (u - v)] at h'
    have := abs_nonneg (qf Δ (u + v))
    have := abs_nonneg (qf Δ (u - v))
    nlinarith [le_abs_self (qf Δ (u + v)), neg_abs_le (qf Δ (u - v))]

lemma qf_sub (A B : E →L[ℝ] E) (v : E) : qf (A - B) v = qf A v - qf B v := by
  unfold qf
  rw [sub_apply, inner_sub_left]

lemma stab_diff {Hx Hy : E →L[ℝ] E} {s : ℝ} (hs : 1 ≤ s)
    (h1 : ∀ v, qf Hy v ≤ s * qf Hx v) (h2 : ∀ v, qf Hx v ≤ s * qf Hy v)
    (hpos : ∀ v, 0 ≤ qf Hx v) (v : E) :
    |qf (Hy - Hx) v| ≤ (s - 1) * qf Hx v := by
  rw [qf_sub, abs_le]
  have a1 := h1 v
  have a2 := h2 v
  have a3 := hpos v
  have hs0 : 0 < s := by linarith
  have hy : qf Hx v / s ≤ qf Hy v := by rw [div_le_iff₀ hs0]; linarith
  have hq : qf Hx v / s ≥ (2 - s) * qf Hx v := by
    rw [ge_iff_le, le_div_iff₀ hs0]
    nlinarith [sq_nonneg (s - 1)]
  constructor <;> nlinarith

lemma norm_apply_le_of_qf {H : E →L[ℝ] E} (hsa : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (hpos : ∀ v, 0 ≤ qf H v) {q : ℝ} (hq : ∀ v, qf H v ≤ q * ‖v‖ ^ 2) (w : E) :
    ‖H w‖ ≤ q * ‖w‖ := by
  have hb : ∀ v, |qf H v| ≤ 1 * qf H v := fun v => by rw [one_mul, abs_of_nonneg (hpos v)]
  have hp := polarization hsa hpos hb w (H w)
  have hq0 : 0 ≤ q ∨ ‖w‖ = 0 := by
    by_cases hw : ‖w‖ = 0
    · exact Or.inr hw
    · left
      have hw' : 0 < ‖w‖ ^ 2 := by positivity
      have := (hpos w).trans (hq w)
      exact nonneg_of_mul_nonneg_left this hw'
  rcases hq0 with hq0 | hw0
  · have e1 : ⟪H w, H w⟫ = ‖H w‖ ^ 2 := real_inner_self_eq_norm_sq _
    have s1 : Real.sqrt (qf H w) ≤ Real.sqrt q * ‖w‖ := by
      rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul hq0]
      exact Real.sqrt_le_sqrt (hq w)
    have s2 : Real.sqrt (qf H (H w)) ≤ Real.sqrt q * ‖H w‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (H w)), ← Real.sqrt_mul hq0]
      exact Real.sqrt_le_sqrt (hq (H w))
    have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
    have h3 : ‖H w‖ ^ 2 ≤ q * ‖w‖ * ‖H w‖ := by
      rw [← e1]
      calc ⟪H w, H w⟫ ≤ 1 * Real.sqrt (qf H w) * Real.sqrt (qf H (H w)) := hp
        _ ≤ 1 * (Real.sqrt q * ‖w‖) * (Real.sqrt q * ‖H w‖) := by
          gcongr
        _ = q * ‖w‖ * ‖H w‖ := by linear_combination ‖w‖ * ‖H w‖ * hsq
    rcases eq_or_lt_of_le (norm_nonneg (H w)) with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  · have : w = 0 := norm_eq_zero.mp hw0
    subst this
    simp

def qN (a : ℝ) (H : E →L[ℝ] E) (v : E) : ℝ := ‖v‖ ^ 2 + a * qf H v

lemma newton_core {Ht Hξ S : E →L[ℝ] E} {a κ : ℝ} (ha : 0 ≤ a)
    (hS : ∀ v, ⟪S v, v⟫ = 0)
    (hsa : ∀ u v, ⟪(Ht - Hξ) u, v⟫ = ⟪u, (Ht - Hξ) v⟫)
    (hpos : ∀ v, 0 ≤ qf Ht v) (hb : ∀ v, |qf (Ht - Hξ) v| ≤ κ * qf Ht v)
    {e e' : E}
    (hkey : ⟪e + a • ((Hξ + S) e), e'⟫ + ⟪(e' - e) + a • ((Ht + S) (e' - e)), e'⟫ ≤ 0) :
    qN a Ht e' ≤ κ ^ 2 * qN a Ht e := by
  have h1 : qN a Ht e' ≤ a * ⟪(Ht - Hξ) e, e'⟫ := by
    unfold qN qf
    have hSe := hS e'
    simp only [add_apply, sub_apply, map_sub,
      inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hkey ⊢
    nlinarith [hSe]
  have hp := polarization hsa hpos hb e e'
  have hκ : 0 ≤ κ ∨ (∀ w, qf Ht w = 0) := by
    by_cases h : ∃ w, 0 < qf Ht w
    · obtain ⟨w, hw⟩ := h
      left
      exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hb w)) hw
    · right
      intro w
      exact le_antisymm (not_lt.mp fun hw => h ⟨w, hw⟩) (hpos w)
  have hqe : a * qf Ht e ≤ qN a Ht e := by unfold qN; nlinarith [sq_nonneg ‖e‖]
  have hqe' : a * qf Ht e' ≤ qN a Ht e' := by unfold qN; nlinarith [sq_nonneg ‖e'‖]
  have hN0 : 0 ≤ qN a Ht e := by unfold qN; have := hpos e; positivity
  have hN0' : 0 ≤ qN a Ht e' := by unfold qN; have := hpos e'; positivity
  rcases hκ with hκ | hz
  · have h2 : a * ⟪(Ht - Hξ) e, e'⟫ ≤ κ * (Real.sqrt (qN a Ht e) * Real.sqrt (qN a Ht e')) := by
      have h3 : a * (κ * Real.sqrt (qf Ht e) * Real.sqrt (qf Ht e')) =
          κ * (Real.sqrt (a * qf Ht e) * Real.sqrt (a * qf Ht e')) := by
        rw [Real.sqrt_mul ha, Real.sqrt_mul ha]
        have : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha
        linear_combination (-(κ * Real.sqrt (qf Ht e) * Real.sqrt (qf Ht e'))) * this
      calc a * ⟪(Ht - Hξ) e, e'⟫ ≤ a * (κ * Real.sqrt (qf Ht e) * Real.sqrt (qf Ht e')) :=
            mul_le_mul_of_nonneg_left hp ha
        _ = κ * (Real.sqrt (a * qf Ht e) * Real.sqrt (a * qf Ht e')) := h3
        _ ≤ κ * (Real.sqrt (qN a Ht e) * Real.sqrt (qN a Ht e')) := by
          gcongr
    have h4 : qN a Ht e' ≤ κ * (Real.sqrt (qN a Ht e) * Real.sqrt (qN a Ht e')) :=
      h1.trans h2
    have se := Real.sq_sqrt hN0
    have se' := Real.sq_sqrt hN0'
    have hs0 := Real.sqrt_nonneg (qN a Ht e)
    have hs0' := Real.sqrt_nonneg (qN a Ht e')
    rcases eq_or_lt_of_le hs0' with hz' | hz'
    · rw [← se', ← hz']
      have := mul_nonneg (sq_nonneg κ) hN0
      nlinarith
    · have h5 : Real.sqrt (qN a Ht e') ≤ κ * Real.sqrt (qN a Ht e) := by
        rw [← se'] at h4
        nlinarith
      have h6 := pow_le_pow_left₀ hs0' h5 2
      rw [se', mul_pow, se] at h6
      exact h6
  · have hz2 : ∀ w, a * qf Ht w = 0 := fun w => by rw [hz w, mul_zero]
    have h0 : ⟪(Ht - Hξ) e, e'⟫ ≤ 0 := by
      have := hp
      simp only [hz e, hz e', Real.sqrt_zero, mul_zero] at this
      exact this
    have : qN a Ht e' ≤ 0 := by nlinarith [mul_nonneg ha (neg_nonneg.mpr h0)]
    have := mul_nonneg (sq_nonneg κ) hN0
    linarith

lemma exp_quarter_le : Real.exp (1 / 4) ≤ 4 / 3 := by
  have h2 : Real.exp (1 / 4) ≤ 1 / (1 - 1 / 4) := by
    have := Real.exp_neg (1 / 4)
    have h3 : 1 - 1 / 4 ≤ Real.exp (-(1 / 4)) := by linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
    rw [Real.exp_neg] at h3
    have hpos := Real.exp_pos (1 / 4)
    rw [le_div_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left h3 hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at this
    linarith
  linarith [h2, show (1 : ℝ) / (1 - 1 / 4) = 4 / 3 by norm_num]

end LongTails.Proofs.HessianStableNewton
