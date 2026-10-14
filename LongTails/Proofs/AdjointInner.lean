import LongTails.Proofs.AdjointLocal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def res (L ρ : ℝ) (F : E → E) (t v : E) : E := v + (2 * ρ + 1 / L) • F v - t

noncomputable def innerStep (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (t v : E) : E :=
  v - stepSize L L₂ ρ (res L ρ F t v) •
    (res L ρ F t v + (2 * ρ + 1 / L) • adj v (res L ρ F t v))

noncomputable def innerRun (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (t v : E) (N : ℕ) : E :=
  (innerStep L L₂ ρ F adj t)^[N] v

lemma gam_L {L ρ : ℝ} (hL : 0 < L) : 1 + (2 * ρ + 1 / L) * L = 2 + 2 * ρ * L := by
  field_simp; ring

omit [InnerProductSpace ℝ E] in
lemma stepSize_nonneg (L L₂ ρ : ℝ) (r : E) : 0 ≤ stepSize L L₂ ρ r := by
  unfold stepSize
  have : 0 < max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖r‖) := lt_max_of_lt_left one_pos
  positivity

lemma res_step [FiniteDimensional ℝ E] {F : E → E} {J : E → E →L[ℝ] E} {L L₂ ρ : ℝ}
    (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ) {adj : E → E → E}
    (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (t v : E) :
    ‖res L ρ F t (innerStep L L₂ ρ F adj t v)‖ ≤ ‖res L ρ F t v‖ -
      (1 / (4 * (2 + 2 * ρ * L) ^ 2)) * ‖res L ρ F t v‖ /
        max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t v‖) := by
  have hγ0 : 0 ≤ 2 * ρ + 1 / L := by positivity
  have hγ : 2 * ρ ≤ 2 * ρ + 1 / L := by
    have : 0 < 1 / L := by positivity
    linarith
  have hgL : 1 + (2 * ρ + 1 / L) * L = 2 + 2 * ρ * L := gam_L hL
  have hΛpos : 0 < 2 + 2 * ρ * L := by positivity
  have hM1 : 1 ≤ max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t v‖) := le_max_left _ _
  have hMpos : 0 < max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t v‖) :=
    lt_of_lt_of_le one_pos hM1
  have hα : stepSize L L₂ ρ (res L ρ F t v) =
      1 / (2 + 2 * ρ * L) ^ 2 / max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t v‖) := rfl
  have hα0 := stepSize_nonneg L L₂ ρ (res L ρ F t v)
  have hα1 : stepSize L L₂ ρ (res L ρ F t v) * (1 + (2 * ρ + 1 / L) * L) ^ 2 ≤ 1 := by
    rw [hgL, hα, div_mul_eq_mul_div, div_le_one hMpos]
    have : 1 / (2 + 2 * ρ * L) ^ 2 * (2 + 2 * ρ * L) ^ 2 = 1 := by field_simp
    rw [this]; exact hM1
  have hE : (2 * ρ + 1 / L) * L₂ * stepSize L L₂ ρ (res L ρ F t v) ^ 2 *
      (1 + (2 * ρ + 1 / L) * L) ^ 2 * ‖res L ρ F t v‖ ^ 2 ≤
      stepSize L L₂ ρ (res L ρ F t v) / 4 * ‖res L ρ F t v‖ := by
    rw [hgL, hα]
    set M := max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t v‖) with hM
    set Λ := 2 + 2 * ρ * L with hΛ
    set x := ‖res L ρ F t v‖ with hx
    have hle : 4 * (2 * ρ + 1 / L) * L₂ * x ≤ M := le_max_right _ _
    have hx0 : 0 ≤ x := norm_nonneg _
    have e : 1 / Λ ^ 2 / M / 4 * x - (2 * ρ + 1 / L) * L₂ * (1 / Λ ^ 2 / M) ^ 2 * Λ ^ 2 * x ^ 2 =
        x / (4 * Λ ^ 2 * M ^ 2) * (M - 4 * (2 * ρ + 1 / L) * L₂ * x) := by
      field_simp
    have hnn : 0 ≤ x / (4 * Λ ^ 2 * M ^ 2) * (M - 4 * (2 * ρ + 1 / L) * L₂ * x) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hle)
    linarith
  have key := step_decrease h hL.le hL₂ hγ hγ0 hα0 hα1 t v (adj v (res L ρ F t v))
    (fun y => hadj v _ y) hE
  refine key.trans (le_of_eq ?_)
  rw [show (v + (2 * ρ + 1 / L) • F v - t) = res L ρ F t v from rfl, hα]
  field_simp

lemma run_length {x : ℕ → ℝ} {c κ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hκ : 0 ≤ κ)
    (hx0 : ∀ j, 0 ≤ x j) (hx : ∀ j, x (j + 1) ≤ x j - c * x j / max 1 (κ * x j)) (i : ℕ) :
    x (⌈κ * x 0 / c⌉₊ + i) ≤ (1 - c) ^ i * x 0 := by
  have hmaxpos : ∀ j, 0 < max 1 (κ * x j) := fun j => lt_max_of_lt_left one_pos
  have hdec_nn : ∀ j, 0 ≤ c * x j / max 1 (κ * x j) := fun j =>
    div_nonneg (mul_nonneg hc.le (hx0 j)) (hmaxpos j).le
  have hmono : ∀ j, x (j + 1) ≤ x j := fun j => (hx j).trans (by linarith [hdec_nn j])
  have hanti : ∀ a b, a ≤ b → x b ≤ x a := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact (hmono n).trans ih
  set P := ⌈κ * x 0 / c⌉₊ with hP
  have hsmall : κ * x P ≤ 1 := by
    by_cases hκ0 : κ = 0
    · rw [hκ0, zero_mul]; exact zero_le_one
    have hκpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hκ0)
    by_cases hall : ∀ j < P, 1 < κ * x j
    · have hstep : ∀ j < P, x (j + 1) ≤ x j - c / κ := by
        intro j hj
        have h1 := hall j hj
        have hm : max 1 (κ * x j) = κ * x j := max_eq_right h1.le
        have := hx j
        rw [hm] at this
        have hxpos : 0 < x j := by
          by_contra hneg
          push Not at hneg
          nlinarith [hx0 j]
        have e : c * x j / (κ * x j) = c / κ := by field_simp
        rw [e] at this; exact this
      have hsum : ∀ j ≤ P, x j ≤ x 0 - j * (c / κ) := by
        intro j hj
        induction j with
        | zero => simp
        | succ j ih =>
          have h1 := hstep j (by omega)
          have h2 := ih (by omega)
          push_cast; linarith
      have h1 := hsum P le_rfl
      have hPge : κ * x 0 / c ≤ P := Nat.le_ceil _
      have h2 : x 0 ≤ P * (c / κ) := by
        rw [div_le_iff₀ hc] at hPge
        rw [mul_div_assoc', le_div_iff₀ hκpos]; linarith
      have : x P ≤ 0 := by linarith
      nlinarith [hx0 P]
    · push Not at hall
      obtain ⟨j, hj, hjle⟩ := hall
      exact (mul_le_mul_of_nonneg_left (hanti j P hj.le) hκ).trans hjle
  have hgeo : ∀ i, x (P + i) ≤ (1 - c) ^ i * x P := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hs : κ * x (P + i) ≤ 1 :=
        (mul_le_mul_of_nonneg_left (hanti P (P + i) (by omega)) hκ).trans hsmall
      have hm : max 1 (κ * x (P + i)) = 1 := max_eq_left hs
      have := hx (P + i)
      rw [hm, div_one] at this
      have h1c : 0 ≤ 1 - c := by linarith
      calc x (P + (i + 1)) = x (P + i + 1) := by rw [Nat.add_succ]
        _ ≤ (1 - c) * x (P + i) := by linarith
        _ ≤ (1 - c) * ((1 - c) ^ i * x P) := mul_le_mul_of_nonneg_left ih h1c
        _ = (1 - c) ^ (i + 1) * x P := by ring
  calc x (P + i) ≤ (1 - c) ^ i * x P := hgeo i
    _ ≤ (1 - c) ^ i * x 0 :=
        mul_le_mul_of_nonneg_left (hanti 0 P (Nat.zero_le _)) (pow_nonneg (by linarith) i)

lemma inner_guarantee [FiniteDimensional ℝ E] {F : E → E} {J : E → E →L[ℝ] E} {L L₂ ρ : ℝ}
    (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ) {adj : E → E → E}
    (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (t v : E) :
    ‖res L ρ F t (innerRun L L₂ ρ F adj t v (innerLen L L₂ ρ ‖res L ρ F t v‖))‖ ≤
      ‖res L ρ F t v‖ / (11 + 10 * ρ * L) := by
  have hΛpos : 0 < 2 + 2 * ρ * L := by positivity
  have hc : 0 < 1 / (4 * (2 + 2 * ρ * L) ^ 2) := by positivity
  have hc1 : 1 / (4 * (2 + 2 * ρ * L) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : 2 ≤ 2 + 2 * ρ * L := by nlinarith [mul_nonneg hρ hL.le]
    nlinarith
  have hκ : 0 ≤ 4 * (2 * ρ + 1 / L) * L₂ := by positivity
  let x : ℕ → ℝ := fun j => ‖res L ρ F t (innerRun L L₂ ρ F adj t v j)‖
  have hx0 : ∀ j, 0 ≤ x j := fun j => norm_nonneg _
  have hx : ∀ j, x (j + 1) ≤ x j - 1 / (4 * (2 + 2 * ρ * L) ^ 2) * x j /
      max 1 (4 * (2 * ρ + 1 / L) * L₂ * x j) := by
    intro j
    have := res_step h hL hL₂ hρ hadj t (innerRun L L₂ ρ F adj t v j)
    have e : innerRun L L₂ ρ F adj t v (j + 1) =
        innerStep L L₂ ρ F adj t (innerRun L L₂ ρ F adj t v j) := by
      simp only [innerRun, Function.iterate_succ_apply']
    show ‖res L ρ F t (innerRun L L₂ ρ F adj t v (j + 1))‖ ≤ _
    rw [e]; exact this
  have hrl := run_length hc hc1 hκ hx0 hx ⌈4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)⌉₊
  have hP : innerLen L L₂ ρ ‖res L ρ F t v‖ =
      ⌈4 * (2 * ρ + 1 / L) * L₂ * x 0 / (1 / (4 * (2 + 2 * ρ * L) ^ 2))⌉₊ +
        ⌈4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)⌉₊ := by
    have hx00 : x 0 = ‖res L ρ F t v‖ := by simp [x, innerRun]
    rw [hx00]
    unfold innerLen
    congr 2
    field_simp; ring
  show x (innerLen L L₂ ρ ‖res L ρ F t v‖) ≤ x 0 / (11 + 10 * ρ * L)
  rw [hP]
  refine hrl.trans ?_
  have hpos : 0 < 11 + 10 * ρ * L := by positivity
  set N := ⌈4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)⌉₊ with hNdef
  set c := 1 / (4 * (2 + 2 * ρ * L) ^ 2) with hcdef
  have hN : Real.log (11 + 10 * ρ * L) ≤ c * N := by
    have h1 := Nat.le_ceil (4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L))
    have h2 : c * (4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)) =
        Real.log (11 + 10 * ρ * L) := by
      rw [hcdef]; field_simp
    calc Real.log (11 + 10 * ρ * L)
        = c * (4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)) := h2.symm
      _ ≤ c * N := mul_le_mul_of_nonneg_left h1 hc.le
  have hexp : (1 - c) ^ N ≤ 1 / (11 + 10 * ρ * L) := by
    have h1 : (1 - c) ^ N ≤ Real.exp (-c) ^ N :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-c)]) N
    rw [← Real.exp_nat_mul] at h1
    refine h1.trans ?_
    rw [one_div, ← Real.exp_log hpos, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc (1 - c) ^ N * x 0 ≤ 1 / (11 + 10 * ρ * L) * x 0 := mul_le_mul_of_nonneg_right hexp (hx0 0)
    _ = x 0 / (11 + 10 * ρ * L) := by ring

lemma rel_error {F : E → E} {J : E → E →L[ℝ] E} {L L₂ ρ : ℝ} (h : Hyp F J L L₂ ρ)
    (hL : 0 < L) (hρ : 0 ≤ ρ) (t gp v : E) (β : ℝ)
    (hv : ‖res L ρ F t v‖ ≤
      ‖res L ρ F t (t - ((2 * ρ + 1 / L) * (1 - β)) • gp)‖ / (11 + 10 * ρ * L)) :
    ‖res L ρ F t v‖ ≤ (ρ + 1 / L) / 2 * ‖F v - (1 - β) • gp‖ := by
  set γ := 2 * ρ + 1 / L with hγ
  set Λ := 2 + 2 * ρ * L with hΛ
  set v0 := t - (γ * (1 - β)) • gp with hv0
  set w := F v - (1 - β) • gp with hw
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  have hgL : 1 + γ * L = Λ := by rw [hγ, hΛ]; exact gam_L hL
  have hpos : 0 < 11 + 10 * ρ * L := by positivity
  have hid : v - v0 = res L ρ F t v - γ • w := by
    rw [hv0, hw, res, ← hγ, smul_sub, smul_smul]; abel
  have hT : ‖res L ρ F t v0‖ ≤ Λ * ‖v0 - v‖ + ‖res L ρ F t v‖ := by
    have e : res L ρ F t v0 = (v0 - v) + γ • (F v0 - F v) + res L ρ F t v := by
      rw [res, res, ← hγ, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0, ← hgL]
    have := h.lip v0 v
    nlinarith [norm_nonneg (v0 - v), norm_nonneg (F v0 - F v)]
  have hvv : ‖v0 - v‖ ≤ ‖res L ρ F t v‖ + γ * ‖w‖ := by
    rw [← neg_sub, norm_neg, hid]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have h1 : ‖res L ρ F t v‖ * (11 + 10 * ρ * L) ≤ ‖res L ρ F t v0‖ := by
    rwa [le_div_iff₀ hpos] at hv
  have e11 : 11 + 10 * ρ * L = 1 + 5 * Λ := by rw [hΛ]; ring
  rw [e11] at h1
  have h2 : 4 * Λ * ‖res L ρ F t v‖ ≤ Λ * (γ * ‖w‖) := by
    nlinarith [mul_le_mul_of_nonneg_left hvv hΛ0]
  have hΛpos : 0 < Λ := by rw [hΛ]; positivity
  have h3 : ‖res L ρ F t v‖ ≤ γ / 4 * ‖w‖ := by
    have : 4 * ‖res L ρ F t v‖ ≤ γ * ‖w‖ := by
      by_contra hneg; push Not at hneg
      nlinarith
    linarith
  have h4 : γ / 4 ≤ (ρ + 1 / L) / 2 := by
    rw [hγ]; have : 0 < 1 / L := by positivity
    linarith
  exact h3.trans (mul_le_mul_of_nonneg_right h4 (norm_nonneg _))

end OracleTemplate.CohypomonotoneAdjoint
