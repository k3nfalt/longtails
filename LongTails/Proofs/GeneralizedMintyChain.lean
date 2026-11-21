import LongTails.Proofs.MintyChainGeometry
import LongTails.Setups.GeneralizedLipschitzMinty
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators RealInnerProductSpace
open LongTails.Setups.GeneralizedLipschitzMinty

namespace LongTails.Proofs.GeneralizedMintyChain

open MintyChainGeometry

variable {d m : ℕ}

def suffix (π : Fin (2 * m + 1) ↪ Fin d) : Fin (m + 1) ↪ Fin d where
  toFun j := π ⟨m + j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val (π.injective h)
    dsimp at this
    omega

noncomputable def deficit (r B : ℝ) (π : Fin (2 * m + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d)) :=
  max 0 ((((m : ℝ) + 1) * r / 2 - ⟪target 1 (suffix π), ball B u⟫) / Real.sqrt (m + 1))

lemma suffix_norm (π : Fin (2 * m + 1) ↪ Fin d) :
    ‖target 1 (suffix π)‖ = Real.sqrt ((m : ℝ) + 1) := by
  rw [← Real.sqrt_sq (norm_nonneg _), target_norm_sq]
  simp

lemma deficit_lipschitz (r B : ℝ) (hB : 0 < B) (π : Fin (2 * m + 1) ↪ Fin d)
    (u v : EuclideanSpace ℝ (Fin d)) :
    |deficit r B π u - deficit r B π v| ≤ ‖u - v‖ := by
  let a := target 1 (suffix π)
  have h := abs_max_sub_max_le_max 0
    (((m + 1 : ℝ) * r / 2 - ⟪a, ball B u⟫) / Real.sqrt (m + 1)) 0
    (((m + 1 : ℝ) * r / 2 - ⟪a, ball B v⟫) / Real.sqrt (m + 1))
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (_ : ℝ))] at h
  apply h.trans
  rw [← sub_div, sub_sub_sub_cancel_left, ← inner_sub_right, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _), div_le_iff₀ (by positivity)]
  have hi := abs_real_inner_le_norm a (ball B v - ball B u)
  have hb := ball_lipschitz B hB v u
  rw [norm_sub_rev v u] at hb
  dsimp only [a] at hi
  rw [suffix_norm] at hi
  exact hi.trans (by rw [mul_comm ‖u - v‖]; gcongr)

lemma deficit_witness (r B : ℝ) (π : Fin (2 * m + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d))
    (h : 0 < deficit r B π u) : ∃ j, ball B u (π j) ≤ r / 2 := by
  by_contra! hn
  have hall (j : Fin (m + 1)) : r / 2 ≤ ball B u (suffix π j) :=
    (hn ⟨m + j.val, by omega⟩).le
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hall j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  unfold deficit at h
  rw [target, inner_lift] at h
  simp only [one_mul] at h
  push_cast at hs
  have hd : ((m : ℝ) + 1) * r / 2 - ∑ j, ball B u (suffix π j) ≤ 0 := by linarith
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hd (Real.sqrt_nonneg _))] at h
  exact h.false

lemma deficit_large (r B : ℝ) (π : Fin (2 * m + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d))
    (hsmall : ∀ j : Fin (2 * m + 1), m ≤ j.val → |ball B u (π j)| ≤ r / 4) :
    r * Real.sqrt ((m : ℝ) + 1) / 4 ≤ deficit r B π u := by
  apply le_trans _ (le_max_right _ _)
  rw [le_div_iff₀ (by positivity), target, inner_lift]
  simp only [one_mul]
  have hall (j : Fin (m + 1)) : ball B u (suffix π j) ≤ r / 4 :=
    (le_abs_self _).trans (hsmall ⟨m + j.val, by omega⟩ (by dsimp; omega))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hall j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  push_cast at hs
  nlinarith [congrArg (fun t : ℝ => r * t) (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m + 1))]

noncomputable def exponent (r B M L1 : ℝ) (π : Fin (2 * m + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) :=
  min (Real.log M) (L1 / 2 * deficit r B π u)

noncomputable def amplified (κ r B M L1 : ℝ) (π : Fin (2 * m + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) :=
  Real.exp (exponent r B M L1 π u) • field κ r B π u

lemma exp_sub_le (s t : ℝ) : Real.exp t - Real.exp s ≤ (t - s) * Real.exp t := by
  have hi := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (s - t)) (Real.exp_pos t).le
  rw [← Real.exp_add, sub_add_cancel] at hi
  linarith

lemma amplified_regular {κ r B M L0 L1 : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hB : 0 < B)
    (h0 : 12 * κ ≤ L0) (h1 : 0 ≤ L1) (hM : 1 ≤ M) (hscale : M ≤ 2 ∨ 48 ≤ L1 * r)
    (π : Fin (2 * m + 1) ↪ Fin d) (hrad : 4 * ((2 * m : ℕ) + 1 : ℝ) * r ^ 2 ≤ B ^ 2) :
    LongTails.Setups.MirrorGeneralizedSmooth.SegmentSmooth (amplified κ r B M L1 π) L0 L1 := by
  let a := exponent r B M L1 π
  let H := field κ r B π
  let F := amplified κ r B M L1 π
  have hn (u) : ‖F u‖ = Real.exp (a u) * ‖H u‖ := by
    simp [F, amplified, a, H, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have ha (u v) : |a u - a v| ≤ L1 / 2 * ‖u - v‖ := by
    have h := abs_min_sub_min_le_max (Real.log M) (L1 / 2 * deficit r B π u)
      (Real.log M) (L1 / 2 * deficit r B π v)
    simp only [sub_self, abs_zero, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ L1 / 2)] at h
    apply h.trans (max_le (by positivity) _)
    exact mul_le_mul_of_nonneg_left (deficit_lipschitz r B hB π u v) (by positivity)
  have hcoef (u) : Real.exp (a u) * (6 * κ) ≤ L0 + L1 / 2 * ‖F u‖ := by
    have hsmall (h : Real.exp (a u) ≤ 2) : Real.exp (a u) * (6 * κ) ≤ L0 + L1 / 2 * ‖F u‖ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h) hκ.le, mul_nonneg h1 (norm_nonneg (F u))]
    by_cases hh : Real.exp (a u) ≤ 2
    · exact hsmall hh
    have hcap : Real.exp (a u) ≤ M := (Real.exp_le_exp.mpr (min_le_left _ _)).trans_eq
      (Real.exp_log (by linarith))
    have hs := hscale.resolve_left (by linarith)
    have hd : 0 < deficit r B π u := by
      by_contra! hd
      have hx : a u ≤ 0 := (min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hd)
      exact hh ((Real.exp_le_one_iff.mpr hx).trans (by norm_num))
    have hl := field_lower κ r B hκ hr hB π hrad u (deficit_witness _ _ _ _ hd)
    have hnorm : κ * r / 4 ≤ ‖H u‖ := by
      apply le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
      change _ ≤ ‖field κ r B π u‖ ^ 2
      nlinarith [sq_nonneg (κ * r)]
    have hb : 6 * κ ≤ L1 / 2 * ‖H u‖ := by
      nlinarith [mul_nonneg h1 (sub_nonneg.mpr hnorm), mul_nonneg hκ.le (sub_nonneg.mpr hs)]
    rw [hn]
    nlinarith [mul_nonneg (Real.exp_pos (a u)).le (sub_nonneg.mpr hb)]
  have hpair (x y : _) (ho : a y ≤ a x) {V : ℝ} (hx : ‖F x‖ ≤ V) (hy : ‖F y‖ ≤ V) :
      ‖F x - F y‖ ≤ (L0 + L1 * V) * ‖x - y‖ := by
    have hid : F x - F y = Real.exp (a y) • (H x - H y) +
        (Real.exp (a x) - Real.exp (a y)) • H x := by
      change Real.exp (a x) • H x - Real.exp (a y) • H y = _
      module
    rw [hid]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr ho))]
    have hΔ := ha x y
    rw [abs_of_nonneg (sub_nonneg.mpr ho)] at hΔ
    have he := (exp_sub_le (a y) (a x)).trans (mul_le_mul_of_nonneg_right hΔ (Real.exp_pos _).le)
    have hc := (hcoef y).trans (add_le_add_right (mul_le_mul_of_nonneg_left hy (by positivity)) _)
    have hh := field_lipschitz κ r B hκ.le hr hB π x y
    change ‖H x - H y‖ ≤ _ at hh
    rw [hn] at hx
    nlinarith [mul_nonneg (Real.exp_pos (a y)).le (sub_nonneg.mpr hh),
      mul_nonneg (norm_nonneg (x - y)) (sub_nonneg.mpr hc),
      mul_nonneg (norm_nonneg (H x)) (sub_nonneg.mpr he),
      mul_nonneg (mul_nonneg h1 (norm_nonneg (x - y))) (sub_nonneg.mpr hx)]
  intro x y V hV
  have hx : ‖F x‖ ≤ V := by simpa using hV 0 ⟨le_rfl, zero_le_one⟩
  have hy : ‖F y‖ ≤ V := by simpa using hV 1 ⟨zero_le_one, le_rfl⟩
  rcases le_total (a y) (a x) with h | h
  · exact hpair x y h hx hy
  · simpa only [norm_sub_rev (F y) (F x), norm_sub_rev y x] using hpair y x h hy hx

end LongTails.Proofs.GeneralizedMintyChain
