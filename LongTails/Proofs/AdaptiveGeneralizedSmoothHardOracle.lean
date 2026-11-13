import LongTails.Proofs.AdaptiveGeneralizedSmoothLocalizedChain
import LongTails.Proofs.AdaptiveGeneralizedSmoothPartialOracle
import LongTails.Proofs.AdaptiveTransientParameters

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.AdaptiveGeneralizedSmoothHardOracle

open GeneralizedSmoothHardChain GeneralizedSmoothHardChainRadius GeneralizedSmoothSmoothedChain
open AdaptiveGeneralizedSmoothLocalizedChain FiniteSumNondualLowerComponents

open AdaptiveTransientParameters

noncomputable def radius (p : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params) (_m : ℕ) : ℝ :=
  4 * width p

noncomputable def threshold (p : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params) (m : ℕ) : ℝ :=
  1 / (4 * p.L1 * Real.sqrt m)

noncomputable def bump (p : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.spec.valid p) (m : ℕ) (hm : 0 < m) :=
  kernel hm (p.L1 / 4) p.R (by have := hp.2.1; positivity) hp.2.2.1

noncomputable def partialReply (p : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.spec.valid p) (m : ℕ) (hm : 0 < m)
    (π : Fin m ↪ Fin p.d) (r : ℕ) : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  AdaptiveGeneralizedSmoothPartialOracle.partialField (bump p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε
    (degree p) (coefficient p m) (width p) π r

variable (p : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.spec.valid p) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1)

include hp in
lemma radius_pos : 0 < radius p m := by
  have := width_pos p hp
  unfold radius
  positivity

include hp hm in
lemma threshold_pos : 0 < threshold p m := by
  have := hp.2.1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold threshold
  positivity

lemma threshold_scaled : threshold p m = 1 / (16 * (p.L1 / 4) * Real.sqrt m) := by
  unfold threshold
  ring

lemma bump_local : (bump p hp m hm).rOut ≤ 1 / (16 * (p.L1 / 4) * Real.sqrt m) :=
  kernel_local_radius hm (p.L1 / 4) p.R (by have := hp.2.1; positivity)

lemma partialReply_prefix (π ρ : Fin m ↪ Fin p.d) (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d))
    (h : ∀ i, i.val ≤ r → π i = ρ i) : partialReply p hp m hm π r x = partialReply p hp m hm ρ r x :=
  AdaptiveGeneralizedSmoothPartialOracle.partialField_prefix _ _ _ _ _ _ _ π ρ r x h

lemma partialReply_eq (π : Fin m ↪ Fin p.d) (r : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : ‖x‖ < radius p m → ∀ i, r ≤ i → |x (π i)| ≤ threshold p m) :
    partialReply p hp m hm π r.val x = AdaptiveGeneralizedSmoothLocalizedChain.field p hp m hm hmB π x := by
  apply AdaptiveGeneralizedSmoothPartialOracle.partialField_eq hm (bump p hp m hm) _ _ _ _ _ _
    (by have := hp.1; positivity) (by have := hp.2.1; positivity) hp.2.2.2.1
    (bump_local p hp m hm) π r x
  · exact AdaptiveGeneralizedSmoothLocalizedChain.field_exterior p hp m hm hmB π x
  · rw [threshold_scaled p m] at hx
    exact hx

lemma objective_nonnegative (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ AdaptiveGeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x :=
  AdaptiveGeneralizedSmoothLocalizedChain.objective_nonnegative p hp m hm hmB π x

lemma objective_near_gap (π : Fin m ↪ Fin p.d) (i : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : |x (π i)| ≤ threshold p m) :
    3 * p.ε ≤ AdaptiveGeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x := by
  have hh := smooth_gap hm (bump p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε
    (by have := hp.1; positivity) (by have := hp.2.1; positivity) hp.2.2.2.1
    (bump_local p hp m hm) i (coordinateMap π x)
    (by rw [threshold_scaled p m] at hx; exact (abs_le.mp hx).1)
  have ha := AdaptiveGeneralizedSmoothLocalizedChain.objective_above p hp m hm hmB π x
  have hε := hp.2.2.2.1
  change smoothObjective (bump p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (coordinateMap π x) ≤
    AdaptiveGeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x at ha
  linarith

lemma objective_far_gap (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : radius p m ≤ ‖x‖) :
    3 * p.ε ≤ AdaptiveGeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x := by
  let a := coefficient p m
  let B := width p
  have ha : 0 < a := coefficient_pos p hp m
  have hB : 0 < B := width_pos p hp
  have hnorm : (4 * B) ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (show 0 ≤ 4 * B by positivity) hx 2
  have hw : 6 * a * B ^ 2 ≤ AdaptivePolynomialLocalization.wall a B x - a * B ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ a / 2 by positivity)
    have hz : 0 ≤ a * B ^ 2 := by positivity
    unfold AdaptivePolynomialLocalization.wall
    nlinarith only [hh, hz]
  have hc : p.L0 / 1000 ≤ a := by
    have hG := (peak_pos m (p.L1 / 4) p.ε (by have := hp.2.1; positivity) hp.2.2.2.1).le
    have hh := div_nonneg hG hB.le
    dsimp [a, coefficient]
    linarith only [hh]
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg B)
  have hlarge : p.L0 * p.R ^ 2 ≤ 6 * a * B ^ 2 := by
    dsimp [B, width] at hmul ⊢
    have hz : 0 ≤ p.L0 * p.R ^ 2 := by have := hp.1; positivity
    nlinarith only [hmul, hz]
  have habove := AdaptivePolynomialLocalization.value_above_wall (seed p hp m hm hmB π).f
    (degree p) (degree_valid p hp) a B (a * B ^ 2) (by positivity) x
  change AdaptivePolynomialLocalization.wall a B x - a * B ^ 2 ≤
    AdaptiveGeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x at habove
  have heps := hp.2.2.2.2.2.2.1
  have hε := hp.2.2.2.1
  linarith only [hw, hlarge, habove, heps, hε]

include hp hm hmB in
lemma dimension_sufficient :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * (radius p m ^ 2 / threshold p m ^ 2) ≤ p.d := by
  have hq := hp.2.2.2.2.1
  have hmq : (m : ℝ) ≤ p.L1 * p.R :=
    (show (m : ℝ) ≤ ((⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1 : ℕ) : ℝ) by
      exact_mod_cast hmB).trans (GeneralizedSmoothTransientParameters.links_le_q _ hq)
  have hratio : radius p m ^ 2 / threshold p m ^ 2 =
      4398046511104 * (p.L1 * p.R) ^ 2 * (m : ℝ) := by
    have hr : radius p m = 524288 * p.R := by unfold radius width; ring
    rw [hr]
    exact hiding_ratio m hm p.L1 p.R hp.2.1
  rw [hratio]
  exact (hiding_dimension m (p.L1 * p.R) (by linarith) hmq).trans
    ((Nat.le_ceil _).trans (Nat.cast_le.mpr hp.2.2.2.2.2.2.2))

end LongTails.Proofs.AdaptiveGeneralizedSmoothHardOracle
