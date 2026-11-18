import LongTails.Proofs.KnownGapLocalizedChain
import LongTails.Proofs.KnownGapPartialOracle

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.KnownGapHardOracle

open KnownGapChainWeights KnownGapSmoothedChain KnownGapParameters KnownGapLocalizedChain
open FiniteSumNondualLowerComponents
open LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension

noncomputable def radius (p : Params) : ℝ := 4 * width p

noncomputable def thresh (p : Params) (m : ℕ) : ℝ := threshold (p.L1 / 4) (ratio p m)

section

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m) (hmM : m ≤ links p)

include hp hm hmM

noncomputable def partialReply (π : Fin m ↪ Fin p.d) (r : ℕ) :
    EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  KnownGapPartialOracle.partialField (kernel p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
    (degree p) (coefficient p m) (width p) π r

omit hm hmM in
lemma radius_pos : 0 < radius p := by
  have := width_pos p hp
  unfold radius
  positivity

omit hmM in
lemma thresh_pos : 0 < thresh p m :=
  threshold_pos (p.L1 / 4) (ratio p m) (by have := L1_pos p hp; positivity) (ratio_pos p hp m hm)

omit hmM in
lemma partialReply_prefix (π ρ : Fin m ↪ Fin p.d) (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d))
    (h : ∀ i, i.val ≤ r → π i = ρ i) :
    partialReply p hp m hm π r x = partialReply p hp m hm ρ r x :=
  KnownGapPartialOracle.partialField_prefix _ _ _ _ _ _ _ _ π ρ r x h

lemma partialReply_eq (π : Fin m ↪ Fin p.d) (r : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : ‖x‖ < radius p → ∀ i, r ≤ i → |x (π i)| ≤ thresh p m) :
    partialReply p hp m hm π r.val x = field p hp m hm hmM π x := by
  apply KnownGapPartialOracle.partialField_eq hm (kernel p hp m hm) _ _ _ _ _ _ _
    (by have := L0_pos p hp; positivity) (by have := L1_pos p hp; positivity) (ε_pos p hp)
    (ratio_pos p hp m hm) (kernel_le_threshold p hp m hm) π r x
  · exact field_exterior p hp m hm hmM π x
  · exact hx

lemma objective_nonneg (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ objective p hp m hm hmM π x :=
  objective_nonnegative p hp m hm hmM π x

lemma objective_near_gap (π : Fin m ↪ Fin p.d) (i : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : |x (π i)| ≤ thresh p m) : 3 * p.ε ≤ objective p hp m hm hmM π x := by
  have hh := smooth_gap hm (kernel p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
    (by have := L0_pos p hp; positivity) (by have := L1_pos p hp; positivity) (ε_pos p hp)
    (ratio_pos p hp m hm) (kernel_le_threshold p hp m hm) i (coordinateMap π x)
    (by exact (abs_le.mp hx).1)
  have ha := objective_above p hp m hm hmM π x
  have hε := ε_pos p hp
  change smoothObjective (kernel p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
    (coordinateMap π x) ≤ objective p hp m hm hmM π x at ha
  linarith

lemma objective_far_gap (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : radius p ≤ ‖x‖) : 3 * p.ε ≤ objective p hp m hm hmM π x := by
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
    have hG := (peak_pos m (p.L1 / 4) p.ε (ratio p m) (by have := L1_pos p hp; positivity)
      (ε_pos p hp)).le
    have hh := div_nonneg hG hB.le
    dsimp [a, coefficient]
    linarith only [hh]
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg B)
  have hlarge : p.L0 * p.R ^ 2 ≤ 6 * a * B ^ 2 := by
    dsimp [B, width] at hmul ⊢
    have hz : 0 ≤ p.L0 * p.R ^ 2 := by have := L0_pos p hp; positivity
    nlinarith only [hmul, hz]
  have habove := AdaptivePolynomialLocalization.value_above_wall (seed p hp m hm hmM π).f
    (degree p) (degree_valid p hp) a B (a * B ^ 2) (by positivity) x
  change AdaptivePolynomialLocalization.wall a B x - a * B ^ 2 ≤
    objective p hp m hm hmM π x at habove
  have heps := accuracy_le p hp
  have hε := ε_pos p hp
  linarith only [hw, hlarge, habove, heps, hε]

lemma dimension_ok :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * (radius p ^ 2 / thresh p m ^ 2) ≤ p.d :=
  dimension_sufficient p hp m hm hmM

end

end LongTails.Proofs.KnownGapHardOracle
