import LongTails.Proofs.SymmetricReverseFisherTrajectory
import LongTails.Proofs.SymmetricReverseFisherRates
open scoped RealInnerProductSpace
namespace LongTails.Proofs.SymmetricReverseFisherEscape
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherTrajectory
open LongTails.Proofs.SymmetricReverseFisherRates
open LongTails.Proofs.SymmetricReverseFisherGeometry
lemma angleRatio_initial {p : Params} (e x : Space p) (he : ‖e‖ = 1)
    (hx : ‖x‖ = 1) (hu : 0 < ⟪x, e⟫) : angleRatio e x ≤ 1 / ⟪x, e⟫ := by
  have hn := coordinate_norm e x he
  rw [hx] at hn
  have hv : ‖transverse e x‖ ≤ 1 := by nlinarith [sq_nonneg ⟪x, e⟫, norm_nonneg (transverse e x)]
  exact div_le_div_of_nonneg_right hv hu.le
lemma angleRatio_antitone {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 < η) (hη48 : η ≤ 1 / 48)
    (hu : 0 < ⟪x, e⟫) (hx : ‖x‖ = 1) :
    Antitone (fun k : ℕ => angleRatio e ((gdStep (a • e) η)^[k] x)) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [Function.iterate_succ_apply']
  have hi := inner_iterate_pos e x he ha.le hη.le hη48 hu k
  have hr := iterate_radius (a • e) x hη.le hη48 (by rw [hx]; linarith [norm_nonneg (a • e)]) k
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, he, mul_one] at hr
  have hh := angleRatio_step e _ he ha hη hη48 hi hr
  apply hh.trans
  have hm : 0 < signalStrength a := (strength_bounds ha).1
  have hq : 0 ≤ angleRatio e ((gdStep (a • e) η)^[k] x) := div_nonneg (norm_nonneg _) hi.le
  exact div_le_self hq (by nlinarith [mul_pos hη hm])
lemma angleRatio_small {p : Params} (e x : Space p) {a η : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 < η) (hη48 : η ≤ 1 / 48)
    (hu : 0 < ⟪x, e⟫) (hx : ‖x‖ = 1) {k : ℕ}
    (hk : 2 / (η * signalStrength a) * Real.log (1 / ⟪x, e⟫) ≤ k) :
    angleRatio e ((gdStep (a • e) η)^[k] x) ≤ 1 := by
  have hm := strength_bounds ha
  have hm1 : signalStrength a ≤ 1 := hm.2.trans (min_le_right _ _)
  have ht1 : η * signalStrength a ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hm1 hη.le]
  have hp := reciprocal_pow_small (mul_pos hη hm.1) ht1 hu hk
  change (1 / (1 + η * signalStrength a)) ^ k ≤ ⟪x, e⟫ at hp
  have hq := angleRatio_iterate e x he ha hη hη48 hu hx k
  have hi := angleRatio_initial e x he hx hu
  have hq0 : 0 ≤ angleRatio e x := div_nonneg (norm_nonneg _) hu.le
  have hh := mul_le_mul_of_nonneg_right hp hq0
  have hh' := mul_le_mul_of_nonneg_left hi hu.le
  have hc : ⟪x, e⟫ * (1 / ⟪x, e⟫) = 1 := by field_simp
  nlinarith
lemma inner_step_capped {p : Params} (e x : Space p) {a η q : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48)
    (hu : 0 < ⟪x, e⟫) (hr : ‖x‖ ≤ 1 + 600 * a)
    (hq : 0 ≤ q) (hqm : q ^ 2 = signalStrength a) (hangle : angleRatio e x ≤ 1) :
    min ((1 + η * signalStrength a / 2) * ⟪x, e⟫) (q / 8) ≤
      ⟪gdStep (a • e) η x, e⟫ := by
  have hv : ‖transverse e x‖ ≤ ⟪x, e⟫ := (div_le_one hu).mp hangle
  have hn := coordinate_norm e x he
  have hcone : ‖x‖ ^ 2 ≤ 2 * ⟪x, e⟫ ^ 2 := by
    nlinarith [norm_nonneg (transverse e x)]
  apply phase_two_capped (by positivity) hu.le (norm_nonneg x) hcone
    (inner_step_half e x he ha.le hη hη48 hu.le)
  intro hs
  apply inner_step_growth e x he ha.le hη hu.le hr
  nlinarith
lemma phase_two_bound {p : Params} (e x : Space p) {a η q : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 < η) (hη48 : η ≤ 1 / 48)
    (hu : 0 < ⟪x, e⟫) (hx : ‖x‖ = 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hqm : q ^ 2 = signalStrength a) {n : ℕ}
    (hn : angleRatio e ((gdStep (a • e) η)^[n] x) ≤ 1) (k : ℕ) :
    min ((1 + η * signalStrength a / 2) ^ k * (q / 8 * ⟪x, e⟫)) (q / 8) ≤
      ⟪(gdStep (a • e) η)^[n + k] x, e⟫ := by
  have hm : 0 < signalStrength a := (strength_bounds ha).1
  have hs (j : ℕ) :
      min ((1 + η * signalStrength a / 2) * ⟪(gdStep (a • e) η)^[n+j] x, e⟫) (q/8) ≤
      ⟪(gdStep (a • e) η)^[n+(j+1)] x, e⟫ := by
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    have hi := inner_iterate_pos e x he ha.le hη.le hη48 hu (n+j)
    have hr := iterate_radius (a • e) x hη.le hη48 (by rw [hx]; linarith [norm_nonneg (a • e)]) (n+j)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, he, mul_one] at hr
    have hang := (angleRatio_antitone e x he ha hη hη48 hu hx (Nat.le_add_right n j)).trans hn
    exact inner_step_capped e _ he ha hη.le hη48 hi hr hq hqm hang
  have hb := capped_growth (fun j => ⟪(gdStep (a • e) η)^[n+j] x, e⟫)
    (show 1 ≤ 1 + η * signalStrength a / 2 by nlinarith [mul_pos hη hm]) (show 0 ≤ q/8 by positivity) hs k
  have hf := iterate_inner_floor e x he ha hη.le hη48 hu hx hq hq1 hqm n
  simp only [Nat.add_zero] at hb
  exact (min_le_min_right (q/8) (mul_le_mul_of_nonneg_left hf (by positivity))).trans hb
lemma phase_two_escape {p : Params} (e x : Space p) {a η q : ℝ}
    (he : ‖e‖ = 1) (ha : 0 < a) (hη : 0 < η) (hη48 : η ≤ 1 / 48)
    (hu : 0 < ⟪x, e⟫) (hx : ‖x‖ = 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hqm : q ^ 2 = signalStrength a) {n k : ℕ}
    (hn : angleRatio e ((gdStep (a • e) η)^[n] x) ≤ 1)
    (hk : 4 / (η * signalStrength a) * Real.log (1 / ⟪x, e⟫) ≤ k) :
    q / 8 ≤ ⟪(gdStep (a • e) η)^[n + k] x, e⟫ := by
  have hm := strength_bounds ha
  have hm1 : signalStrength a ≤ 1 := hm.2.trans (min_le_right _ _)
  have hmp : 0 < signalStrength a := hm.1
  have ht : 0 < η * signalStrength a / 2 := by positivity
  have ht1 : η * signalStrength a / 2 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hm1 hη.le]
  have hk' : 2 / (η * signalStrength a / 2) * Real.log (1 / ⟪x, e⟫) ≤ k := by
    convert hk using 1
    ring
  have hg := growth_pow_large ht ht1 hu hk'
  have hb := phase_two_bound e x he ha hη hη48 hu hx hq hq1 hqm hn k
  have hmul := mul_le_mul_of_nonneg_left hg (show 0 ≤ q/8 by positivity)
  have hmin : q/8 ≤ (1 + η * signalStrength a / 2)^k * (q/8 * ⟪x,e⟫) := by nlinarith
  rwa [min_eq_right hmin] at hb
end LongTails.Proofs.SymmetricReverseFisherEscape
