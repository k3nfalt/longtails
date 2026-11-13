import LongTails.Proofs.GeneralizedSmoothLocalizedChain
import LongTails.Proofs.GeneralizedSmoothPartialOracle
import LongTails.Proofs.GeneralizedSmoothTransientDimension

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GeneralizedSmoothHardOracle

open GeneralizedSmoothHardChain GeneralizedSmoothHardChainRadius GeneralizedSmoothSmoothedChain
open GeneralizedSmoothLocalizedChain FiniteSumNondualLowerComponents

noncomputable def scale (p : LongTails.Setups.GeneralizedSmoothConvexTransient.Params) (m : ℕ) : ℝ :=
  peak m (p.L1 / 4) p.ε + (p.L0 / 32) * (p.R / 2)

noncomputable def radius (p : LongTails.Setups.GeneralizedSmoothConvexTransient.Params) (m : ℕ) : ℝ :=
  24 * scale p m / (p.L0 / 32)

noncomputable def threshold (p : LongTails.Setups.GeneralizedSmoothConvexTransient.Params) (m : ℕ) : ℝ :=
  1 / (4 * p.L1 * Real.sqrt m)

noncomputable def bump (p : LongTails.Setups.GeneralizedSmoothConvexTransient.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexTransient.spec.valid p) (m : ℕ) (hm : 0 < m) :=
  kernel hm (p.L1 / 4) p.R (by have := hp.2.1; positivity) hp.2.2.1

noncomputable def partialReply (p : LongTails.Setups.GeneralizedSmoothConvexTransient.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexTransient.spec.valid p) (m : ℕ) (hm : 0 < m)
    (π : Fin m ↪ Fin p.d) (r : ℕ) : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  GeneralizedSmoothPartialOracle.partialField (bump p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε
    (p.L0 / 32) (scale p m) π r

variable (p : LongTails.Setups.GeneralizedSmoothConvexTransient.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexTransient.spec.valid p) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1)

include hp in
lemma scale_pos : 0 < scale p m := by
  have hG := peak_pos m (p.L1 / 4) p.ε (by have := hp.2.1; positivity) hp.2.2.2.1
  have h0 := hp.1
  have hR := hp.2.2.1
  unfold scale
  positivity

include hp in
lemma radius_pos : 0 < radius p m := by
  have := scale_pos p hp m
  have := hp.1
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
  GeneralizedSmoothPartialOracle.partialField_prefix _ _ _ _ _ _ π ρ r x h

lemma partialReply_eq (π : Fin m ↪ Fin p.d) (r : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : ‖x‖ < radius p m → ∀ i, r ≤ i → |x (π i)| ≤ threshold p m) :
    partialReply p hp m hm π r.val x = GeneralizedSmoothLocalizedChain.field p hp m hm hmB π x := by
  have ha : 0 < p.L0 / 32 := by have := hp.1; positivity
  have hu := GeneralizedSmoothLocalization.seed_upper (seed p hp m hm hmB π) _ ha x
  change smoothObjective (bump p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (coordinateMap π x) ≤
    scale p m * ‖x‖ + scale p m ^ 2 / (p.L0 / 32) at hu
  exact GeneralizedSmoothPartialOracle.partialField_eq hm (bump p hp m hm) _ _ _ _ _
    (by have := hp.1; positivity) (by have := hp.2.1; positivity) hp.2.2.2.1 ha
    (scale_pos p hp m) (bump_local p hp m hm) π r x hu
    (by rw [threshold_scaled p m] at hx; exact hx)

lemma objective_nonnegative (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ GeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x :=
  GeneralizedSmoothLocalization.objective_nonnegative (seed p hp m hm hmB π) _
    (by have := hp.1; positivity) x

lemma objective_near_gap (π : Fin m ↪ Fin p.d) (i : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : |x (π i)| ≤ threshold p m) :
    3 * p.ε ≤ GeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x := by
  have hh := smooth_gap hm (bump p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε
    (by have := hp.1; positivity) (by have := hp.2.1; positivity) hp.2.2.2.1
    (bump_local p hp m hm) i (coordinateMap π x)
    (by rw [threshold_scaled p m] at hx; exact (abs_le.mp hx).1)
  have ha := GeneralizedSmoothLocalization.objective_above (seed p hp m hm hmB π) (p.L0 / 32)
    (by have := hp.1; positivity) x
  have hε := hp.2.2.2.1
  change smoothObjective (bump p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (coordinateMap π x) ≤
    GeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x at ha
  linarith

lemma objective_far_gap (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : radius p m ≤ ‖x‖) :
    3 * p.ε ≤ GeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x := by
  let a := p.L0 / 32
  let S := scale p m
  have ha : 0 < a := by have := hp.1; dsimp [a]; positivity
  have hS : 0 < S := scale_pos p hp m
  have hnorm : (24 * S / a) ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (show 0 ≤ 24 * S / a by positivity) hx 2
  have hw : 160 * S ^ 2 / a ≤ GeneralizedSmoothShieldCalculus.wall a (16 * S / a) x := by
    have he : a / 2 * ((24 * S / a) ^ 2 - (16 * S / a) ^ 2) = 160 * S ^ 2 / a := by
      field_simp
      ring
    rw [← he]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hnorm _) (by positivity)
  have hSr : a * (p.R / 2) ≤ S := GeneralizedSmoothLocalization.strength_radius (seed p hp m hm hmB π) a
  have hs := pow_le_pow_left₀ (show 0 ≤ a * (p.R / 2) by have := hp.2.2.1; positivity) hSr 2
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ 160 / a by positivity)
  have he : 160 / a * (a * (p.R / 2)) ^ 2 = 40 * a * p.R ^ 2 := by field_simp; ring
  rw [he] at hb
  have habove := (GeneralizedSmoothShieldCalculus.value_above (seed p hp m hm hmB π).f a
    (16 * S / a) (64 * S ^ 2 / a) (by positivity) x).2
  change GeneralizedSmoothShieldCalculus.wall a (16 * S / a) x ≤
    GeneralizedSmoothLocalizedChain.objective p hp m hm hmB π x at habove
  have heps := hp.2.2.2.2.2.2.1
  have hε := hp.2.2.2.1
  have heq : 160 / a * S ^ 2 = 160 * S ^ 2 / a := by ring
  rw [heq] at hb
  dsimp only [a] at hb hw habove
  nlinarith only [hb, hw, habove, heps, hε]

include hp hm hmB in
lemma dimension_sufficient :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * (radius p m ^ 2 / threshold p m ^ 2) ≤ p.d := by
  have hq := hp.2.2.2.2.1
  have hmq : (m : ℝ) ≤ p.L1 * p.R :=
    (show (m : ℝ) ≤ ((⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1 : ℕ) : ℝ) by
      exact_mod_cast hmB).trans (GeneralizedSmoothTransientParameters.links_le_q _ hq)
  have hq1 : 1 ≤ p.L1 * p.R := by linarith
  have hU := GeneralizedSmoothTransientDimension.exterior_radius_bound m hm p.L0 p.L1 p.R p.ε
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2.2.1 hmq hq1
  change radius p m ≤ 36 * p.R * (p.L1 * p.R) * Real.exp (Real.sqrt (p.L1 * p.R)) at hU
  have hθ : threshold p m = p.R / (4 * (p.L1 * p.R) * Real.sqrt m) := by
    unfold threshold
    have hR := hp.2.2.1.ne'
    field_simp
  have hratio := GeneralizedSmoothTransientDimension.ratio_bound m hm (p.L1 * p.R) p.R (radius p m)
    (by linarith) hp.2.2.1 (radius_pos p hp m).le hU
  rw [← hθ] at hratio
  have hdim := GeneralizedSmoothTransientDimension.dimension_scalar m (p.L1 * p.R)
    (radius p m ^ 2 / threshold p m ^ 2) hq1 hmq hratio
  exact hdim.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr hp.2.2.2.2.2.2.2))

end LongTails.Proofs.GeneralizedSmoothHardOracle
