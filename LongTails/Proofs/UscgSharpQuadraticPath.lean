import LongTails.Proofs.UscgSharpScalarPath
import LongTails.Proofs.UscgSharpInstances
import LongTails.Proofs.UscgSharpExcursion

namespace LongTails.Proofs.UscgSharpQuadraticPath

open scoped RealInnerProductSpace
open LongTails.Setups.UscgConstant (Space IsBallLMO dualNorm)
open UscgSharpScalar UscgSharpScalarPath UscgSharpInstances

lemma excursion {Ω : Type} {α η B L : ℝ} {k : ℕ} (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω)
    (ha : 0 < α) (ha1 : α < 1) (hB : 0 ≤ B) (hL : 0 < L) (he : 0 < η)
    (hk : 0 < k) (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo)
    (hfirst : noise (ξ 0) = -B) (hzero : ∀ t, 1 ≤ t → t ≤ k → noise (ξ t) = 0)
    (hshock : 2 * L * η * (k : ℝ) ^ 2 ≤ B * (1 - α) ^ k) :
    ∀ t ≤ k, position α η (fun x => L * x) noise lmo ξ t = η * t := by
  let x := position α η (fun x => L * x) noise lmo ξ
  let m := fun t => momentum α η (fun x => L * x) noise lmo ξ (t + 1)
  have hi := initial (α := α) (η := η) (fun x => L * x) noise lmo ξ
  have hm : m 0 = -α * B := by
    dsimp [m]
    rw [momentum_succ _ _ _ _ ha ha1, hi.1, hi.2, hfirst]
    ring
  have hh := UscgSharpExcursion.excursion (x := x) (m := m) ha ha1 hB hL he hk hi.1 hm
    (fun t ht hn => position_succ_negative _ _ _ _ ha ha1 hlmo t hn)
    (fun t ht => by
      dsimp [m, x]
      rw [momentum_succ _ _ _ _ ha ha1 (t + 1), hzero (t + 1) (by omega) (by omega)]
      ring)
    hshock
  exact fun t ht => (hh t ht).1

lemma gradient_area {Ω : Type} {α η L : ℝ} {k T : ℕ} (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (hL : 0 ≤ L) (he : 0 ≤ η) (hkT : k < T)
    (hx : ∀ t ≤ k, position α η (fun x => L * x) noise lmo ξ t = η * t) :
    L * η * (k : ℝ) ^ 2 / 2 ≤ ∑ t ∈ Finset.range T,
      dualNorm (normSeminorm ℝ (Space 1)) (gradient (lift (quadratic L))
        (trajectory α η (fun x => L * x) noise lmo ξ t).1) := by
  simp_rw [lift_gradient_eq (quadratic_derivative L), dual_axis]
  change _ ≤ ∑ t ∈ Finset.range T, |L * position α η (fun x => L * x) noise lmo ξ t|
  apply (UscgSharpExcursion.gradient_area hL he hx).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : k + 1 ≤ T))
  intro i _ _
  exact abs_nonneg _

lemma area_failure {L η ε Δ : ℝ} {k T : ℕ}
    (hL : 0 ≤ L) (he : 0 < ε) (hT : 0 < T)
    (hprogress : Δ ≤ 4 * ε * η * T)
    (hgeometry : 16 * ε ^ 2 * (T : ℝ) ^ 2 ≤ L * Δ * (k : ℝ) ^ 2) :
    2 * ε * T ≤ L * η * (k : ℝ) ^ 2 / 2 := by
  have hp : 0 < 4 * ε * (T : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hprogress (show 0 ≤ L * (k : ℝ) ^ 2 by positivity)
  have hb : (4 * ε * (T : ℝ)) * (4 * ε * T) ≤
      (4 * ε * T) * (L * η * (k : ℝ) ^ 2) := by nlinarith
  have hc := (mul_le_mul_iff_right₀ hp).mp hb
  linarith

lemma first_step_area {Ω : Type} {α η B L : ℝ} {T : ℕ} (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω)
    (ha : 0 < α) (ha1 : α < 1) (hB : 0 < B) (hL : 0 ≤ L) (he : 0 ≤ η)
    (hT : 1 < T) (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo)
    (hfirst : noise (ξ 0) = -B) :
    L * η ≤ ∑ t ∈ Finset.range T, dualNorm (normSeminorm ℝ (Space 1))
      (gradient (lift (quadratic L)) (trajectory α η (fun x => L * x) noise lmo ξ t).1) := by
  have hi := initial (α := α) (η := η) (fun x => L * x) noise lmo ξ
  have hm : momentum α η (fun x => L * x) noise lmo ξ 1 < 0 := by
    rw [show 1 = 0 + 1 by rfl, momentum_succ _ _ _ _ ha ha1, hi.1, hi.2, hfirst]
    nlinarith
  have hx := position_succ_negative (fun x => L * x) noise lmo ξ ha ha1 hlmo 0 hm
  rw [hi.1, zero_add] at hx
  simp_rw [lift_gradient_eq (quadratic_derivative L), dual_axis]
  change L * η ≤ ∑ t ∈ Finset.range T, |L * position α η (fun x => L * x) noise lmo ξ t|
  have hh := Finset.single_le_sum (fun t (_ : t ∈ Finset.range T) =>
    abs_nonneg (L * position α η (fun x => L * x) noise lmo ξ t)) (Finset.mem_range.mpr hT)
  simpa only [hx, zero_add, abs_of_nonneg (mul_nonneg hL he)] using hh

end LongTails.Proofs.UscgSharpQuadraticPath
