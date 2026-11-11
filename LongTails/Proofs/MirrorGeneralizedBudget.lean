import LongTails.Proofs.MirrorGeneralizedGrowth

namespace LongTails.Proofs.MirrorGeneralizedBudget

open LongTails.Setups.MirrorGeneralizedSmooth
open LongTails.Algorithms.MirrorGeneralizedAcceleration
open MirrorGeneralizedStep MirrorGeneralizedRun MirrorGeneralizedGrowth

lemma potential_difference {L Q A B : ℝ} (hL : 0 < L) (hA : 0 < A) (hB : 0 < B) :
    potential L Q B - potential L Q A =
      Real.sqrt (L * B) - Real.sqrt (L * A) + Q * Real.log (B / A) := by
  unfold potential
  rw [Real.log_sqrt (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul hL.ne' hB.ne', Real.log_mul hL.ne' hA.ne', Real.log_div hB.ne' hA.ne']
  ring

lemma potential_below_target {L Q D Δ ε B : ℝ} (hL : 0 < L) (hQ : 0 ≤ Q)
    (hD : 0 < D) (hΔ : 0 < Δ) (hε : 0 < ε) (hB : 0 < B) (hBt : B < 2 * D / ε) :
    potential L Q B - potential L Q (D / Δ) ≤
      Real.sqrt (2 * L * D / ε) + Q * Real.log (2 + 2 * Δ / ε) := by
  rw [potential_difference hL (div_pos hD hΔ) hB]
  have hs : Real.sqrt (L * B) ≤ Real.sqrt (2 * L * D / ε) := by
    apply Real.sqrt_le_sqrt
    have hh := mul_le_mul_of_nonneg_left hBt.le hL.le
    convert hh using 1
    ring
  have hr : B / (D / Δ) ≤ 2 + 2 * Δ / ε := by
    apply (div_le_iff₀ (div_pos hD hΔ)).mpr
    have hh : 2 * D / ε ≤ (2 + 2 * Δ / ε) * (D / Δ) := by
      field_simp
      nlinarith
    exact hBt.le.trans hh
  have hl := Real.log_le_log (div_pos hB (div_pos hD hΔ)) hr
  have hq := mul_le_mul_of_nonneg_left hl hQ
  nlinarith [Real.sqrt_nonneg (L * (D / Δ))]

lemma run_accuracy {p : Public} {I : Instance p} (h : Hyp I)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hD : 0 < p.D) (hΔ : 0 < p.Δ)
    {xs : p.E} (hmin : ∀ u, I.f xs ≤ I.f u)
    (hb : bregman I xs p.x0 ≤ p.D) (hgap : I.f p.x0 - I.f xs ≤ p.Δ)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hN : 24576 * (1 + Real.sqrt (2 * p.L0 * p.D / ε) +
      (1 + p.L1 * radius p) * Real.log (2 + 2 * p.Δ / ε)) ≤ (N : ℝ)) :
    I.f (run p I.grad I.prox N).x - I.f xs ≤ ε := by
  have hi := inv_run h hL0 hL1 hD hΔ hmin hb hgap N
  have hr : 0 ≤ radius p := by unfold radius; positivity
  have hQ : 0 ≤ 1 + p.L1 * radius p := by positivity
  have hAt : 2 * p.D / ε ≤ (run p I.grad I.prox N).A := by
    by_contra hn
    push Not at hn
    have hp := potential_run h hL0 hL1 hD hΔ hmin hb hgap N
    have hu := potential_below_target hL0 hQ hD hΔ hε hi.positive hn
    have hl : 0 ≤ Real.log (2 + 2 * p.Δ / ε) := Real.log_nonneg (by
      have hh : 0 ≤ 2 * p.Δ / ε := by positivity
      linarith)
    have hterm := mul_nonneg hQ hl
    nlinarith [Real.sqrt_nonneg (2 * p.L0 * p.D / ε)]
  have hg := objective_bound h hi
  have hdiv : 2 * p.D / (run p I.grad I.prox N).A ≤ ε := by
    apply (div_le_iff₀ hi.positive).mpr
    have hh := (div_le_iff₀ hε).mp hAt
    nlinarith
  exact hg.trans hdiv

end LongTails.Proofs.MirrorGeneralizedBudget
