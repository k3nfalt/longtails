import LongTails.Proofs.QuarticAccelerationTrace
import LongTails.Proofs.QuarticAccelerationCount

namespace LongTails.Proofs.QuarticAccelerationWeights

open LongTails.Algorithms.CompositeCubicAcceleration hiding advance damping
open LongTails.Algorithms.QuarticAcceleration
open LongTails.Proofs.QuarticAccelerationEnergy LongTails.Proofs.QuarticAccelerationTrace
open LongTails.Proofs.CompositeCubicAcceleration hiding advance_certificate
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma first_weight {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hN : 0 < N) : (t.state 1).weight = (t.guess 0)⁻¹ := by
  have hloc : location t 0 = x0 := by
    unfold location
    rw [hv.initial]
    exact initial_center (hv.guess_pos 0 (Nat.zero_le _)) x0
  have hlam : parameter E γ x0 (t.point 0) = t.guess 0 := by
    rw [hv.first_guess hN]
    simp only [lam, hloc]
  rw [hv.advance_eq 0 hN, hv.initial,
    initial_advance (hv.guess_pos 0 (Nat.zero_le _)) x0 (t.point 0) (t.gradient 0) hlam]

lemma inverse_root_step {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) {k : ℕ} (hk : k < N) :
    1 / Real.sqrt (t.guess (k + 1)) =
      if t.guess k < lam t γ k then (1 / Real.sqrt (t.guess k)) / 2 else 2 * (1 / Real.sqrt (t.guess k)) := by
  have hp := hv.guess_pos k hk.le
  rw [hv.guess_eq k hk]
  unfold nextGuess
  by_cases hu : t.guess k < lam t γ k
  · rw [ite_eq_right (not_le.mpr hu), ite_eq_left hu, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  · rw [ite_eq_left (le_of_not_gt hu), ite_eq_right hu, Real.sqrt_div hp.le]
    norm_num
    ring

lemma weight_sum {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hN : 0 < N) :
    (∑ k ∈ Finset.range N, 1 / Real.sqrt (t.guess k)) ≤ 8 * Real.sqrt (t.state N).weight := by
  classical
  refine QuarticAccelerationCount.step_weight_sum
    (fun k => 1 / Real.sqrt (t.guess k)) (fun k => Real.sqrt (t.state k).weight)
    (fun k => t.guess k < lam t γ k) N
    (fun k hk => inverse_root_step hv hk) (Real.sqrt_nonneg _) ?_ ?_ (by positivity) ?_
  · intro k hk
    exact Real.sqrt_le_sqrt (weight_strict hv hk).le
  · intro k hk hdown
    have hh := (LongTails.Proofs.QuarticAcceleration.advance_down_weight (t.state k)
      (g := t.gradient k) (hv.guess_pos k hk.le) (weight_nonneg hv k hk.le)
      (hv.lam_pos k hk) (le_of_not_gt hdown)).2
    rw [← hv.advance_eq k hk] at hh
    have he : 1 / (2 * Real.sqrt (t.guess k)) = (1 / Real.sqrt (t.guess k)) / 2 := by ring
    rw [he] at hh
    nlinarith only [hh]
  · rw [show 1 / Real.sqrt (t.guess 0) = Real.sqrt (t.state 1).weight by
      rw [first_weight hv hN, Real.sqrt_inv, one_div]]
    exact Real.sqrt_le_sqrt (weight_mono hv hN (le_refl N))

lemma up_energy_point {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hγ : 0 < γ) {k : ℕ} (hk : k < N)
    (hup : t.guess k < lam t γ k) :
    (t.state (k + 1)).weight * t.guess k ^ 2 ≤ 4 * γ * dissipation t γ k := by
  have hA := weight_nonneg hv k hk.le
  have hμ := hv.guess_pos k hk.le
  have hh := up_energy hμ hA hup
  have hcoef : 0 ≤ ((t.state k).weight + trialWeight (t.guess k) (t.state k).weight) *
      min (t.guess k) (lam t γ k) * ‖t.point k - location t k‖ ^ 2 := by
    have ha := trialWeight_pos hμ hA
    have hl := hv.lam_pos k hk
    positivity
  have hn := mul_nonneg hγ.le hcoef
  rw [hv.advance_eq k hk]
  dsimp only [advance, damping, parameter, dissipation, lam, location] at hh hn ⊢
  nlinarith only [hh, hn]

lemma up_energy_sum {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) :
    (∑ k ∈ Finset.range N, if t.guess k < lam t γ k then (t.state (k + 1)).weight * t.guess k ^ 2 else 0) ≤
      2 * γ * R ^ 2 := by
  have hh : (∑ k ∈ Finset.range N, if t.guess k < lam t γ k then (t.state (k + 1)).weight * t.guess k ^ 2 else 0) ≤
      ∑ k ∈ Finset.range N, 4 * γ * dissipation t γ k := by
    apply Finset.sum_le_sum
    intro k hk
    have hlt := Finset.mem_range.mp hk
    split_ifs with hu
    · exact up_energy_point hv hγ hlt hu
    · exact mul_nonneg (by positivity) (dissipation_nonneg hv hlt)
  rw [← Finset.mul_sum] at hh
  have hsum := (energy_bounds hv hc hγ hx0 hmin (le_refl N)).2
  have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * γ by positivity)
  nlinarith only [hh, hm]

end LongTails.Proofs.QuarticAccelerationWeights
