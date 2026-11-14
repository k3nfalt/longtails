import LongTails.Proofs.CompositeAdaptiveRun

open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeAdaptive

open LongTails.Setups.RadiusCompositeGeneralizedSmooth
open LongTails.Algorithms.RadiusCompositeAccelerated

variable {q : Params} {I : Instance q.toPublic} {xs : q.E} {r0 : ReadyState q I xs}

lemma trajectory_weight_step (T : Trajectory q I xs r0) (n : ℕ) :
    (T.ready (n + 1)).iterate.weight = (T.ready n).iterate.weight + (T.steps n).trial.weight := by
  rw [T.next, (T.steps n).next_iterate]
  rfl

lemma trajectory_start_step (T : Trajectory q I xs r0) (n : ℕ) :
    (T.ready (n + 1)).start = (T.steps n).trial.weight / restartFactor q.toPublic := by
  rw [T.next, (T.steps n).next_start]

lemma trajectory_weight_mono (T : Trajectory q I xs r0) :
    Monotone (fun n => (T.ready n).iterate.weight) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [trajectory_weight_step]
  have hp := (T.steps n).resolved.2.2.1
  linarith

def trajectoryCalls (T : Trajectory q I xs r0) (n : ℕ) : ℕ :=
  2 * ∑ k ∈ Finset.range n, (T.steps k).pairs

lemma trajectory_calls_succ (T : Trajectory q I xs r0) (n : ℕ) :
    trajectoryCalls T (n + 1) = 2 * (T.steps n).pairs + trajectoryCalls T n := by
  simp only [trajectoryCalls, Finset.sum_range_succ]
  omega

lemma trajectory_execution (T : Trajectory q I xs r0) (N : ℕ)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    (transition q.toPublic I)^[trajectoryCalls T N]
      (if targetWeight q.toPublic ≤ r0.iterate.weight then .finished r0.iterate.point
        else beginSearch r0.iterate r0.start) =
      if targetWeight q.toPublic ≤ (T.ready N).iterate.weight then .finished (T.ready N).iterate.point
        else beginSearch (T.ready N).iterate (T.ready N).start := by
  induction N with
  | zero => simp only [trajectoryCalls, Finset.range_zero, Finset.sum_empty, Nat.mul_zero,
      Function.iterate_zero, id_eq, T.initial]
  | succ n ih =>
      have hprefix : ∀ k < n, (T.ready k).iterate.weight < targetWeight q.toPublic := by
        intro k hk
        exact hactive k (by omega)
      rw [trajectory_calls_succ, Function.iterate_add_apply, ih hprefix,
        ite_eq_right (not_le.mpr (hactive n (by omega))), (T.steps n).execution, T.next]
      simp only [commit, (T.steps n).next_iterate, (T.steps n).next_start]

noncomputable def trajectorySurplus (T : Trajectory q I xs r0) (n : ℕ) : ℝ :=
  I.f xs - I.f (mix (T.ready n).iterate.weight (T.steps n).trial.weight
    (T.ready n).iterate.point (T.ready n).iterate.momentum) -
    ⟪(T.steps n).trial.gradient, xs - mix (T.ready n).iterate.weight (T.steps n).trial.weight
      (T.ready n).iterate.point (T.ready n).iterate.momentum⟫

noncomputable def trajectoryDisplacement (T : Trajectory q I xs r0) (n : ℕ) : ℝ :=
  ‖(T.steps n).trial.proximalPoint - (T.ready n).iterate.momentum‖

lemma trajectory_surplus_nonneg (h : Conditions q I xs) (T : Trajectory q I xs r0) (n : ℕ) :
    0 ≤ trajectorySurplus T n := by
  have hc := congrArg Trial.gradient (T.steps n).resolved.1
  dsimp only [evaluatedTrial] at hc
  unfold trajectorySurplus
  rw [hc]
  linarith [OracleTemplate.Gradient.convex_support h.convex h.grad
    (mix (T.ready n).iterate.weight (T.steps n).trial.weight
      (T.ready n).iterate.point (T.ready n).iterate.momentum) xs]

lemma trajectory_energy_step (h : Conditions q I xs) (T : Trajectory q I xs r0) (n : ℕ) :
    energy I xs (T.ready (n + 1)).iterate + trajectoryDisplacement T n ^ 2 / 4 +
      (T.steps n).trial.weight * trajectorySurplus T n ≤ energy I xs (T.ready n).iterate := by
  have hc := (T.steps n).resolved.1
  have ht := (T.steps n).resolved.2.2.1
  have hs : accepts q.toPublic (T.ready n).iterate
      (evaluatedTrial q.toPublic I (T.ready n).iterate (T.steps n).trial.weight) := by
    rw [← hc]
    exact (T.steps n).resolved.2.1
  have he := (accepted_valid h (T.ready n).valid ht hs).2
  rw [← hc] at he
  rw [T.next, (T.steps n).next_iterate]
  exact he

lemma trajectory_energy_nonneg (h : Conditions q I xs) (T : Trajectory q I xs r0) (n : ℕ) :
    0 ≤ energy I xs (T.ready n).iterate := by
  unfold energy
  exact add_nonneg (mul_nonneg (T.ready n).valid.weightPositive.le
    (objective_gap_nonneg h (T.ready n).valid.point_mem)) (by positivity)

lemma trajectory_payments (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ) :
    (∑ k ∈ Finset.range N, trajectoryDisplacement T k ^ 2) ≤ 12 * q.R ^ 2 ∧
      (∑ k ∈ Finset.range N, (T.steps k).trial.weight * trajectorySurplus T k) ≤ 3 * q.R ^ 2 := by
  have hstep : ∀ k ∈ Finset.range N,
      trajectoryDisplacement T k ^ 2 / 4 + (T.steps k).trial.weight * trajectorySurplus T k ≤
        energy I xs (T.ready k).iterate - energy I xs (T.ready (k + 1)).iterate := by
    intro k _
    linarith [trajectory_energy_step h T k]
  have hs := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, ← Finset.sum_div,
    show (∑ k ∈ Finset.range N, (energy I xs (T.ready k).iterate -
      energy I xs (T.ready (k + 1)).iterate)) =
      energy I xs (T.ready 0).iterate - energy I xs (T.ready N).iterate by
      have hh := Finset.sum_range_sub (fun k => energy I xs (T.ready k).iterate) N
      rw [Finset.sum_sub_distrib] at hh ⊢
      linarith] at hs
  have hd0 : 0 ≤ ∑ k ∈ Finset.range N, trajectoryDisplacement T k ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD0 : 0 ≤ ∑ k ∈ Finset.range N, (T.steps k).trial.weight * trajectorySurplus T k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (T.steps k).resolved.2.2.1.le
      (trajectory_surplus_nonneg h T k))
  have he0 := (T.ready 0).valid.energy_bound
  have heN := trajectory_energy_nonneg h T N
  constructor <;> linarith

lemma trajectory_log_ratio (h : Conditions q I xs) (T : Trajectory q I xs r0) (n : ℕ) :
    Real.log ((T.steps n).trial.weight / (T.ready n).start) =
      Real.log (T.ready (n + 1)).start - Real.log (T.ready n).start +
        Real.log (restartFactor q.toPublic) := by
  have hL1 := h.hL1
  have hR := h.radiusPositive
  have hQ : 0 < restartFactor q.toPublic := by unfold restartFactor; positivity
  have ht := (T.steps n).resolved.2.2.1
  rw [trajectory_start_step, Real.log_div ht.ne' hQ.ne',
    Real.log_div ht.ne' (T.ready n).startPositive.ne']
  ring

lemma trajectory_calls_bound (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ) :
    (trajectoryCalls T N : ℝ) ≤
      2 * N * (2 + refinementSteps q.toPublic + Real.log (restartFactor q.toPublic) / Real.log 2) +
        2 * (Real.log (T.ready N).start - Real.log r0.start) / Real.log 2 := by
  have hstep : ∀ k ∈ Finset.range N, ((T.steps k).pairs : ℝ) ≤
      (Real.log (T.ready (k + 1)).start - Real.log (T.ready k).start) / Real.log 2 +
        (2 + refinementSteps q.toPublic + Real.log (restartFactor q.toPublic) / Real.log 2) := by
    intro k _
    have hc := (T.steps k).cost
    rw [trajectory_log_ratio h T k] at hc
    convert hc using 1
    ring
  have hs := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_range_sub (fun k => Real.log (T.ready k).start) N] at hs
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, T.initial] at hs
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [trajectoryCalls, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, mul_add, mul_assoc,
    mul_div_assoc, add_comm] using hm

lemma trajectory_selected_payments (h : Conditions q I xs) (T : Trajectory q I xs r0)
    (N : ℕ) (s : Finset ℕ) (hsub : s ⊆ Finset.range N) :
    (∑ k ∈ s, trajectoryDisplacement T k ^ 2) ≤ 12 * q.R ^ 2 ∧
      (∑ k ∈ s, (T.steps k).trial.weight * trajectorySurplus T k) ≤ 3 * q.R ^ 2 := by
  have htotal := trajectory_payments h T N
  have hd := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => sq_nonneg (trajectoryDisplacement T k))
  have hD := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => mul_nonneg (T.steps k).resolved.2.2.1.le (trajectory_surplus_nonneg h T k))
  exact ⟨hd.trans htotal.1, hD.trans htotal.2⟩

lemma trajectory_selected_fraction (T : Trajectory q I xs r0) (N : ℕ) (s : Finset ℕ)
    (hsub : s ⊆ Finset.range N) :
    (∑ k ∈ s, (T.steps k).trial.weight / (T.ready (k + 1)).iterate.weight) ≤
      Real.log (T.ready N).iterate.weight - Real.log (T.ready 0).iterate.weight := by
  have hh := LongTails.Proofs.CohypomonotoneNewtonEnergy.fraction_sum_le_log
    (fun k => (T.ready k).iterate.weight) (fun k => (T.steps k).trial.weight) N
    (fun k _ => (T.ready k).valid.weightPositive)
    (fun k _ => (T.steps k).resolved.2.2.1.le) (fun k _ => trajectory_weight_step T k)
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
    div_nonneg (T.steps k).resolved.2.2.1.le (T.ready (k + 1)).valid.weightPositive.le)
  exact hs.trans hh

end OracleTemplate.CompositeAdaptive
