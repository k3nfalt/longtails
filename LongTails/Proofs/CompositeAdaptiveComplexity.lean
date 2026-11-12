import LongTails.Proofs.CompositeAdaptiveTrajectory
import LongTails.Proofs.CompositeAdaptiveBudget

namespace OracleTemplate.CompositeAdaptive

open LongTails.Setups.RadiusCompositeGeneralizedSmooth
open LongTails.Algorithms.RadiusCompositeAccelerated

noncomputable def solutionCurvature (q : Params) : ℝ := q.L0 + q.L1 * q.G

noncomputable def radiusCondition (q : Params) : ℝ := q.L1 * q.R

noncomputable def accuracyCondition (q : Params) : ℝ := solutionCurvature q * q.R ^ 2 / q.ε

noncomputable def logFactor (q : Params) : ℝ :=
  Real.log (128 * (1 + radiusCondition q + accuracyCondition q))

noncomputable def rateFactor (q : Params) : ℝ :=
  (1 + radiusCondition q) ^ (4 / 3 : ℝ) + Real.sqrt (accuracyCondition q)

variable {q : Params} {I : Instance q.toPublic} {xs : q.E} {r0 : ReadyState q I xs}

lemma parameter_bounds (h : Conditions q I xs) :
    0 < solutionCurvature q ∧ 0 ≤ radiusCondition q ∧ 0 < accuracyCondition q ∧
      4 ≤ logFactor q ∧ 1 + radiusCondition q ≤ rateFactor q := by
  have hL0 := h.hL0
  have hL1 := h.hL1
  have hR := h.radiusPositive
  have hε := h.accuracyPositive
  have hG : 0 ≤ q.G := (norm_nonneg _).trans h.gradient_bound
  have hM : 0 < solutionCurvature q := by unfold solutionCurvature; positivity
  have hκ : 0 ≤ radiusCondition q := mul_nonneg hL1 hR.le
  have hτ : 0 < accuracyCondition q := by unfold accuracyCondition; positivity
  have hpow := Real.self_le_rpow_of_one_le (by linarith : 1 ≤ 1 + radiusCondition q)
    (by norm_num : (1 : ℝ) ≤ 4 / 3)
  refine ⟨hM, hκ, hτ, log_scale_lower hκ hτ.le, ?_⟩
  unfold rateFactor
  linarith [Real.sqrt_nonneg (accuracyCondition q)]

lemma initial_gradient_scale (h : Conditions q I xs) :
    q.L0 + q.L1 * ‖I.grad q.x0‖ ≤ solutionCurvature q * Real.exp (radiusCondition q) := by
  have hL0 := h.hL0
  have hL1 := h.hL1
  have hG := h.gradient_bound
  have hG0 : 0 ≤ q.G := (norm_nonneg _).trans hG
  have hr := h.initial_radius
  have hg := symmetric_gradient_growth_nonneg h.cont hL1 h.smooth q.x0 xs
  calc
    _ ≤ (q.L0 + q.L1 * ‖I.grad xs‖) * Real.exp (q.L1 * ‖q.x0 - xs‖) := hg
    _ ≤ _ := by unfold solutionCurvature radiusCondition; gcongr

lemma initial_inverse (h : Conditions q I xs)
    (hinit : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0)) :
    1 / r0.iterate.weight ≤ 8 * solutionCurvature q * Real.exp (5 * radiusCondition q) := by
  have hh := initial_weight_inverse_bound (initial_gradient_scale h)
  rw [hinit]
  simpa only [initialWeight, radiusCondition, mul_assoc] using hh

lemma active_endpoint (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    (T.ready N).iterate.weight ≤ 2 * targetWeight q.toPublic := by
  have hR := h.radiusPositive
  have hε := h.accuracyPositive
  have hT : 0 < targetWeight q.toPublic := by unfold targetWeight; positivity
  cases N with
  | zero => rw [T.initial]; linarith
  | succ n =>
      rw [trajectory_weight_step]
      have ht := (T.steps n).resolved.2.2.2.1
      have ha := hactive n (by omega)
      linarith

lemma active_endpoint_products (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    solutionCurvature q * (T.ready N).iterate.weight ≤ 8 * accuracyCondition q ∧
      solutionCurvature q * (T.ready N).start ≤ 8 * accuracyCondition q := by
  have hM := (parameter_bounds h).1
  have he := mul_le_mul_of_nonneg_left (active_endpoint h T N hinit hactive) hM.le
  have hid : solutionCurvature q * (2 * targetWeight q.toPublic) = 8 * accuracyCondition q := by
    unfold targetWeight accuracyCondition
    ring
  rw [hid] at he
  exact ⟨he, (mul_le_mul_of_nonneg_left (T.ready N).start_le hM.le).trans he⟩

lemma active_log_span (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    Real.log (T.ready N).iterate.weight - Real.log (T.ready 0).iterate.weight ≤
      5 * radiusCondition q + logFactor q := by
  obtain ⟨hM, hκ, hτ, _, _⟩ := parameter_bounds h
  have he := endpoint_log_bound r0.valid.weightPositive (T.ready N).valid.weightPositive hτ
    (initial_inverse h hweight) (active_endpoint_products h T N hinit hactive).1
  rw [T.initial]
  exact endpoint_log_scale_bound hκ hτ he

lemma active_potential_span (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    countPotential (256 * solutionCurvature q) (T.ready N).iterate.weight -
      countPotential (256 * solutionCurvature q) (T.ready 0).iterate.weight ≤ 4 * logFactor q := by
  obtain ⟨hM, hκ, hτ, _, _⟩ := parameter_bounds h
  have hi := initialization_log_bound r0.valid.weightPositive hM (initial_inverse h hweight)
  have hf : (256 * solutionCurvature q) * (T.ready N).iterate.weight ≤ 2048 * accuracyCondition q := by
    nlinarith [(active_endpoint_products h T N hinit hactive).1]
  apply countPotential_parameter_span (by positivity) (T.ready 0).valid.weightPositive
    (T.ready N).valid.weightPositive hκ hτ.le
  · simpa only [T.initial] using hi
  · exact hf

lemma active_start_charge (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hstart : r0.start = r0.iterate.weight / 16)
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    (Real.log (T.ready N).start - Real.log r0.start) / Real.log 2 ≤
      8 * radiusCondition q + 3 * logFactor q := by
  obtain ⟨_, hκ, hτ, _, _⟩ := parameter_bounds h
  have hh := endpoint_start_log_bound r0.valid.weightPositive (T.ready N).startPositive hκ hτ
    (initial_inverse h hweight) (active_endpoint_products h T N hinit hactive).2
  rw [Real.log_div (T.ready N).startPositive.ne' (div_pos r0.valid.weightPositive (by norm_num)).ne'] at hh
  simpa only [hstart, logFactor] using hh

lemma active_calls_bound (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hstart : r0.start = r0.iterate.weight / 16)
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    2 + (trajectoryCalls T N : ℝ) ≤ 2 + 14 * N * logFactor q + 16 * radiusCondition q + 6 * logFactor q := by
  obtain ⟨_, hκ, hτ, hℓ, _⟩ := parameter_bounds h
  have hf := search_log_factors hκ hτ.le
  have hm : (refinementSteps q.toPublic : ℝ) ≤ 4 * logFactor q := by
    simpa only [refinementSteps, radiusCondition, logFactor, mul_assoc] using hf.1
  have hQ : Real.log (restartFactor q.toPublic) / Real.log 2 ≤ 2 * logFactor q := by
    simpa only [restartFactor, radiusCondition, logFactor, mul_assoc] using hf.2
  have hfactor : 2 + refinementSteps q.toPublic + Real.log (restartFactor q.toPublic) / Real.log 2 ≤
      7 * logFactor q := by linarith
  have hcost := trajectory_calls_bound h T N
  rw [mul_div_assoc] at hcost
  have hend := active_start_charge h T N hweight hstart hinit hactive
  have hmul := mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ 2 * (N : ℝ))
  nlinarith

noncomputable def trajectoryCurvature (T : Trajectory q I xs r0) (n : ℕ) : ℝ :=
  q.L0 + q.L1 * ‖(T.steps n).trial.gradient‖

noncomputable def curvatureTest (T : Trajectory q I xs r0) (n : ℕ) : ℝ :=
  (T.steps n).trial.weight ^ 2 * trajectoryCurvature T n / (T.ready (n + 1)).iterate.weight

noncomputable def movementTest (T : Trajectory q I xs r0) (n : ℕ) : ℝ :=
  q.L1 * ((T.steps n).trial.weight / (T.ready (n + 1)).iterate.weight) * trajectoryDisplacement T n

lemma trajectory_boundary (h : Conditions q I xs) (T : Trajectory q I xs r0) (n : ℕ) :
    (T.steps n).trial.weight = (T.ready n).iterate.weight ∨
      1 / 64 ≤ curvatureTest T n ∨ 1 / 64 ≤ movementTest T n := by
  have hh := resolved_boundary h (T.ready n).valid (T.steps n).resolved
  simpa only [curvatureTest, movementTest, trajectoryCurvature, trajectoryDisplacement,
    trajectory_weight_step] using hh

lemma active_relaxed_log_span (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    Real.log (T.ready N).iterate.weight - Real.log (T.ready 0).iterate.weight ≤
      6 * (1 + radiusCondition q) * logFactor q := by
  obtain ⟨_, hκ, _, hℓ, _⟩ := parameter_bounds h
  have hh := active_log_span h T N hweight hinit hactive
  nlinarith [mul_nonneg hκ (by linarith : 0 ≤ logFactor q - 1)]

lemma active_low_count (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (s : Finset ℕ) (hsub : s ⊆ Finset.range N)
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic)
    (hlow : ∀ k ∈ s, q.L1 * ‖(T.steps k).trial.gradient‖ ≤ 2 * solutionCurvature q)
    (hboundary : ∀ k ∈ s, 1 / 64 ≤ curvatureTest T k) :
    (s.card : ℝ) ≤ 79 * Real.sqrt (accuracyCondition q) := by
  obtain ⟨hM, _, hτ, _, _⟩ := parameter_bounds h
  have hL1 := h.hL1
  have hG0 : 0 ≤ q.G := (norm_nonneg _).trans h.gradient_bound
  have hL0 : q.L0 ≤ solutionCurvature q := by unfold solutionCurvature; nlinarith [mul_nonneg hL1 hG0]
  have hc := low_curvature_count (fun k => (T.ready k).iterate.weight)
    (fun k => (T.steps k).trial.weight) (trajectoryCurvature T) N s hM
    (fun k _ => (T.ready k).valid.weightPositive.le) (fun k _ => (T.steps k).resolved.2.2.1)
    (fun k _ => trajectory_weight_step T k) hsub
    (fun k hk => by dsimp only [trajectoryCurvature]; linarith [hlow k hk]) hboundary
  exact low_curvature_parameter_count (Nat.cast_nonneg _) hM (T.ready N).valid.weightPositive.le hτ.le
    (active_endpoint_products h T N hinit hactive).1 hc

lemma active_cap_count (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (s : Finset ℕ) (hsub : s ⊆ Finset.range N)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic)
    (hcap : ∀ k ∈ s, (T.steps k).trial.weight = (T.ready k).iterate.weight) :
    (s.card : ℝ) ≤ 9 * (1 + radiusCondition q) * logFactor q := by
  have hc := cap_count (fun k => (T.ready k).iterate.weight) (fun k => (T.steps k).trial.weight)
    N s (fun k _ => (T.ready k).valid.weightPositive) (fun k _ => (T.steps k).resolved.2.2.1.le)
    (fun k _ => trajectory_weight_step T k) hsub hcap
  exact cap_parameter_count (Nat.cast_nonneg _) hc (active_relaxed_log_span h T N hweight hinit hactive)

lemma active_displacement_count (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (s : Finset ℕ) (hsub : s ⊆ Finset.range N)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic)
    (hboundary : ∀ k ∈ s, 1 / 64 ≤ movementTest T k) :
    (s.card : ℝ) ≤ 123 * (1 + radiusCondition q) ^ (4 / 3 : ℝ) * logFactor q := by
  obtain ⟨_, hκ, _, hℓ, _⟩ := parameter_bounds h
  have hb : ∀ k ∈ s, (T.ready (k + 1)).iterate.weight ≤
      64 * q.L1 * (T.steps k).trial.weight * trajectoryDisplacement T k := by
    intro k hk
    have hh := hboundary k hk
    unfold movementTest at hh
    have hid : q.L1 * ((T.steps k).trial.weight / (T.ready (k + 1)).iterate.weight) *
        trajectoryDisplacement T k =
        (q.L1 * (T.steps k).trial.weight * trajectoryDisplacement T k) /
        (T.ready (k + 1)).iterate.weight := by ring
    rw [hid] at hh
    have hm := (le_div_iff₀ (T.ready (k + 1)).valid.weightPositive).mp hh
    linarith
  have hc := displacement_count s (fun k => (T.ready (k + 1)).iterate.weight)
    (fun k => (T.steps k).trial.weight) (trajectoryDisplacement T) h.hL1
    (fun k _ => (T.ready (k + 1)).valid.weightPositive)
    (fun k _ => (T.steps k).resolved.2.2.1.le)
    (fun k _ => norm_nonneg _) hb (trajectory_selected_payments h T N s hsub).1
    (trajectory_selected_fraction T N s hsub)
  have hH : 0 ≤ Real.log (T.ready N).iterate.weight - Real.log (T.ready 0).iterate.weight := by
    have hm := trajectory_weight_mono T (Nat.zero_le N)
    have hl := Real.log_le_log (T.ready 0).valid.weightPositive hm
    linarith
  exact displacement_parameter_count (Nat.cast_nonneg _) hκ hH (by linarith)
    (active_relaxed_log_span h T N hweight hinit hactive) hc

lemma trajectory_weighted_curvature (h : Conditions q I xs) (T : Trajectory q I xs r0) (k : ℕ)
    (hhigh : 2 * solutionCurvature q ≤ q.L1 * ‖(T.steps k).trial.gradient‖)
    (hboundary : 1 / 64 ≤ curvatureTest T k) :
    (T.ready (k + 1)).iterate.weight *
      max 1 (Real.log (1 / (256 * solutionCurvature q * (T.ready (k + 1)).iterate.weight))) ≤
      8192 * q.L1 ^ 2 * (T.steps k).trial.weight ^ 2 * trajectorySurplus T k := by
  have hM := (parameter_bounds h).1
  have hL1 : 0 < q.L1 := by
    by_contra hn
    have hz : q.L1 = 0 := le_antisymm (le_of_not_gt hn) h.hL1
    rw [hz, zero_mul] at hhigh
    linarith
  have hS : 0 ≤ trajectoryCurvature T k := by
    unfold trajectoryCurvature
    have hL0 := h.hL0
    positivity
  have hb := curvature_boundary_product (T.ready k).valid.weightPositive
    (T.steps k).resolved.2.2.1 (T.steps k).resolved.2.2.2.1 hS
    (by simpa only [curvatureTest, trajectory_weight_step] using hboundary)
  rw [← trajectory_weight_step T k] at hb
  have hg := congrArg Trial.gradient (T.steps k).resolved.1
  dsimp only [evaluatedTrial] at hg
  have hs := weighted_gradient_surplus h.hL0 hL1 h.convex h.grad h.cont h.smooth xs
    (mix (T.ready k).iterate.weight (T.steps k).trial.weight
      (T.ready k).iterate.point (T.ready k).iterate.momentum) h.gradient_bound
    (T.ready (k + 1)).valid.weightPositive
    (by simpa only [solutionCurvature, hg] using hhigh)
    (by simpa only [trajectoryCurvature, hg] using hb)
  have hs' : trajectoryCurvature T k *
      max 1 (Real.log (1 / (256 * solutionCurvature q * (T.ready (k + 1)).iterate.weight))) ≤
      128 * q.L1 ^ 2 * trajectorySurplus T k := by
    simpa only [trajectoryCurvature, solutionCurvature, trajectorySurplus, hg] using hs
  exact weighted_curvature_boundary (T.ready (k + 1)).valid.weightPositive
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) hboundary hs'

lemma active_high_count (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (s : Finset ℕ) (hsub : s ⊆ Finset.range N)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic)
    (hhigh : ∀ k ∈ s, 2 * solutionCurvature q ≤ q.L1 * ‖(T.steps k).trial.gradient‖)
    (hboundary : ∀ k ∈ s, 1 / 64 ≤ curvatureTest T k) :
    (s.card : ℝ) ≤ 444 * radiusCondition q * Real.sqrt (logFactor q) := by
  obtain ⟨hM, hκ, _, hℓ, _⟩ := parameter_bounds h
  have hf := weighted_fraction_sum (fun k => (T.ready k).iterate.weight)
    (fun k => (T.steps k).trial.weight) N s (by positivity : 0 < 256 * solutionCurvature q)
    (fun k _ => (T.ready k).valid.weightPositive)
    (fun k _ => (T.steps k).resolved.2.2.1.le)
    (fun k _ => (T.steps k).resolved.2.2.2.1)
    (fun k _ => trajectory_weight_step T k) hsub
  have hspan := active_potential_span h T N hweight hinit hactive
  have hf' : (∑ k ∈ s, ((T.steps k).trial.weight / (T.ready (k + 1)).iterate.weight) /
      max 1 (Real.log (1 / (256 * solutionCurvature q * (T.ready (k + 1)).iterate.weight)))) ≤
      8 * logFactor q := by linarith
  have hc := weighted_curvature_count s (fun k => (T.ready (k + 1)).iterate.weight)
    (fun k => (T.steps k).trial.weight) (trajectorySurplus T)
    (fun k => max 1 (Real.log (1 / (256 * solutionCurvature q * (T.ready (k + 1)).iterate.weight))))
    (by norm_num : (0 : ℝ) ≤ 8192)
    (fun k _ => (T.ready (k + 1)).valid.weightPositive)
    (fun k _ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _))
    (fun k _ => (T.steps k).resolved.2.2.1.le)
    (fun k _ => trajectory_surplus_nonneg h T k)
    (fun k hk => trajectory_weighted_curvature h T k (hhigh k hk) (hboundary k hk))
    (trajectory_selected_payments h T N s hsub).2 hf'
  apply high_curvature_parameter_count (Nat.cast_nonneg _) hκ (by linarith)
  dsimp only [radiusCondition]
  nlinarith [hc]

lemma active_iteration_bound (h : Conditions q I xs) (T : Trajectory q I xs r0) (N : ℕ)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hinit : r0.iterate.weight < targetWeight q.toPublic)
    (hactive : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) :
    (N : ℝ) ≤ 1024 * rateFactor q * logFactor q := by
  classical
  let cap := (Finset.range N).filter (fun k => (T.steps k).trial.weight = (T.ready k).iterate.weight)
  let low := (Finset.range N).filter (fun k => 1 / 64 ≤ curvatureTest T k ∧
    q.L1 * ‖(T.steps k).trial.gradient‖ ≤ 2 * solutionCurvature q)
  let high := (Finset.range N).filter (fun k => 1 / 64 ≤ curvatureTest T k ∧
    2 * solutionCurvature q < q.L1 * ‖(T.steps k).trial.gradient‖)
  let disp := (Finset.range N).filter (fun k => 1 / 64 ≤ movementTest T k)
  have hcap := active_cap_count h T N cap (Finset.filter_subset _ _) hweight hinit hactive
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hlow := active_low_count h T N low (Finset.filter_subset _ _) hinit hactive
    (fun k hk => (Finset.mem_filter.mp hk).2.2) (fun k hk => (Finset.mem_filter.mp hk).2.1)
  have hhigh := active_high_count h T N high (Finset.filter_subset _ _) hweight hinit hactive
    (fun k hk => (Finset.mem_filter.mp hk).2.2.le) (fun k hk => (Finset.mem_filter.mp hk).2.1)
  have hdisp := active_displacement_count h T N disp (Finset.filter_subset _ _) hweight hinit hactive
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hcover : Finset.range N ⊆ ((cap ∪ low) ∪ high) ∪ disp := by
    intro k hk
    rcases trajectory_boundary h T k with hc | hc | hd
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hk, hc⟩)))
    · by_cases hl : q.L1 * ‖(T.steps k).trial.gradient‖ ≤ 2 * solutionCurvature q
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hk, hc, hl⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hk, hc, lt_of_not_ge hl⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hd⟩)
  have hcard : N ≤ cap.card + low.card + high.card + disp.card := by
    have hh := Finset.card_le_card hcover
    rw [Finset.card_range] at hh
    have h1 := Finset.card_union_le (cap ∪ low ∪ high) disp
    have h2 := Finset.card_union_le (cap ∪ low) high
    have h3 := Finset.card_union_le cap low
    omega
  have hcard' : (N : ℝ) ≤ (cap.card : ℝ) + low.card + high.card + disp.card := by exact_mod_cast hcard
  obtain ⟨_, hκ, _, hℓ, _⟩ := parameter_bounds h
  exact combined_parameter_count hκ (by linarith) hcard' hcap hlow hhigh hdisp

lemma trajectory_reaches_target (h : Conditions q I xs) (T : Trajectory q I xs r0)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0)) :
    ∃ N : ℕ, targetWeight q.toPublic ≤ (T.ready N).iterate.weight := by
  by_contra hn
  push Not at hn
  have hi : r0.iterate.weight < targetWeight q.toPublic := by simpa only [T.initial] using hn 0
  let N := ⌈1024 * rateFactor q * logFactor q⌉₊ + 1
  have hb := active_iteration_bound h T N hweight hi (fun k _ => hn k)
  have hc := Nat.le_ceil (1024 * rateFactor q * logFactor q)
  have hN : (N : ℝ) = (⌈1024 * rateFactor q * logFactor q⌉₊ : ℝ) + 1 := by simp [N]
  linarith

end OracleTemplate.CompositeAdaptive
