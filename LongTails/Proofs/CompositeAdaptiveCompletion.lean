import LongTails.Proofs.CompositeAdaptiveComplexity

namespace OracleTemplate.CompositeAdaptive

open LongTails.Setups.RadiusCompositeGeneralizedSmooth
open LongTails.Algorithms.RadiusCompositeAccelerated

lemma trajectory_first_stop {q : Params} {I : Instance q.toPublic} {xs : q.E}
    {r0 : ReadyState q I xs} (h : Conditions q I xs) (T : Trajectory q I xs r0)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0)) :
    ∃ N : ℕ, targetWeight q.toPublic ≤ (T.ready N).iterate.weight ∧
      (∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) ∧
      (N : ℝ) ≤ 1024 * rateFactor q * logFactor q := by
  classical
  have hex := trajectory_reaches_target h T hweight
  let N := Nat.find hex
  have hs : targetWeight q.toPublic ≤ (T.ready N).iterate.weight := Nat.find_spec hex
  have ha : ∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic := by
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)
  refine ⟨N, hs, ha, ?_⟩
  by_cases hz : N = 0
  · subst N
    obtain ⟨_, hκ, _, hℓ, hV⟩ := parameter_bounds h
    have hv : 0 ≤ rateFactor q := by linarith
    have hl : 0 ≤ logFactor q := by linarith
    rw [hz]
    simpa only [Nat.cast_zero] using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024) hv) hl
  · have hi := ha 0 (Nat.pos_of_ne_zero hz)
    rw [T.initial] at hi
    exact active_iteration_bound h T N hweight hi ha

lemma trajectory_first_stop_cost {q : Params} {I : Instance q.toPublic} {xs : q.E}
    {r0 : ReadyState q I xs} (h : Conditions q I xs) (T : Trajectory q I xs r0)
    (hweight : r0.iterate.weight = initialWeight q.toPublic (I.grad q.x0))
    (hstart : r0.start = r0.iterate.weight / 16) :
    ∃ N : ℕ, targetWeight q.toPublic ≤ (T.ready N).iterate.weight ∧
      (∀ k < N, (T.ready k).iterate.weight < targetWeight q.toPublic) ∧
      2 + (trajectoryCalls T N : ℝ) ≤ 32768 * rateFactor q * logFactor q ^ 2 := by
  obtain ⟨N, hs, ha, hn⟩ := trajectory_first_stop h T hweight
  obtain ⟨_, hκ, _, hℓ, hV⟩ := parameter_bounds h
  refine ⟨N, hs, ha, final_call_budget hκ (by linarith) hV hn ?_⟩
  by_cases hz : N = 0
  · subst N
    simp only [trajectoryCalls, Finset.range_zero, Finset.sum_empty,
      Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have hl : 0 ≤ logFactor q := by linarith
    nlinarith
  · have hi := ha 0 (Nat.pos_of_ne_zero hz)
    rw [T.initial] at hi
    exact active_calls_bound h T N hweight hstart hi ha

lemma finite_execution_accuracy {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) :
    ∃ (K : ℕ) (x : q.E), (transition q.toPublic I)^[K] .initial = .finished x ∧
      (K : ℝ) ≤ 32768 * rateFactor q * logFactor q ^ 2 ∧
      x ∈ I.Q ∧ objective I x - objective I xs ≤ q.ε := by
  let A := initialWeight q.toPublic (I.grad q.x0)
  let u := I.prox (initialStep q.toPublic (I.grad q.x0)) q.x0 (I.grad q.x0)
  let s : Iterate q.E := ⟨A, u, u⟩
  have hr := initial_ready h
  change ValidIterate q I xs s ∧ 0 < A / 16 ∧ A / 16 ≤ A ∧
    accepts q.toPublic s (evaluatedTrial q.toPublic I s (A / 16)) at hr
  let r0 : ReadyState q I xs := ⟨s, A / 16, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩
  obtain ⟨T⟩ := trajectory_exists h r0
  obtain ⟨N, hs, ha, hc⟩ := trajectory_first_stop_cost h T rfl rfl
  refine ⟨trajectoryCalls T N + 2, (T.ready N).iterate.point, ?_, ?_,
    (valid_accuracy h (T.ready N).valid hs).1, (valid_accuracy h (T.ready N).valid hs).2⟩
  · rw [Function.iterate_add_apply, initialization_pair]
    have ht := trajectory_execution T N ha
    rw [ite_eq_left hs] at ht
    exact ht
  · push_cast
    linarith

lemma padded_execution_accuracy {q : Params} {I : Instance q.toPublic} {xs : q.E}
    (h : Conditions q I xs) (B : ℕ)
    (hB : 32768 * rateFactor q * logFactor q ^ 2 ≤ B) :
    output q.toPublic ((transition q.toPublic I)^[B] .initial) ∈ I.Q ∧
      objective I (output q.toPublic ((transition q.toPublic I)^[B] .initial)) -
        objective I xs ≤ q.ε := by
  obtain ⟨K, x, he, hc, hx, hf⟩ := finite_execution_accuracy h
  have hKB : K ≤ B := by exact_mod_cast hc.trans hB
  have hid : B = (B - K) + K := by omega
  rw [hid, Function.iterate_add_apply, he, finished_iterate]
  exact ⟨hx, hf⟩

end OracleTemplate.CompositeAdaptive
