import LongTails.Algorithms.StochasticQuasarProgram
import LongTails.Proofs.ProjectedClippedExecution
import LongTails.Proofs.StochasticQuasarAccelerationExecution
import LongTails.Proofs.StochasticQuasarOuterTuning
import LongTails.Proofs.StochasticQuasarCleanupExecution

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.StochasticQuasar

open QueryPlan
open LongTails.Setups.StochasticConstrainedQuasar
open LongTails.Proofs.EnergyHessianExecution (length_update)

lemma execute_program (q : Params) (g : (Fin 2 × q.E) → q.Ω → q.E)
    (O : Oracle q.E q.E 2) (hSeed : ∀ k, O.Seed k = q.Ω)
    (budget : Fin 2 → ℕ) (seed : ProgramSeed q)
    (hb : ∀ i, (program q seed).1 ≤ budget i)
    (hO : ∀ k query ω, O.answer k query ω = g query (cast (hSeed k.length) ω))
    (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm q) budget seed ξ =
      sampledEval g (fun k => cast (hSeed k) (ξ k)) (program q seed).2 0 := by
  let q0 : Fin 2 × q.E := (0, q.x0)
  let u0 := q.x0
  let K := (program q seed).1
  let plan := (program q seed).2
  let ζ := fun k => cast (hSeed k) (ξ k)
  let state : ℕ → (Σ k, QueryPlan (Fin 2 × q.E) q.E q.E k) :=
    Nat.rec ⟨K, plan⟩ (fun k s => update s (g (query q0 s) (ζ k)))
  have hstep (k : ℕ) : state (k + 1) = update (state k) (g (query q0 (state k)) (ζ k)) := rfl
  let remaining : ℕ → Fin 2 → ℕ :=
    Nat.rec budget (fun k b => Function.update b (query q0 (state k)).1
      (b (query q0 (state k)).1 - 1))
  have hremaining (k : ℕ) : remaining (k + 1) =
      Function.update (remaining k) (query q0 (state k)).1
        (remaining k (query q0 (state k)).1 - 1) := rfl
  have hcover (k : ℕ) (i : Fin 2) : K - k ≤ remaining k i := by
    induction k with
    | zero => exact hb i
    | succ k ih =>
      rw [hremaining]
      by_cases hi : i = (query q0 (state k)).1
      · rw [hi, Function.update_self]
        have := ih
        rw [hi] at this
        omega
      · rw [Function.update_of_ne hi]
        omega
  have hlength (k : ℕ) : (state k).1 = K - k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, length_update (fun q => g q (ζ k)) q0, ih]; omega
  have heval (k : ℕ) : sampledEval g ζ (state k).2 k = sampledEval g ζ plan 0 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, sampledEval_update, ih]
  apply execute_eq_of_safe_prefix O (algorithm q) budget seed ξ
    state remaining K (sampledEval g ζ plan 0)
  · rfl
  · intro k
    change state (k.length + 1) = update (state k.length)
      (O.answer k (query q0 (state k.length)) (ξ k.length))
    rw [hO]
  · rfl
  · exact hremaining
  · intro k hk
    exact (Nat.sub_pos_of_lt hk).trans_le (hcover k _)
  · intro k hk
    change QueryPlan.output u0 (state k) = _
    have hz : (state k).1 = 0 := by rw [hlength]; omega
    have hout : QueryPlan.output u0 (state k) = sampledEval g ζ (state k).2 k := by
      generalize state k = st at hz ⊢
      obtain ⟨j, pl⟩ := st
      cases pl with
      | done value => rfl
      | ask q rest => simp at hz
    rw [hout, heval]
  · exact (hb q0.1).trans (Finset.single_le_sum (fun i _ => Nat.zero_le (budget i)) (Finset.mem_univ q0.1))

lemma program_calls_le (q : Params) (seed : ProgramSeed q) :
    (program q seed).1 ≤ workCap q + cleanupCalls q := by
  unfold program
  split_ifs with he hc
  · dsimp only
    unfold cleanupCalls
    omega
  · change cleanupCalls q + outerCalls q seed ≤ _
    omega
  · exact Nat.zero_le _

lemma sampled_outer_seeded (q : Params) (P : q.E → q.E) (g : q.E → q.Ω → q.E)
    (seed : ProgramSeed q) (ξ : ℕ → q.Ω) :
    sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ (outerPlan q seed) 0 =
      seededStreamRun
        (fun a : OuterSeed q => accelerationJumpCalls q.L q.σ q.D (outerDeviation q) (outerBias q) a.2.val)
        (fun state a ζ => sampledEval (ProjectedClippedExtragradient.channelReply P g) ζ
          (accelerationAdvancePlan (outerWeight q) (outerMirror q) (outerThreshold q)
            q.γ q.L q.σ q.D (outerDeviation q) (outerBias q) (outerStep q) q.x0 a state) 0)
        (outerCount q) (0, q.x0, q.x0) seed ξ := by
  have hh := sampled_acceleration_run_seeded P g ξ (outerWeight q) (outerMirror q) (outerThreshold q)
    q.γ q.L q.σ q.D (outerDeviation q) (outerBias q) (outerStep q) q.x0
    (extendOuterSeeds q seed) (outerCount q) 0 0 (0, q.x0, q.x0)
  simpa [outerPlan, outerCalls, extendOuterSeeds] using hh

lemma sampled_complete (q : Params) (P : q.E → q.E) (g : q.E → q.Ω → q.E)
    (seed : ProgramSeed q) (ξ : ℕ → q.Ω) :
    sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ (completePlan q seed) 0 =
      let state := sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ (outerPlan q seed) 0
      sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (cleanupPlan q.L q.σ q.D (outputRadius q) state.2.1 q.x0 (outputBatch q) (outerOrder q))
        (outerCalls q seed) := by
  simpa only [completePlan, cleanupCalls, Nat.zero_add] using
    sampledEval_bind (ProjectedClippedExtragradient.channelReply P g) ξ (outerPlan q seed)
      (fun state => cleanupPlan q.L q.σ q.D (outputRadius q) state.2.1 q.x0 (outputBatch q) (outerOrder q)) 0

lemma measurable_extend_outer_seeds (q : Params) : Measurable (extendOuterSeeds q) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i < outerCount q
  · simpa only [extendOuterSeeds, hi, dite_true] using (measurable_pi_apply (⟨i, hi⟩ : Fin (outerCount q)))
  · simp only [extendOuterSeeds, hi, dite_false]
    exact measurable_const

lemma measurable_outer_execution {q : Params} (hv : spec.valid q)
    {P : q.E → q.E} {g : q.E → q.Ω → q.E} (hP : Measurable P) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : ProgramSeed q × (ℕ → q.Ω) =>
      sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (outerPlan q w.1) 0) := by
  exact measurable_acceleration_run_parameters hP hg (continuous_outer_weight q) (outer_weight_pos hv)
    hv.2.2.1.le (continuous_outer_mirror q).measurable (continuous_outer_threshold hv).measurable
    q.L q.σ q.D (outerDeviation q) (outerBias q) (outerStep q) q.x0 (outerCount q) 0
    (measurable_const (a := (0, q.x0, q.x0)))
    ((measurable_extend_outer_seeds q).comp measurable_fst) measurable_snd (measurable_const (a := 0))

lemma sampled_outer_clock (q : Params) (P : q.E → q.E) (g : q.E → q.Ω → q.E)
    (seed : ProgramSeed q) (ξ : ℕ → q.Ω) :
    (sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ (outerPlan q seed) 0).1 =
      ∑ i : Fin (outerCount q), max 0 (seed i).1 := by
  have hh := sampled_acceleration_run_clock P g ξ (outerWeight q) (outerMirror q) (outerThreshold q)
    q.γ q.L q.σ q.D (outerDeviation q) (outerBias q) (outerStep q) q.x0
    (extendOuterSeeds q seed) (outerCount q) 0 0 (0, q.x0, q.x0)
  rw [← Fin.sum_univ_eq_sum_range] at hh
  simpa [outerPlan, outerCalls, extendOuterSeeds] using hh

lemma sampled_complete_shift (q : Params) (P : q.E → q.E) (g : q.E → q.Ω → q.E)
    (seed : ProgramSeed q) (ξ : ℕ → q.Ω) :
    sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ (completePlan q seed) 0 =
      let state := sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ (outerPlan q seed) 0
      sampledEval (ProjectedClippedExtragradient.channelReply P g) (fun i => ξ (outerCalls q seed + i))
        (cleanupPlan q.L q.σ q.D (outputRadius q) state.2.1 q.x0 (outputBatch q) (outerOrder q)) 0 := by
  rw [sampled_complete]
  exact StochasticCohypomonotone.sampledEval_shift _ _ ξ (outerCalls q seed)

lemma sampled_program (q : Params) (g : (Fin 2 × q.E) → q.Ω → q.E)
    (seed : ProgramSeed q) (ξ : ℕ → q.Ω) :
    sampledEval g ξ (program q seed).2 0 =
      if 4 * q.L * q.D ^ 2 ≤ q.ε then sampledEval g ξ
        (initialCleanupPlan q.L q.x0 (outputBatch q) (outerOrder q)) 0
      else if outerCalls q seed ≤ workCap q then sampledEval g ξ (completePlan q seed) 0 else q.x0 := by
  let ev := fun plan : Σ k, QueryPlan (Fin 2 × q.E) q.E q.E k => sampledEval g ξ plan.2 0
  by_cases he : 4 * q.L * q.D ^ 2 ≤ q.ε
  · have hp : program q seed = ⟨_, initialCleanupPlan q.L q.x0 (outputBatch q) (outerOrder q)⟩ := ite_eq_left he
    have hh := congrArg ev hp
    simpa only [he, ite_true] using hh
  · by_cases hc : outerCalls q seed ≤ workCap q
    · have hp : program q seed = ⟨_, completePlan q seed⟩ := (ite_eq_right he).trans (ite_eq_left hc)
      have hh := congrArg ev hp
      simpa only [he, ite_false, hc, ite_true] using hh
    · have hp : program q seed = ⟨0, .done q.x0⟩ := (ite_eq_right he).trans (ite_eq_right hc)
      have hh := congrArg ev hp
      simpa only [he, ite_false, hc, ev, sampledEval] using hh

lemma sampled_program_mem (q : Params) {Q : Set q.E} {P : q.E → q.E}
    (hP : ∀ y, P y ∈ Q) (hx0 : q.x0 ∈ Q) (g : q.E → q.Ω → q.E)
    (seed : ProgramSeed q) (ξ : ℕ → q.Ω) :
    sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ (program q seed).2 0 ∈ Q := by
  rw [sampled_program]
  split_ifs
  · rw [sampled_initial_cleanup]
    exact hP _
  · rw [sampled_complete]
    exact sampled_cleanup_mem hP g ξ q.L q.σ q.D (outputRadius q) _ q.x0 (outputBatch q) (outerOrder q) _
  · exact hx0

end OracleTemplate.StochasticQuasar
