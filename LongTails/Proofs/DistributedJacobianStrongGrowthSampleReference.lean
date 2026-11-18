import LongTails.Proofs.DistributedJacobianStrongGrowthWorkerReference
import LongTails.Proofs.DistributedJacobianStrongGrowthQueryAccounting

namespace LongTails.Proofs.DistributedJacobianStrongGrowthSampleReference

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthQueryAccounting
open DistributedJacobianStrongGrowthWorkerReference
open DistributedJacobianStrongGrowthExecution

lemma refinement_used (p : Params) (state : State p) (used epoch localUsed : ℕ)
    (g : Point p → p.Ω → Point p) (x : Point p) (samples : ℕ → p.Ω)
    (hs : state.phase = .refinement epoch)
    (hw : state.work = some (extraWork p (localDepth p) g x samples localUsed))
    (hu : localUsed ≤ 2 * localDepth p) (h : Accounted p state used) :
    used = warmCount p (localDepth p) + 2 * localDepth p * epoch + localUsed := by
  simp only [Accounted, workRemaining, hw, hs, targetQueries,
    extraWork_remaining p (localDepth p) g x samples localUsed hu, Nat.mul_add, Nat.mul_one] at h
  omega

lemma sample_index (p : Params) (epoch localUsed : ℕ) (i : Fin p.n) :
    p.n * (warmCount p (localDepth p) + 2 * localDepth p * epoch + localUsed) + i.val =
      p.n * (warmCount p (localDepth p) + 2 * localDepth p * epoch) + (p.n * localUsed + i.val) := by
  simp [Nat.mul_add, Nat.add_assoc]

lemma refinement_answer_work (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (state : State p) (oracle next : ComputationState p)
    (epoch localUsed : ℕ) (x value : Point p) (time : DistributedTemplate.Time)
    (hs : state.phase = .refinement epoch)
    (hw : state.work = some (extraWork p (localDepth p) (g i) x
      (fun k => oracle.samples (p.n * (warmCount p (localDepth p) + 2 * localDepth p * epoch) + (p.n * k + i.val))) localUsed))
    (hu : localUsed < 2 * localDepth p) (h : Accounted p state oracle.used)
    (hm : PendingMatches p state oracle)
    (ha : (computation p g S).answer i oracle time = some (value, next)) :
    (update p i state (.computed value)).work = some (extraWork p (localDepth p) (g i) x
      (fun k => oracle.samples (p.n * (warmCount p (localDepth p) + 2 * localDepth p * epoch) + (p.n * k + i.val))) (localUsed + 1)) := by
  obtain ⟨finish, point, hpending, _, hvalue, _⟩ :=
    DistributedJacobianStrongGrowthOracle.computation_received_data p g S i oracle next time value ha
  obtain ⟨work, hwork, hquery⟩ := hm.2 finish point hpending
  have he : work = extraWork p (localDepth p) (g i) x
      (fun k => oracle.samples (p.n * (warmCount p (localDepth p) + 2 * localDepth p * epoch) + (p.n * k + i.val))) localUsed := by
    exact Option.some.inj (hwork.symm.trans hw)
  subst work
  have hbusy : state.busy = true := by simpa only [hpending, Option.isSome_some] using hm.1.symm
  rw [DistributedJacobianStrongGrowthProtocol.update_computed p i state _ value hw hbusy]
  have hused := refinement_used p state oracle.used epoch localUsed (g i) x _ hs hw hu.le h
  rw [hused, sample_index] at hvalue
  simp only
  rw [hvalue]
  exact congrArg some (extraWork_reply p (localDepth p) (g i) x _ localUsed hu point hquery)

lemma warm_used (p : Params) (state : State p) (used localUsed : ℕ) (x : Point p)
    (hs : state.phase = .warming)
    (hw : state.work = some (.warm (warmCount p (localDepth p) - localUsed) x))
    (hu : localUsed ≤ warmCount p (localDepth p)) (h : Accounted p state used) : used = localUsed := by
  simp only [Accounted, workRemaining, hw, hs, targetQueries,
    LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries] at h
  omega

lemma warm_answer_work (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (state : State p) (oracle next : ComputationState p)
    (localUsed : ℕ) (value : Point p) (time : DistributedTemplate.Time)
    (hs : state.phase = .warming)
    (hw : state.work = some (.warm (warmCount p (localDepth p) - localUsed)
      (LongTails.Algorithms.LocalNonlinearExtragradient.warmRun (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0
        (fun k => oracle.samples (p.n * k + i.val)) localUsed)))
    (hu : localUsed < warmCount p (localDepth p)) (h : Accounted p state oracle.used)
    (hm : PendingMatches p state oracle)
    (ha : (computation p g S).answer i oracle time = some (value, next)) :
    (update p i state (.computed value)).work = some (.warm (warmCount p (localDepth p) - (localUsed + 1))
      (LongTails.Algorithms.LocalNonlinearExtragradient.warmRun (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0
        (fun k => oracle.samples (p.n * k + i.val)) (localUsed + 1))) := by
  obtain ⟨finish, point, hpending, _, hvalue, _⟩ :=
    DistributedJacobianStrongGrowthOracle.computation_received_data p g S i oracle next time value ha
  obtain ⟨work, hwork, hquery⟩ := hm.2 finish point hpending
  have he : work = .warm (warmCount p (localDepth p) - localUsed)
      (LongTails.Algorithms.LocalNonlinearExtragradient.warmRun (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0
        (fun k => oracle.samples (p.n * k + i.val)) localUsed) := Option.some.inj (hwork.symm.trans hw)
  subst work
  have hbusy : state.busy = true := by simpa only [hpending, Option.isSome_some] using hm.1.symm
  have hused := warm_used p state oracle.used localUsed _ hs hw hu.le h
  have hrem : warmCount p (localDepth p) - localUsed =
      (warmCount p (localDepth p) - (localUsed + 1)) + 1 := by omega
  rw [hrem, LongTails.Algorithms.DistributedLocalExtragradientWorker.query] at hquery
  have hx := Option.some.inj hquery
  rw [DistributedJacobianStrongGrowthProtocol.update_computed p i state _ value hw hbusy]
  rw [hused, ← hx] at hvalue
  simp only
  rw [hvalue]
  exact congrArg some (DistributedJacobianStrongGrowthWorker.warm_reply_run p (warmCount p (localDepth p))
    localUsed hu (g i) p.x0 (fun k => oracle.samples (p.n * k + i.val)))

open DistributedTemplate

lemma samples_notification (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (i : Fin p.n) (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    ∀ v, (next.computation v).samples = (c.oracle.computation v).samples := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i next he).1]
      exact fun _ => rfl
  | computed value =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      obtain ⟨_, _, _, _, _, rfl⟩ :=
        DistributedJacobianStrongGrowthOracle.computation_received_data p g S i (c.oracle.computation i) oracle c.time value ha
      intro v
      by_cases hv : v = i
      · subst v
        simp [Function.update]
      · simp [Function.update, hv]
  | received message =>
      obtain ⟨oracle, _, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      exact fun _ => rfl

lemma samples_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time) (c next : ExecutionState (system p g S) (algorithm p idle))
    (hs : step (system p g S) (algorithm p idle) c = some next) :
    ∀ v, (next.oracle.computation v).samples = (c.oracle.computation v).samples := by
  classical
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · simp only [ite_eq_right hlate] at hs
    cases he : event (system p g S) (algorithm p idle) c c.time with
    | none =>
        rw [he] at hs
        by_cases ht : c.time = c.deadline
        · simp only [ite_eq_left ht, reduceCtorEq] at hs
        · rw [ite_eq_right ht] at hs
          have hh := Option.some.inj hs
          subst next
          exact fun _ => rfl
    | some result =>
        obtain ⟨⟨i, notification⟩, oracle⟩ := result
        have hn := samples_notification p g S idle c i notification oracle he
        rw [he] at hs
        cases hq : query p i (update p i (c.workers i) notification) with
        | mk action worker =>
            simp only [algorithm, hq] at hs
            cases action with
            | compute x =>
                dsimp only at hs
                have hh := Option.some.inj hs
                subst next
                intro v
                by_cases hv : v = i
                · subst v
                  cases hpending : (oracle.computation i).pending <;>
                    simpa [Function.update, system, computation, hpending] using hn i
                · simpa [Function.update, hv] using hn v
            | communicate packet =>
                dsimp only at hs
                have hh := Option.some.inj hs
                subst next
                exact hn
            | advance code =>
                dsimp only at hs
                have hh := Option.some.inj hs
                subst next
                exact hn

lemma samples_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time) (k : ℕ) (c : ExecutionState (system p g S) (algorithm p idle)) :
    ∀ v, ((run (system p g S) (algorithm p idle) k c).oracle.computation v).samples =
      (c.oracle.computation v).samples := by
  induction k generalizing c with
  | zero => exact fun _ => rfl
  | succ k ih =>
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => exact fun _ => by simp [run, hs]
      | some next =>
          intro v
          simpa only [run, hs] using (ih next v).trans (samples_step p g S idle c next hs v)

lemma samples_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle deadline : Time) (seed : (algorithm p idle).Seed × (system p g S).Seed)
    (k : ℕ) (v : Fin p.n) :
    ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).oracle.computation v).samples =
      fun j => S.sample j seed.2 :=
  samples_run p g S idle k _ v

end LongTails.Proofs.DistributedJacobianStrongGrowthSampleReference
