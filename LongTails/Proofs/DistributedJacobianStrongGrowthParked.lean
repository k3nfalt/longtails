import LongTails.Proofs.DistributedJacobianStrongGrowthLiveShape

namespace LongTails.Proofs.DistributedJacobianStrongGrowthParked

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree

def Parked (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle)) : Prop :=
  ∀ v, c.time < c.wakeTime v → (query p v (c.workers v)).1 = .advance 1

lemma parked_initial (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle deadline : Time) (seed : (algorithm p idle).Seed × (system p g S).Seed) :
    Parked p g S idle (initial (system p g S) (algorithm p idle) deadline seed) := by
  intro v hv
  exact False.elim (lt_irrefl (0 : Time) hv)

lemma query_advance_nonzero (p : Params) (v : Fin p.n) (s next : State p) (code : ClockReading)
    (hc : code ≠ 0) (hq : query p v s = (.advance code, next)) : code = 1 ∧ next = s := by
  unfold query at hq
  split at hq
  · cases hq
  · split at hq
    · split_ifs at hq
      · have he := Prod.mk.inj hq
        exact ⟨(Action.advance.inj he.1).symm, he.2.symm⟩
      · split at hq
        · cases hq
        · exact False.elim (hc (Action.advance.inj (Prod.mk.inj hq).1).symm)
    · split_ifs at hq
      · exact False.elim (hc (Action.advance.inj (Prod.mk.inj hq).1).symm)
      · cases hq
      · have he := Prod.mk.inj hq
        exact ⟨(Action.advance.inj he.1).symm, he.2.symm⟩

lemma query_park_data (p : Params) (v : Fin p.n) (s : State p)
    (h : (query p v s).1 = .advance 1) :
    s.queue = [] ∧
      (∀ work, s.work = some work → s.busy = true) ∧
      (s.work = none → ¬ (s.ready ∧ ¬ s.sent ∧ children p v ⊆ s.collector.seen)) := by
  classical
  cases hqueue : s.queue with
  | cons packet rest => simp [query, hqueue] at h
  | nil =>
      refine ⟨rfl, ?_, ?_⟩
      · intro work hw
        cases hb : s.busy with
        | true => rfl
        | false =>
            cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work <;>
              simp [query, hqueue, hw, hb, hquery, clockBits] at h
      · intro hw hr
        by_cases hv : v = p.root
        · subst v
          simp [query, hqueue, hw, hr, clockBits] at h
        · simp [query, hqueue, hw, hr, hv] at h

lemma parked_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c next : ExecutionState (system p g S) (algorithm p idle))
    (h : Parked p g S idle c) (hs : step (system p g S) (algorithm p idle) c = some next) :
    Parked p g S idle next := by
  classical
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · rw [ite_eq_right hlate] at hs
    cases he : event (system p g S) (algorithm p idle) c c.time with
    | none =>
        rw [he] at hs
        by_cases ht : c.time = c.deadline
        · simp only [ite_eq_left ht, reduceCtorEq] at hs
        · rw [ite_eq_right ht] at hs
          have hstate := Option.some.inj hs
          subst next
          intro v hv
          exact h v ((DistributedExecution.nextTime_ge _ _ _).trans_lt hv)
    | some result =>
        obtain ⟨⟨i, notification⟩, oracle⟩ := result
        rw [he] at hs
        cases hq : query p i (update p i (c.workers i) notification) with
        | mk action worker =>
            simp only [algorithm, hq] at hs
            cases action with
            | compute x =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                intro v hv
                by_cases hi : v = i
                · subst v
                  simp [Function.update] at hv
                · simpa [Function.update, hi] using h v (by simpa [Function.update, hi] using hv)
            | communicate packet =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                intro v hv
                by_cases hi : v = i
                · subst v
                  simp [Function.update] at hv
                · simpa [Function.update, hi] using h v (by simpa [Function.update, hi] using hv)
            | advance code =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                intro v hv
                by_cases hi : v = i
                · subst v
                  have hcode : code ≠ 0 := by
                    intro hz
                    subst code
                    simp [Function.update] at hv
                  obtain ⟨hc, hw⟩ := query_advance_nonzero p i (update p i (c.workers i) notification) worker code hcode hq
                  have hworker : (query p i worker).1 = .advance 1 := by
                    rw [hw]
                    simpa only [hc] using congrArg Prod.fst hq
                  simpa [Function.update, algorithm] using hworker
                · simpa [Function.update, hi] using h v (by simpa [Function.update, hi] using hv)

lemma parked_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (k : ℕ) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : Parked p g S idle c) : Parked p g S idle (run (system p g S) (algorithm p idle) k c) := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using h
      | some next => simpa only [run, hs] using ih next (parked_step p g S idle c next h hs)

lemma parked_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle deadline : Time) (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) :
    Parked p g S idle (run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)) :=
  parked_run p g S idle k _ (parked_initial p g S idle deadline seed)

end LongTails.Proofs.DistributedJacobianStrongGrowthParked
