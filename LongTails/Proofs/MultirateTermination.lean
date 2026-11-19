import LongTails.Algorithms.MultirateSchedule
import LongTails.Proofs.LeonTermination

namespace LongTails.Proofs.MultirateTermination

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex (system)
open LongTails.Algorithms
open MultirateSchedule
open LeonInstructionCount (Size depth depth_eq)

variable {p : Params}

noncomputable def length (p : Params) (i : Fin p.n) : List ℕ → ℕ
  | [] => 0
  | k :: ks =>
    length p i ks + (due p k).length + if k % (period p i : ℕ) = 0 ∧ k + period p i < K p then (p.n : ℕ) + 1 else 0

lemma publish_size (i : Fin p.n) (x : Point p) {q : LeonProtocol.Program (network p)} {c : ℕ}
    (hq : Size q c) : Size (publish p i x q) (c + p.n + 1) := by
  apply Size.sample
  intro vs
  simpa using LeonInstructionCount.size_post (fun _ => packet p vs) hq (List.finRange p.n)

lemma program_size (i : Fin p.n) (a b : ℕ) (ks : List ℕ) (model : Model p) (bs : Table p) :
    Size (program p i a b ks model bs) (length p i ks) := by
  induction ks generalizing model bs with
  | nil => exact Size.finish _
  | cons k ks ih =>
    simp only [program, length]
    have hn := LeonInstructionCount.size_collect (p := network p) (fun data => ih (update p model data) data) (due p k) bs
    split_ifs
    · simpa [Nat.add_assoc] using publish_size i model.point hn
    · simpa using hn

lemma initial_balanced (i : Fin p.n) (a b : ℕ) :
    Size (initialProgram p i a b) (depth (initialProgram p i a b)) := by
  unfold initialProgram
  split_ifs
  · exact Size.finish _
  · have hh := publish_size i p.x0 (program_size i a b (List.range (K p)) (LeonTrajectory.initial (network p)) (fun _ => []))
    rw [depth_eq hh]
    exact hh

variable (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p)) (T : Time)

abbrev RunState := ExecutionState (system (network p) g P) (algorithm p T)

def asLeon (c : RunState g P T) : LeonClock.RunState g P T :=
  ⟨c.time, c.deadline, c.workers, c.wakeTime, c.turn, c.oracle⟩

lemma step_eq (c : RunState g P T) :
    (step (system (network p) g P) (algorithm p T) c).map (asLeon g P T) =
      step (system (network p) g P) (LeonProtocol.algorithm (network p) T) (asLeon g P T c) := by
  let O := system (network p) g P
  let A := LeonProtocol.algorithm (network p) T
  have he : event O A (asLeon g P T c) = event O (algorithm p T) c := rfl
  have ht : (asLeon g P T c).time = c.time := rfl
  have hd : (asLeon g P T c).deadline = c.deadline := rfl
  change (step O (algorithm p T) c).map _ = step O A (asLeon g P T c)
  by_cases h : c.deadline < c.time
  · simp only [step,ht,hd,ite_eq_left h,Option.map_none]
  simp only [step,ht,hd,ite_eq_right h,he]
  cases hv : event O (algorithm p T) c c.time with
  | none =>
    by_cases hlim : c.time = c.deadline <;> (simp only [hlim, ↓reduceIte,Option.map_none,Option.map_some] <;> rfl)
  | some z =>
    obtain ⟨⟨i,e⟩,o⟩ := z
    dsimp only [A,algorithm,LeonProtocol.algorithm,asLeon]
    cases ha : (LeonProtocol.query (network p) (LeonProtocol.update (network p) (c.workers i) e)).1 <;> rfl

lemma balanced_step (c next : RunState g P T)
    (hc : ∀ i, LeonProgramCost.balanced (c.workers i)) (ht : c.time ≤ c.deadline)
    (hd : c.deadline ≤ T) (hs : step (system (network p) g P) (algorithm p T) c = some next) :
    (∀ i, LeonProgramCost.balanced (next.workers i)) ∧
      LeonClock.rank g P T (asLeon g P T next) < LeonClock.rank g P T (asLeon g P T c) := by
  let O := system (network p) g P
  let A := LeonProtocol.algorithm (network p) T
  let a := asLeon g P T c
  let b := asLeon g P T next
  have h : step O A a = some b := by rw [← step_eq g P T c, hs]; rfl
  change (∀ i, LeonProgramCost.balanced (b.workers i)) ∧ LeonClock.rank g P T b < LeonClock.rank g P T a
  have htime : a.time ≤ a.deadline := ht
  cases he : event O A a a.time with
  | some z =>
    obtain ⟨⟨i,e⟩,o⟩ := z
    have hb := Option.some.inj (h.symm.trans (LeonClock.step_event g P T a i e o htime he))
    rw [hb]
    constructor
    · intro j
      by_cases hij : j = i
      · subst j
        simpa [LeonClock.eventStep,a,asLeon] using (LeonProgramCost.query_control (network p) _
          (LeonProgramCost.update_control (network p) _ e (hc i)).1).1
      · simpa [LeonClock.eventStep,a,asLeon,Function.update_of_ne hij] using hc j
    · have hdec := LeonClock.event_credits g P T a i e o (hc i) ht hd he
      unfold LeonClock.rank
      split_ifs <;> omega
  | none =>
    simp only [step, ite_eq_right (not_lt.mpr htime), he] at h
    split_ifs at h with hfinal
    injection h with heq
    rw [← heq]
    refine ⟨hc, ?_⟩
    have hnext := DistributedExecution.nextTime_spec _ _ _ (LeonNetwork.next_exists _ g P A a htime)
    have hgood : (event O A {a with time := nextTime (event O A a) a.time a.deadline}
        (nextTime (event O A a) a.time a.deadline)).isSome ∨
        nextTime (event O A a) a.time a.deadline = a.deadline := hnext.1.2.2.symm
    change 2 * LeonClock.credits g P T a + (if _ then 0 else 1) < 2 * LeonClock.credits g P T a + (if _ then 0 else 1)
    rw [ite_eq_left hgood]
    have hn : ¬((event O A a a.time).isSome ∨ a.time = a.deadline) := by simp [he,hfinal]
    rw [ite_eq_right hn]; omega

lemma finite (seed : (algorithm p T).Seed × Samples p) :
    FiniteEvents (system (network p) g P) (algorithm p T) T seed := by
  intro t ht
  let O := system (network p) g P
  let A := algorithm p T
  let inv (c : RunState g P T) :=
    (∀ i, LeonProgramCost.balanced (c.workers i)) ∧ c.time ≤ c.deadline ∧ c.deadline ≤ T
  apply DistributedExecution.termination_of_rank O A inv (fun c => LeonClock.rank g P T (asLeon g P T c))
  · intro c d hc hs
    obtain ⟨hbal, htime, hlim⟩ := hc
    obtain ⟨hb,hr⟩ := balanced_step g P T c d hbal htime hlim hs
    exact ⟨⟨hb,DistributedExecution.step_time_le_deadline O A c d htime hs,
      (DistributedExecution.step_deadline O A c d hs).trans_le hlim⟩,hr⟩
  · exact ⟨fun i => initial_balanced i seed.1.1 seed.1.2,zero_le, ht⟩

end LongTails.Proofs.MultirateTermination
