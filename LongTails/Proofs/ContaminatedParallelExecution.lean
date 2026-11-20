import LongTails.Algorithms.ContaminatedParallelDescent
import LongTails.Proofs.LeonScheduledExecution

namespace LongTails.Proofs.ContaminatedParallelExecution

open DistributedTemplate MeasureTheory
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex (system)
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms
open LeonInstructionCount LeonProgramCost

lemma size_aggregate (p : Params) (i : Fin p.n) (x a : Point p) (l q : ℕ)
    (next : Point p → LeonProtocol.Program (network p)) {k : ℕ} (hk : ∀ v, Size (next v) k) :
    Size (aggregate p i x a l q next) (k + (4 * p.n + 1)) := by
  rw [show k + (4 * (p.n : ℕ) + 1) = ((k + 2 * p.n) + 2 * p.n) + 1 by ring]
  apply Size.sample
  intro values
  apply size_exchange
  intro chunks
  apply size_exchange
  intro blocks
  exact hk _

lemma size_schedule (p : Params) (i : Fin p.n) (ls model) :
    Size (schedule p i ls model) (ls.length * (4 * p.n + 1)) := by
  induction ls generalizing model with
  | nil => simpa [schedule] using (Size.finish (p := network p) (output p model))
  | cons op ls ih =>
    rw [List.length_cons, Nat.succ_mul, schedule]
    apply size_aggregate
    intro v
    exact ih _

variable (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
  (P : ProbabilityMeasure (Samples p)) (limit : Time)

abbrev Run := ExecutionState (system (network p) g P) (algorithm p limit)

def toLeon (c : Run p g P limit) : LeonClock.RunState g P limit (p := network p) :=
  ⟨c.time, c.deadline, c.workers, c.wakeTime, c.turn, c.oracle⟩

lemma step_toLeon (c : Run p g P limit) :
    step (system (network p) g P) (LeonProtocol.algorithm (network p) limit) (toLeon p g P limit c) =
      (step (system (network p) g P) (algorithm p limit) c).map (toLeon p g P limit) := by
  let O := system (network p) g P
  let A := algorithm p limit
  let B := LeonProtocol.algorithm (network p) limit
  change step O B (toLeon p g P limit c) = (step O A c).map _
  have he : event O B (toLeon p g P limit c) = event O A c := rfl
  unfold step
  rw [he]
  simp only [toLeon]
  by_cases hc : c.deadline < c.time
  · simp only [hc, ↓reduceIte, Option.map_none]
  simp only [hc, ↓reduceIte]
  cases hv : event O A c c.time with
  | none =>
    by_cases hd : c.time = c.deadline <;> simp only [hd, ↓reduceIte] <;> rfl
  | some pair =>
    obtain ⟨⟨i, e⟩, o⟩ := pair
    simp only [A, B, algorithm, LeonProtocol.algorithm]
    cases h : LeonProtocol.query (network p) (LeonProtocol.update (network p) (c.workers i) e) with
    | mk action s => cases action <;> rfl

lemma run_toLeon (k : ℕ) (c : Run p g P limit) :
    run (system (network p) g P) (LeonProtocol.algorithm (network p) limit) k (toLeon p g P limit c) =
    toLeon p g P limit (run (system (network p) g P) (algorithm p limit) k c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [run, step_toLeon]
    cases h : step (system (network p) g P) (algorithm p limit) c with
    | none => rfl
    | some d => exact ih d

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Clock

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex (Params system Samples Point)
open LongTails.Algorithms.LeonProtocol (algorithm)
open LeonClock

private lemma terminal_of_balanced {p : LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.Params}
    (g : Fin p.n → LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.Point p →
      p.Ω → LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.Point p)
    (P : ProbabilityMeasure (LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.Samples p))
    (limit : Time) (start : RunState g P limit)
    (hbalance : ∀ i, balanced (start.workers i))
    (htime : start.time ≤ start.deadline) (hdeadline : start.deadline ≤ limit) :
    ∃ k, step (system p g P) (LeonProtocol.algorithm p limit)
      (run (system p g P) (LeonProtocol.algorithm p limit) k start) = none := by
  let O := system p g P
  let A := LeonProtocol.algorithm p limit
  let inv (c : RunState g P limit) := (∀ i, balanced (c.workers i)) ∧ c.time ≤ c.deadline ∧ c.deadline ≤ limit
  apply DistributedExecution.termination_of_rank O A inv (rank g P limit)
  · intro c next hc hs
    obtain ⟨hbal, ht, hb⟩ := hc
    refine ⟨⟨?_, DistributedExecution.step_time_le_deadline O A c next ht hs,
      by simpa only [DistributedExecution.step_deadline O A c next hs] using hb⟩, ?_⟩
    · cases he : event O A c c.time with
      | none =>
        simp only [step, ite_eq_right (not_lt.mpr ht), he] at hs
        split_ifs at hs
        cases hs
        exact hbal
      | some val =>
        rcases val with ⟨⟨i, ev⟩, o⟩
        have hstep := step_event g P limit c i ev o ht he
        have hnext : next = eventStep g P limit c i ev o := Option.some.inj (hs.symm.trans hstep)
        rw [hnext]
        intro j
        by_cases hj : j = i
        · subst j
          simpa [eventStep] using (query_control p _ (update_control p _ ev (hbal i)).1).1
        · simpa [eventStep, Function.update_of_ne hj] using hbal j
    · cases he : event O A c c.time with
      | none =>
        simp only [step, ite_eq_right (not_lt.mpr ht), he] at hs
        split_ifs at hs with hlim
        cases hs
        have hnext := DistributedExecution.nextTime_spec _ _ _ (LeonNetwork.next_exists p g P A c ht)
        have hready := hnext.1.2.2
        have hgood : (event O A {c with time := nextTime (event O A c) c.time c.deadline}
            (nextTime (event O A c) c.time c.deadline)).isSome ∨
              nextTime (event O A c) c.time c.deadline = c.deadline := by
          exact hready.symm
        change 2 * credits g P limit c + (if _ then 0 else 1) <
          2 * credits g P limit c + (if _ then 0 else 1)
        rw [ite_eq_left hgood]
        have hn : ¬((event O A c c.time).isSome ∨ c.time = c.deadline) := by simp [he, hlim]
        rw [ite_eq_right hn]
        omega
      | some val =>
        rcases val with ⟨⟨i, ev⟩, o⟩
        have hnext := Option.some.inj (hs.symm.trans (step_event g P limit c i ev o ht he))
        rw [hnext]
        have hdec := event_credits g P limit c i ev o (hbal i) ht hb he
        unfold rank
        split_ifs <;> omega
  · exact ⟨hbalance, htime, hdeadline⟩

end Clock

lemma finite (ab : (algorithm p limit).Seed) (samples : Samples p) :
    FiniteEvents (system (network p) g P) (algorithm p limit) limit (ab,samples) := by
  intro T hT
  let c := initial (system (network p) g P) (algorithm p limit) T (ab,samples)
  have hb (i) : balanced ((toLeon p g P limit c).workers i) := by
    have h := size_schedule p i (operations p ab) (initialModel p)
    change Size _ (depth (schedule p i _ _))
    rw [depth_eq h]
    exact h
  obtain ⟨k, hk⟩ := terminal_of_balanced (p := network p) g P limit (toLeon p g P limit c) hb zero_le hT
  rw [run_toLeon, step_toLeon, Option.map_eq_none_iff] at hk
  exact ⟨k,hk⟩

open LeonReservations LeonScheduledExecution LeonExecutionInvariant

lemma execute_certified {rows : List (Frame (network p))} {out : Point p} (samples : Samples p)
    (cert : Certified g samples limit rows) (ab : (algorithm p limit).Seed)
    (htr : ∀ i, LeonTranscript.Trace ((algorithm p limit).initial i ab).program
      (rows.map (fun c => c.op i)) out) :
    DistributedTemplate.execute (system (network p) g P) (algorithm p limit) limit ab samples = out := by
  let O := system (network p) g P
  let B := LeonProtocol.algorithm (network p) limit
  let A := algorithm p limit
  let init := initial O A limit (ab,samples)
  let c := toLeon p g P limit init
  let start : Fin p.n → Cursor rows := fun _ => ⟨[],rows,rfl⟩
  have hinit : Valid g P limit samples rows out c start := by
    refine ⟨⟨htr,fun _ => ⟨rfl,rfl,rfl⟩,fun _ _ => LeonLinkLedger.empty⟩,fun _ => zero_le,
      fun _ _ => le_rfl⟩
  obtain ⟨k, hend⟩ := finite p g P limit ab samples limit le_rfl
  rw [DistributedExecution.execute_eq_terminal O A limit (ab,samples) k hend]
  have hrun (j : ℕ) (z : LeonClock.RunState (p := network p) g P limit)
      (hc : z.time ≤ z.deadline) (hd : z.deadline = limit)
      (cur : Fin p.n → Cursor rows) (h : Valid g P limit samples rows out z cur) :
      ∃ cur', Valid g P limit samples rows out (run O B j z) cur' := by
    induction j generalizing z cur with
    | zero => exact ⟨cur,h⟩
    | succ j ih =>
      cases hz : step O B z with
      | none => simpa [run,hz] using (show ∃ cs, Valid g P limit samples rows out z cs from ⟨cur,h⟩)
      | some d =>
        obtain ⟨cs,hcs⟩ := step_valid cert z d hd hc cur h hz
        simpa [run,hz] using ih d (DistributedExecution.step_time_le_deadline O B z d hc hz)
          ((DistributedExecution.step_deadline O B z d hz).trans hd) cs hcs
  obtain ⟨cs,hcs⟩ := hrun k c zero_le rfl start hinit
  have hstop : step O B (run O B k c) = none := by
    change step O B (run O B k (toLeon p g P limit init)) = none
    rw [run_toLeon, step_toLeon]
    exact congrArg (Option.map (toLeon p g P limit)) hend
  have he := terminal_output cert _ (DistributedExecution.run_deadline O B c k)
    (DistributedExecution.run_time_le_deadline O B c k zero_le) cs hcs hstop
  change B.output ((run O B k (toLeon p g P limit init)).workers B.root) = out at he
  rw [run_toLeon] at he
  exact he

end LongTails.Proofs.ContaminatedParallelExecution
