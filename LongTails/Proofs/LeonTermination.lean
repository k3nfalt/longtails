import LongTails.Algorithms.LeonProtocol
import LongTails.Proofs.LeonNetwork

namespace LongTails.Proofs.LeonInstructionCount

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol

inductive Size {p : Params} : Program p → ℕ → Prop
  | finish (x) : Size (.finish x) 0
  | sample {q next k} (h : ∀ values, Size (next values) k) : Size (.sample q next) (k + 1)
  | send {i bits next k} (h : Size next k) : Size (.send i bits next) (k + 1)
  | receive {i next k} (h : ∀ bits, Size (next bits) k) : Size (.receive i next) (k + 1)

def depth {p : Params} : Program p → ℕ
  | .finish _ => 0
  | .sample _ next => depth (next []) + 1
  | .send _ _ next => depth next + 1
  | .receive _ next => depth (next []) + 1

lemma depth_eq {p : Params} {q : Program p} {k : ℕ} (h : Size q k) : depth q = k := by
  induction h with
  | finish => rfl
  | sample _ ih => simp [depth, ih]
  | send _ ih => simp [depth, ih]
  | receive _ ih => simp [depth, ih]

lemma size_post {p : Params} (packets : Fin p.n → List Bool) {next : Program p} {k : ℕ}
    (h : Size next k) (workers : List (Fin p.n)) :
    Size (post packets next workers) (k + workers.length) := by
  induction workers with
  | nil => simpa [post] using h
  | cons i workers ih => simpa [post, Nat.add_assoc] using Size.send (i := i) (bits := packets i) ih

lemma size_collect {p : Params} {next : (Fin p.n → List Bool) → Program p} {k : ℕ}
    (h : ∀ data, Size (next data) k) (workers : List (Fin p.n)) (data) :
    Size (collect next workers data) (k + workers.length) := by
  induction workers generalizing data with
  | nil => simpa [collect] using h data
  | cons i workers ih =>
    simpa [collect, Nat.add_assoc] using Size.receive (i := i)
      (fun bits => ih (Function.update data i bits))

lemma size_exchange {p : Params} (packets : Fin p.n → List Bool)
    {next : (Fin p.n → List Bool) → Program p} {k : ℕ} (h : ∀ data, Size (next data) k) :
    Size (exchange packets next) (k + 2 * p.n) := by
  simpa [exchange, two_mul, Nat.add_assoc] using
    size_post packets (size_collect h (List.finRange p.n) (fun _ => [])) (List.finRange p.n)

lemma size_schedule (p : Params) (i : Fin p.n) (a b : ℕ) (ls : List ℕ)
    (model : LongTails.Algorithms.LeonTrajectory.Model p) :
    Size (schedule p i a b ls model) (ls.length * (4 * p.n + 1)) := by
  induction ls generalizing model with
  | nil => simpa [schedule] using Size.finish (LongTails.Algorithms.LeonTrajectory.output p model a b)
  | cons l rest ih =>
    simp only [schedule, List.length_cons]
    rw [show (rest.length + 1) * (4 * (p.n : ℕ) + 1) =
      ((rest.length * (4 * p.n + 1) + 2 * p.n) + 2 * p.n) + 1 by ring]
    apply Size.sample
    intro values
    apply size_exchange
    intro chunks
    apply size_exchange
    intro blocks
    exact ih _

end LongTails.Proofs.LeonInstructionCount

namespace LongTails.Proofs.LeonProgramCost

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonInstructionCount

def balanced {p : Params} (s : State p) : Prop := Size s.program (depth s.program)

def remaining {p : Params} (s : State p) : ℕ :=
  8 * depth s.program + if s.busy then 0 else 3

def charge {Q : Type} {n : ℕ} : Action Q n → ℕ
  | .communicate _ => 4
  | .compute _ => 3
  | .advance t => if t = 0 then 2 else 0

lemma update_control (p : Params) (s : State p) (e : Event (ComputeReply p) (CommReply p))
    (h : balanced s) : balanced (update p s e) ∧ remaining (update p s e) ≤ remaining s := by
  rcases s with ⟨prog, mail, busy⟩
  cases e with
  | wake => exact ⟨h, le_rfl⟩
  | received msg => exact ⟨h, le_rfl⟩
  | computed values =>
    change Size prog (depth prog) at h
    cases prog with
    | finish x => exact ⟨h, le_rfl⟩
    | send i bits next => exact ⟨h, le_rfl⟩
    | receive i next => exact ⟨h, le_rfl⟩
    | sample q next =>
      have hnext : ∀ vs, Size (next vs) (depth (next [])) := by
        cases h with | sample hh => exact hh
      have he := depth_eq (hnext values)
      constructor
      · change Size (next values) (depth (next values))
        rw [he]
        exact hnext values
      · cases busy <;> simp [update, remaining, depth, he]
        omega

lemma query_control (p : Params) (s : State p) (h : balanced s) :
    balanced (query p s).2 ∧ remaining (query p s).2 + charge (query p s).1 ≤ remaining s := by
  rcases s with ⟨prog, mail, busy⟩
  change Size prog (depth prog) at h
  cases prog with
  | finish x =>
    exact ⟨h, by cases busy <;> simp [query, remaining, charge, clockBits]⟩
  | sample q next =>
    cases busy <;> simp [query, balanced, remaining, charge, clockBits, h]
  | send i bits next =>
    have hn : Size next (depth next) := by cases h with | send hh => exact hh
    exact ⟨hn, by cases busy <;> simp [query, remaining, charge, depth] <;> omega⟩
  | receive i next =>
    have hn : ∀ bs, Size (next bs) (depth (next [])) := by cases h with | receive hh => exact hh
    cases hm : mail i with
    | nil => exact ⟨by simpa [query, hm, balanced] using h, by simp [query, hm, remaining, charge, clockBits]⟩
    | cons bits rest =>
      have he := depth_eq (hn bits)
      exact ⟨by simpa [query, hm, balanced, he] using hn bits,
        by simp [query, hm, remaining, charge, depth, he]; omega⟩

end LongTails.Proofs.LeonProgramCost

namespace LongTails.Proofs.LeonClock

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonProgramCost LeonNetworkWork LeonInstructionCount

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
  (limit : Time)

abbrev RunState := ExecutionState (system p g P) (algorithm p limit)

noncomputable def oracleCost (o : OracleState (system p g P)) : ℕ :=
  2 * (queued o.communication + pending o.computation)

noncomputable def workerCost (T : Time) (states : Fin p.n → State p)
    (wake : Fin p.n → Time) : ℕ :=
  ∑ i, (remaining (states i) + if wake i ≤ T then 1 else 0)

noncomputable def credits (c : RunState g P limit) : ℕ :=
  workerCost c.deadline c.workers c.wakeTime + oracleCost g P c.oracle

noncomputable def rank (c : RunState g P limit) : ℕ :=
  2 * credits g P limit c +
    if (event (system p g P) (algorithm p limit) c c.time).isSome ∨ c.time = c.deadline then 0 else 1

lemma oracle_event_cost (c : RunState g P limit) (i : Fin p.n) (e : Event (ComputeReply p) (CommReply p))
    (o : OracleState (system p g P)) (he : event (system p g P) (algorithm p limit)
      c c.time = some ((i, e), o)) :
    (e = .wake ∧ o = c.oracle ∧ c.wakeTime i ≤ c.time) ∨ oracleCost g P o + 2 ≤ oracleCost g P c.oracle := by
  obtain ho | hw := DistributedExecution.event_cases _ _ _ _ _ _ _ he
  · right
    rcases DistributedExecution.oracle_answer_cases _ _ _ _ _ _ ho with
      ⟨reply, state, _, ha, rfl⟩ | ⟨⟨sender, bits⟩, state, _, ha, rfl⟩
    · have h := answer_work p g c.oracle.computation state i c.time reply ha
      unfold oracleCost
      dsimp only
      rw [← h]
      omega
    · have h := deliver_work p c.oracle.communication state c.time sender i bits ha
      unfold oracleCost
      dsimp only
      omega
  · exact Or.inl hw

noncomputable def after (o : OracleState (system p g P)) (i : Fin p.n) (time : Time)
    (a : Action (ComputeQuery p) p.n) : OracleState (system p g P) :=
  match a with
  | .advance _ => o
  | .compute q =>
    { o with computation := Function.update o.computation i ((computation p g).submit i (o.computation i) time q) }
  | .communicate (j, bits) =>
    { o with communication := (communication p).submit o.communication time i (j, bits ++ List.replicate clockBits false) }

lemma submit_cost (o : OracleState (system p g P)) (i : Fin p.n) (t : Time)
    (a : Action (ComputeQuery p) p.n) :
    oracleCost g P (after g P o i t a) +
      (match a with | .advance _ => 0 | _ => 1) ≤ oracleCost g P o + charge a := by
  cases a with
  | advance r => simp [after, charge]
  | compute q =>
    have h := compute_work p g o.computation i t q
    unfold oracleCost
    simp only [after, charge]
    omega
  | communicate q =>
    rcases q with ⟨j, bits⟩
    simp [oracleCost, after, charge, post_work]
    omega

def wakeAfter (limit time : Time) (a : Action (ComputeQuery p) p.n) : Time :=
  match a with
  | .advance k => max time (if k = 0 then 0 else limit + 1)
  | _ => time

noncomputable def eventStep (c : RunState g P limit) (i : Fin p.n) (ev : Event (ComputeReply p) (CommReply p))
    (o : OracleState (system p g P)) : RunState g P limit :=
  let (a, s) := query p (update p (c.workers i) ev)
  { c with workers := Function.update c.workers i s
           turn := i.val + 1
           wakeTime := Function.update c.wakeTime i (wakeAfter limit c.time a)
           oracle := after g P o i c.time a }

lemma step_event (c : RunState g P limit) (i : Fin p.n) (ev : Event (ComputeReply p) (CommReply p))
    (o : OracleState (system p g P)) (ht : c.time ≤ c.deadline)
    (he : event (system p g P) (algorithm p limit) c c.time = some ((i, ev), o)) :
    step (system p g P) (algorithm p limit) c = some (eventStep g P limit c i ev o) := by
  simp only [step, ite_eq_right (not_lt.mpr ht), he]
  simp only [algorithm]
  cases hq : query p (update p (c.workers i) ev) with
  | mk a s =>
    cases a <;> simp [eventStep, hq, after, wakeAfter, algorithm, Function.update_idem] <;> rfl

lemma worker_update_cost (T : Time) (ws : Fin p.n → State p) (w : Fin p.n → Time)
    (i : Fin p.n) (s : State p) (t : Time) :
    workerCost T (Function.update ws i s) (Function.update w i t) +
        (remaining (ws i) + if w i ≤ T then 1 else 0) =
      workerCost T ws w + (remaining s + if t ≤ T then 1 else 0) := by
  classical
  let f := fun i => (ws i, w i)
  have h := update_sum f (fun _ st => remaining st.1 + if st.2 ≤ T then 1 else 0) i (s, t)
  have hf (j) : Function.update f i (s,t) j = (Function.update ws i s j, Function.update w i t j) := by
    by_cases hj : j = i <;> simp [f, hj, Function.update_of_ne]
  simpa only [hf, f, workerCost] using h

lemma event_credits (c : RunState g P limit) (i : Fin p.n) (ev : Event (ComputeReply p) (CommReply p))
    (o : OracleState (system p g P)) (hb : balanced (c.workers i))
    (ht : c.time ≤ c.deadline) (hT : c.deadline ≤ limit)
    (he : event (system p g P) (algorithm p limit) c c.time = some ((i, ev), o)) :
    credits g P limit (eventStep g P limit c i ev o) < credits g P limit c := by
  obtain ⟨hu, hrem⟩ := update_control p (c.workers i) ev hb
  have hq := (query_control p _ hu).2
  have hsrc := oracle_event_cost g P limit c i ev o he
  cases hqs : query p (update p (c.workers i) ev) with
  | mk a s =>
    simp only [hqs] at hq
    have ho := submit_cost g P o i c.time a
    have hw := worker_update_cost c.deadline c.workers c.wakeTime i s (wakeAfter limit c.time a)
    simp only [credits, eventStep, hqs]
    rcases hsrc with ⟨_, rfl, hready⟩ | hchg
    · rw [ite_eq_left (hready.trans ht)] at hw
      cases a with
      | compute q => simp only [wakeAfter, ite_eq_left ht] at hw ⊢; dsimp only at ho; omega
      | communicate q => simp only [wakeAfter, ite_eq_left ht] at hw ⊢; dsimp only at ho; omega
      | advance k =>
        by_cases hk : k = 0
        · simp [wakeAfter, charge, hk, ht, after] at hw hq ho ⊢; omega
        · have hfar : ¬max c.time (limit + 1) ≤ c.deadline := by
            exact not_le.mpr (lt_of_le_of_lt hT ((lt_add_of_pos_right _ zero_lt_one).trans_le (le_max_right _ _)))
          simp [wakeAfter, charge, hk, hfar, after] at hw hq ho ⊢; omega
    · have hnew : (if wakeAfter limit c.time a ≤ c.deadline then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
      cases a <;> dsimp only at ho <;> split_ifs at hw hnew <;> omega

end LongTails.Proofs.LeonClock

namespace LongTails.Proofs.LeonTermination

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonProgramCost LeonInstructionCount LeonClock

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
  (limit : Time)

lemma finite (ab : (algorithm p limit).Seed) (samples : Samples p) :
    FiniteEvents (system p g P) (algorithm p limit) limit (ab, samples) := by
  intro T hT
  let O := system p g P
  let A := algorithm p limit
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
  · refine ⟨?_, zero_le, hT⟩
    intro i
    have hh := size_schedule p i ab.1 ab.2
      (LongTails.Algorithms.LeonCalendar.levels (LongTails.Algorithms.LeonTuning.height p))
      (LongTails.Algorithms.LeonTrajectory.initial p)
    change Size (schedule p i ab.1 ab.2 _ _) (depth (schedule p i ab.1 ab.2 _ _))
    rw [depth_eq hh]
    exact hh

end LongTails.Proofs.LeonTermination
