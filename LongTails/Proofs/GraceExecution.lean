import LongTails.Proofs.GraceProgramSize

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GraceExecution

open MeasureTheory DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open GraceRouting GraceSgd

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n} (A : Routes p S r)
  (g : Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p)) (limit : Time)

abbrev RunState := ExecutionState (system p g P) (algorithm A limit)

noncomputable abbrev reference := LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.system
  p.base (fun _ => g) P

def referenceOracle (o : OracleState (system p g P)) : OracleState (reference g P) :=
  ⟨o.computation, o.communication⟩

def referenceState (c : RunState A g P limit) : LeonClock.RunState (p := p.base) (fun _ => g) P limit :=
  ⟨c.time, c.deadline, c.workers, c.wakeTime, c.turn, referenceOracle g P c.oracle⟩

private lemma findSome_map {α β γ : Type*} (l : List α) (f : α → Option β) (k : β → γ) :
    (l.findSome? (fun x => (f x).map k)) = (l.findSome? f).map k := by
  induction l with
  | nil => rfl
  | cons i rest ih => cases he : f i <;> simp [he, ih]

lemma reference_answer (o : OracleState (system p g P)) (t : Time) :
    (reference g P).answer (referenceOracle g P o) t =
      ((system p g P).answer o t).map (fun z => (z.1, referenceOracle g P z.2)) := by
  let comp (v : Fin p.n) := ((system p g P).computation.answer v (o.computation v) t).map
    fun (reply,state) => ((v, Event.computed (CommReply := CommReply p) reply),
      { o with computation := Function.update o.computation v state })
  let trans (z : (Fin p.n × Event (ComputeReply p) (CommReply p)) × OracleState (system p g P)) :=
    (z.1, referenceOracle g P z.2)
  have hf : ((List.finRange p.n).findSome? (fun v => ((reference g P).computation.answer v
      ((referenceOracle g P o).computation v) t).map fun (reply,state) =>
        ((v, Event.computed (CommReply := CommReply p) reply),
          { referenceOracle g P o with computation := Function.update o.computation v state }))) =
      ((List.finRange p.n).findSome? comp).map trans := by
    rw [← findSome_map]
    congr 1
    funext v
    cases hv : (system p g P).computation.answer v (o.computation v) t with
    | none => change (Option.map _ ((system p g P).computation.answer v (o.computation v) t)) = _; simp [comp, hv]
    | some q => rcases q with ⟨reply,state⟩; change (Option.map _ ((system p g P).computation.answer v (o.computation v) t)) = _; simp [comp, hv, trans, referenceOracle]
  unfold Oracle.answer
  erw [hf]
  cases he : (List.finRange p.n).findSome? comp with
  | some val => simp [trans]
  | none =>
    simp only [Option.map_none]
    change Option.map _ ((communication p).answer o.communication t) =
      Option.map _ (Option.map _ ((communication p).answer o.communication t))
    cases hm : (communication p).answer o.communication t <;> rfl

lemma reference_event (c : RunState A g P limit) (t : Time) :
    event (reference g P) (LeonProtocol.algorithm p.base limit) (referenceState A g P limit c) t =
      (event (system p g P) (algorithm A limit) c t).map
        (fun z => (z.1, referenceOracle g P z.2)) := by
  unfold event
  dsimp only [referenceState]
  rw [reference_answer]
  cases ha : (system p g P).answer c.oracle t with
  | some z => rfl
  | none =>
    dsimp only [referenceState, Option.map_none]
    cases hw : ((List.finRange p.n).rotate c.turn).find? (fun v => decide (c.wakeTime v ≤ t)) <;> rfl

lemma next_exists (c : RunState A g P limit) (hc : c.time ≤ c.deadline) :
    ∃ t, IsLeast {t | c.time ≤ t ∧ t ≤ c.deadline ∧
      (t = c.deadline ∨ (event (system p g P) (algorithm A limit) c t).isSome)} t := by
  have h := LeonNetwork.next_exists p.base (fun _ => g) P _ (referenceState A g P limit c) hc
  simp only [reference_event, Option.isSome_map] at h
  exact h

noncomputable def after (o : OracleState (system p g P)) (i : Fin p.n) (t : Time)
    (a : Action (ComputeQuery p) p.n) : OracleState (system p g P) :=
  match a with
  | .advance _ => o
  | .compute q =>
    { o with computation := Function.update o.computation i ((system p g P).computation.submit i (o.computation i) t q) }
  | .communicate (j, bits) =>
    { o with communication := (communication p).submit o.communication t i (j,bits ++ List.replicate clockBits false) }

lemma post_work_le (mail : Mail p) (i j : Fin p.n) (t : Time) (bits : List Bool) :
    LeonNetworkWork.queued (p := p.base) ((communication p).submit mail t i (j,bits)) ≤
      LeonNetworkWork.queued mail + 1 := by
  classical
  unfold communication
  dsimp only
  split
  · have hlen (f : Time) : LeonNetworkWork.queued (p := p.base) (Function.update mail (i,j)
        (mail (i,j) ++ [(f,bits)])) = LeonNetworkWork.queued mail + 1 := by
      have hh := LeonNetworkWork.update_sum mail (fun _ msgs => msgs.length) (i,j) (mail (i,j) ++ [(f,bits)])
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add] at hh
      change LeonNetworkWork.queued (p := p.base) (Function.update mail (i,j) (mail (i,j) ++ [(f,bits)])) +
        (mail (i,j)).length = LeonNetworkWork.queued (p := p.base) mail + ((mail (i,j)).length + 1) at hh
      omega
    exact (hlen _).le
  · exact Nat.le_succ _

lemma after_cost (o : OracleState (system p g P)) (i : Fin p.n) (t : Time)
    (a : Action (ComputeQuery p) p.n) :
    LeonClock.oracleCost (p := p.base) (fun _ => g) P (referenceOracle g P (after g P o i t a)) ≤
      LeonClock.oracleCost (p := p.base) (fun _ => g) P (LeonClock.after (p := p.base) (fun _ => g) P (referenceOracle g P o) i t a) := by
  cases a with
  | compute => exact le_rfl
  | advance => exact le_rfl
  | communicate q =>
    rcases q with ⟨j,bits⟩
    unfold LeonClock.oracleCost
    dsimp only [after, LeonClock.after, referenceOracle]
    rw [LeonNetworkWork.post_work]
    gcongr
    apply post_work_le

noncomputable def eventState (c : RunState A g P limit) (i : Fin p.n)
    (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState (system p g P)) : RunState A g P limit :=
  let (act, w) := LeonProtocol.query p.base (LeonProtocol.update p.base (c.workers i) ev)
  { c with workers := Function.update c.workers i w
           turn := i.val + 1
           wakeTime := Function.update c.wakeTime i (LeonClock.wakeAfter limit c.time act)
           oracle := after g P o i c.time act }

lemma step_event (c : RunState A g P limit) (i : Fin p.n) (e : Event (ComputeReply p) (CommReply p))
    (o : OracleState (system p g P)) (ht : c.time ≤ c.deadline)
    (he : event (system p g P) (algorithm A limit) c c.time = some ((i,e),o)) :
    step (system p g P) (algorithm A limit) c = some (eventState A g P limit c i e o) := by
  simp only [step, ite_eq_right (not_lt.mpr ht), he]
  simp only [algorithm]
  cases hq : LeonProtocol.query p.base (LeonProtocol.update p.base (c.workers i) e) with
  | mk a w =>
    cases a <;> simp [eventState, hq, after, LeonClock.wakeAfter, algorithm, Function.update_idem]
    rfl

noncomputable def credits (c : RunState A g P limit) :=
  LeonClock.credits (p := p.base) (fun _ => g) P limit (referenceState A g P limit c)

lemma event_decreases (c : RunState A g P limit) (i : Fin p.n) (e : Event (ComputeReply p) (CommReply p))
    (o : OracleState (system p g P)) (hbal : LeonProgramCost.balanced (c.workers i))
    (ht : c.time ≤ c.deadline) (hl : c.deadline ≤ limit)
    (he : event (system p g P) (algorithm A limit) c c.time = some ((i,e),o)) :
    credits A g P limit (eventState A g P limit c i e o) < credits A g P limit c := by
  let ref := referenceState A g P limit c
  have he' : event (reference g P) (LeonProtocol.algorithm p.base limit) ref ref.time =
      some ((i,e),referenceOracle g P o) := by
    rw [reference_event]
    exact congrArg (Option.map (fun z => (z.1, referenceOracle g P z.2))) he
  refine lt_of_le_of_lt ?_ (LeonClock.event_credits (fun _ => g) P limit ref i e
    (referenceOracle g P o) hbal ht hl he')
  unfold credits LeonClock.credits
  apply Nat.add_le_add_left
  exact after_cost g P o i c.time _

noncomputable def rank (c : RunState A g P limit) :=
  2 * credits A g P limit c +
    if (event (system p g P) (algorithm A limit) c c.time).isSome ∨ c.time = c.deadline then 0 else 1

lemma finite (j : (algorithm A limit).Seed) (s : Samples p) :
    FiniteEvents (system p g P) (algorithm A limit) limit (j,s) := by
  intro T hT
  let O := system p g P
  let alg := algorithm A limit
  let inv (c : RunState A g P limit) :=
    (∀ i, LeonProgramCost.balanced (c.workers i)) ∧ c.time ≤ c.deadline ∧ c.deadline ≤ limit
  apply DistributedExecution.termination_of_rank O alg inv (rank A g P limit)
  · intro c d hv hs
    obtain ⟨hbal, ht, hl⟩ := hv
    have htime := DistributedExecution.step_time_le_deadline O alg c d ht hs
    have hlimit := (DistributedExecution.step_deadline O alg c d hs).le.trans hl
    cases he : event O alg c c.time with
    | none =>
      simp only [step, ite_eq_right (not_lt.mpr ht), he] at hs
      split_ifs at hs with hend
      cases hs
      refine ⟨⟨hbal, htime, hlimit⟩, ?_⟩
      have hn := (DistributedExecution.nextTime_spec _ _ _ (next_exists A g P limit c ht)).1.2.2
      let t := nextTime (event O alg c) c.time c.deadline
      have hr : (event O alg {c with time := t} t).isSome ∨ t = c.deadline := hn.symm
      have hnow : ¬ ((event O alg c c.time).isSome ∨ c.time = c.deadline) := by simp [he, hend]
      change 2 * credits A g P limit c + (if (event O alg {c with time := t} t).isSome ∨ t = c.deadline then 0 else 1) <
        2 * credits A g P limit c + (if (event O alg c c.time).isSome ∨ c.time = c.deadline then 0 else 1)
      simp [hr,hnow]
    | some z =>
      rcases z with ⟨⟨i,ev⟩,o⟩
      have hd := Option.some.inj (hs.symm.trans (step_event A g P limit c i ev o ht he))
      subst d
      refine ⟨⟨?_, htime, hlimit⟩, ?_⟩
      · intro v
        by_cases hv : v = i
        · subst v
          simpa [eventState] using (LeonProgramCost.query_control p.base _
            (LeonProgramCost.update_control p.base _ ev (hbal i)).1).1
        · simpa [eventState, Function.update_of_ne hv] using hbal v
      · have hdec := event_decreases A g P limit c i ev o (hbal i) ht hl he
        unfold rank
        split_ifs <;> omega
  · refine ⟨?_, zero_le, hT⟩
    intro i
    have h := GraceProgramSize.program_size A i j.val p.x₀
    change LeonInstructionCount.Size (program A i j.val p.x₀) (LeonInstructionCount.depth (program A i j.val p.x₀))
    rw [LeonInstructionCount.depth_eq h]
    exact h

end LongTails.Proofs.GraceExecution
