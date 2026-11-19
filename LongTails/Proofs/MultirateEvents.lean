import LongTails.Proofs.MultirateMachineProjection

open MeasureTheory

namespace LongTails.Proofs.MultirateEvents

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex LongTails.Setups.StarNetwork
open LongTails.Algorithms.MultirateProtocol LongTails.Algorithms.MultirateAllocation
open MultirateReservations MultirateMachine

variable {p : Params}

structure Config (p : Params) where
  now : Time
  deadline : Time
  table : Table p
  program : Program p
  wakes : Fin (p.n+1) → Time
  turn : ℕ

noncomputable def image (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (D : Time) (x : Config p) : ExecutionState (systemOf g P) (algorithm p D) :=
  ⟨x.now,x.deadline,workersOf g s x.table x.program,x.wakes,x.turn,oracleOf g P s x.table⟩

def tick (x : Config p) (i : Fin (p.n+1)) (wake : Time) (table : Table p) (program : Program p) : Config p :=
  {x with table, program, wakes := Function.update x.wakes i wake, turn := i.val+1}

def revised (x : Config p) (i : Fin p.n) (v : Cell p) :=
  Function.update x.table i v

noncomputable def cleared (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (b : Table p) (src dst : Fin (p.n+1)) : OracleState (systemOf g P) :=
  {oracleOf g P s b with communication := ⟨Function.update (messages g s b) src
    (Function.update (messages g s b src) dst none)⟩}

inductive Observed (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (x : Config p) : Fin (p.n+1) →
    Event (spec.ComputeReply p) (spec.CommReply p) → OracleState (systemOf g P) → Prop
  | wake (i) (h : x.wakes i ≤ x.now) : Observed g P s x i .wake (oracleOf g P s x.table)
  | down (i job t) (h : x.table i = .down job t) (ht : t ≤ x.now) :
      Observed g P s x i.succ (.received (.received 0 (wire job.query))) (cleared g P s x.table 0 i.succ)
  | up (i job t) (h : x.table i = .up job t) (ht : t ≤ x.now) :
      Observed g P s x 0 (.received (.received i.succ (jobReply g s i job))) (cleared g P s x.table i.succ 0)
  | work (i job j t) (h : x.table i = .work job j t) (ht : t ≤ x.now) :
      Observed g P s x i.succ (.computed (.computed (jobInput p job)
        (g i (jobInput p job) (s i (job.number * batch p i+j)))))
        ({oracleOf g P s x.table with computation := Function.update (oracleOf g P s x.table).computation i.succ ⟨none,s,job.number * batch p i+j+1⟩})

variable (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p)) (s : Samples p) (D : Time)

lemma observed (x : Config p) (v : Fin (p.n+1)) (e : Event (spec.ComputeReply p) (spec.CommReply p))
    (os : OracleState (systemOf g P))
    (h : event (systemOf g P) (algorithm p D) (image g P s D x) x.now = some ((v,e),os)) :
    Observed g P s x v e os := by
  let O := systemOf g P
  let A := algorithm p D
  let c := image g P s D x
  cases e with
  | wake =>
    obtain ⟨rfl,ht⟩ := DistributedExecution.wake_event O A c x.now v os h
    exact .wake _ ht
  | computed reply =>
    obtain ⟨cs,ha,rfl⟩ := DistributedExecution.computed_event O A c x.now v reply os h
    cases reply with
    | computed input value =>
      refine Fin.cases (motive := fun w => O.computation.answer w (c.oracle.computation w) x.now =
        some (.computed input value,cs) → Observed g P s x w _ {c.oracle with computation := Function.update c.oracle.computation w cs})
        (fun hn => by cases hn) (fun i hi => ?_) v ha
      obtain ⟨t,hp,ht,hv,hs⟩ := DistributedExecution.computation_completed_data (network p) (evalAt g) i
        (computationOf s i (x.table i)) cs x.now input value hi
      cases he : x.table i with
      | work job j u =>
        simp only [he,computationOf,Option.some.injEq,Prod.mk.injEq] at hp
        obtain ⟨rfl,rfl⟩ := hp
        rw [he] at hv hs
        subst value cs
        exact .work _ _ _ _ he ht
      | free | down | up | buffered | dispatch => simp [he,computationOf] at hp
  | received reply =>
    obtain ⟨cs,ha,rfl⟩ := DistributedExecution.received_event O A c x.now v reply os h
    cases reply with
    | received src bits =>
      obtain ⟨t,hp,ht,hs⟩ := DistributedExecution.communication_received_data (Seed := Samples p)
        (network p) ⟨messages g s x.table⟩ cs x.now src v bits ha
      subst cs
      change messages g s x.table src v = some (t,bits) at hp
      change Observed g P s x v (.received (.received src bits)) (cleared g P s x.table src v)
      revert hp
      refine Fin.cases (motive := fun a => ∀ v, messages g s x.table a v = some (t,bits) →
        Observed g P s x v (.received (.received a bits)) (cleared g P s x.table a v))
        (fun v => ?_) (fun i v => ?_) src v
      · refine Fin.cases (motive := fun w => messages g s x.table 0 w = some (t,bits) →
          Observed g P s x w (.received (.received 0 bits)) (cleared g P s x.table 0 w))
          (fun hn => by cases hn) (fun i hp => ?_) v
        change downlink (x.table i) = some (t,bits) at hp
        cases he : x.table i with
        | down job u =>
          simp only [he,downlink,Option.some.injEq,Prod.mk.injEq] at hp
          obtain ⟨rfl,rfl⟩ := hp
          exact .down _ _ _ he ht
        | free | work | up | buffered | dispatch => simp [he,downlink] at hp
      · refine Fin.cases (motive := fun w => messages g s x.table i.succ w = some (t,bits) →
          Observed g P s x w (.received (.received i.succ bits)) (cleared g P s x.table i.succ w))
          (fun hp => ?_) (fun _ hn => by cases hn) v
        change uplink g s i (x.table i) = some (t,bits) at hp
        cases he : x.table i with
        | up job u =>
          simp only [he,uplink,Option.some.injEq,Prod.mk.injEq] at hp
          obtain ⟨rfl,rfl⟩ := hp
          exact .up _ _ _ he ht
        | free | work | down | buffered | dispatch => simp [he,uplink] at hp

end LongTails.Proofs.MultirateEvents
