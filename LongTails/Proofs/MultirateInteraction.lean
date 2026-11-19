import LongTails.Proofs.MultirateEvents

open MeasureTheory

namespace LongTails.Proofs.MultirateInteraction

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateProtocol LongTails.Algorithms.MultirateAllocation
open LongTails.Algorithms.MultirateTrajectory
open MultirateReservations MultirateMachine MultirateEvents

variable {p : Params}

inductive Move (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (D u : Time) (x : Config p) : Fin (p.n+1) →
    Event (spec.ComputeReply p) (spec.CommReply p) → OracleState (systemOf g P) → Config p → Prop
  | sleep (v) (hw : x.wakes v ≤ x.now)
      (hs : (algorithm p D).query v (workersOf g s x.table x.program v) 0 =
        (.advance 1,workersOf g s x.table x.program v)) :
      Move g P s D u x v .wake (oracleOf g P s x.table) (tick x v (D+1) x.table x.program)
  | post (i bits next e) (hp : x.program = .post i bits next) (hf : x.table i = .free e)
      (hw : x.wakes 0 ≤ x.now) (hb : bits.length = payload p) :
      Move g P s D u x 0 .wake (oracleOf g P s x.table)
        (tick x 0 x.now (revised x i (.down ⟨e,bits,u⟩ (x.now + packetDelay p))) next)
  | take (i job next) (hp : x.program = .collect i next) (hf : x.table i = .buffered job)
      (hw : x.wakes 0 ≤ x.now) :
      Move g P s D u x 0 .wake (oracleOf g P s x.table)
        (tick x 0 x.now (revised x i (.free (job.number+1))) (next (jobReply g s i job)))
  | evaluate (i job j t) (hc : x.table i = .dispatch job j t) (hw : x.wakes i.succ ≤ x.now)
      (hj : j < batch p i) :
      Move g P s D u x i.succ .wake (oracleOf g P s x.table)
        (tick x i.succ x.now (revised x i (.work job j (x.now + p.h i))) x.program)
  | reply (i job t) (hc : x.table i = .dispatch job (batch p i) t) (hw : x.wakes i.succ ≤ x.now) :
      Move g P s D u x i.succ .wake (oracleOf g P s x.table)
        (tick x i.succ x.now (revised x i (.up job (x.now + packetDelay p))) x.program)
  | down (i job t) (hc : x.table i = .down job t) (ht : t ≤ x.now) :
      Move g P s D u x i.succ (.received (.received 0 (wire job.query))) (cleared g P s x.table 0 i.succ)
        (tick x i.succ x.now (revised x i (.dispatch job 0 t)) x.program)
  | up (i job t) (hc : x.table i = .up job t) (ht : t ≤ x.now) :
      Move g P s D u x 0 (.received (.received i.succ (jobReply g s i job))) (cleared g P s x.table i.succ 0)
        (tick x 0 x.now (revised x i (.buffered job)) x.program)
  | computed (i job j t) (hc : x.table i = .work job j t) (ht : t ≤ x.now) :
      Move g P s D u x i.succ (.computed (.computed (jobInput p job) (g i (jobInput p job) (s i (job.number * batch p i+j)))))
        ({oracleOf g P s x.table with computation := Function.update (oracleOf g P s x.table).computation i.succ ⟨none,s,job.number * batch p i+j+1⟩})
        (tick x i.succ x.now (revised x i (.dispatch job (j+1) t)) x.program)

noncomputable def wakeAfter (D now : Time) : Action (spec.ComputeQuery p) (p.n+1) → Time
  | .advance t => max now ((algorithm p D).timer t)
  | _ => now

noncomputable def submit (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (os : OracleState (systemOf g P)) (v : Fin (p.n+1)) (t : Time) :
    Action (spec.ComputeQuery p) (p.n+1) → OracleState (systemOf g P)
  | .advance _ => os
  | .compute q => {os with computation := Function.update os.computation v ((systemOf g P).computation.submit v (os.computation v) t q)}
  | .communicate (w,bits) => {os with communication := (systemOf g P).communication.submit os.communication t v (w,wire bits)}

variable (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p)) (s : Samples p) (D : Time)

lemma actual_tick {x : Config p} {v : Fin (p.n+1)} {e : Event (spec.ComputeReply p) (spec.CommReply p)}
    {os : OracleState (systemOf g P)} (hnow : x.now ≤ x.deadline)
    (he : event (systemOf g P) (algorithm p D) (image g P s D x) x.now = some ((v,e),os))
    {act : Action (spec.ComputeQuery p) (p.n+1)} {st : State p} {b : Table p} {prog : Program p} {w : Time}
    (hq : (algorithm p D).query v ((algorithm p D).update v (workersOf g s x.table x.program v) 0 e) 0 = (act,st))
    (hws : Function.update (workersOf g s x.table x.program) v st = workersOf g s b prog)
    (ho : submit g P os v x.now act = oracleOf g P s b) (ht : wakeAfter (p := p) D x.now act = w) :
    step (systemOf g P) (algorithm p D) (image g P s D x) = some (image g P s D (tick x v w b prog)) := by
  calc
    _ = some ⟨x.now, x.deadline, Function.update (workersOf g s x.table x.program) v st,
        Function.update x.wakes v (wakeAfter (p := p) D x.now act), v.val+1, submit g P os v x.now act⟩ := by
      simp only [step,show (image g P s D x).time = x.now from rfl,
        show (image g P s D x).deadline = x.deadline from rfl, ite_eq_right (not_lt.mpr hnow), he,
        show (algorithm p D).clock x.now = 0 from rfl,
        show (image g P s D x).workers = workersOf g s x.table x.program from rfl,hq]
      cases act <;> simp only [Function.update_idem] <;> rfl
    _ = _ := by
      cases ht
      unfold image tick
      congr 2

lemma wake_zero (t : Time) : wakeAfter (p := p) D t (.advance 0) = t := by simp [wakeAfter,algorithm]
lemma wake_sleep {t : Time} (ht : t ≤ D) : wakeAfter (p := p) D t (.advance 1) = D+1 := by
  have h : (1 : ClockReading) ≠ 0 := by decide
  simp only [wakeAfter,algorithm,ite_eq_right h,max_eq_right (ht.trans (le_add_of_nonneg_right zero_le))]

end LongTails.Proofs.MultirateInteraction
