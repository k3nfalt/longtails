import LongTails.Proofs.MultirateInteraction

open MeasureTheory

namespace LongTails.Proofs.MultirateProgress

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex LongTails.Setups.StarNetwork
open LongTails.Algorithms.MultirateProtocol LongTails.Algorithms.MultirateAllocation
open MultirateReservations MultirateMachine MultirateEvents MultirateInteraction

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
    {s : Samples p} {D u : Time} {x : Config p} {out : Point p} {n : ℕ}

def buffered : Cell p → Prop
  | .buffered _ => True
  | _ => False

def dispatching : Cell p → Prop
  | .dispatch _ _ _ => True
  | _ => False

def rootReady (b : Table p) : Program p → Prop
  | .done _ => False
  | .post _ _ _ => True
  | .collect i _ => buffered (b i)

def Responsive (x : Config p) : Prop :=
  (rootReady x.table x.program → x.wakes 0 ≤ x.now) ∧
    ∀ i, dispatching (x.table i) → x.wakes i.succ ≤ x.now

def Safe (x : Config p) (i : Fin p.n) : Prop :=
  Feasible p i (x.table i) ∧ ∀ t ∈ readyTime (x.table i), x.now ≤ t

structure Valid (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (out : Point p) (D : Time)
    (x : Config p) (n : ℕ) (u : Time) : Prop where
  cert : Certified g s out D n x.program (fun i => booking (x.table i)) u
  time : x.now ≤ x.deadline
  deadline : x.deadline ≤ D
  current : 0 < n → x.now ≤ u
  safe : ∀ i, Safe x i
  responsive : Responsive x

lemma leaf_ready (h : Responsive x) (i : Fin p.n) {t : Time} (ht : readyTime (x.table i) = some t)
    (hs : x.now ≤ t) :
    (event (systemOf g P) (algorithm p D) (image g P s D x) t).isSome := by
  apply (DistributedExecution.event_ready ..).mpr
  cases hc : x.table i with
  | free | buffered => rw [hc] at ht; cases ht
  | dispatch job j a =>
    right
    exact ⟨i.succ,(h.2 i (by rw [hc]; trivial)).trans hs⟩
  | down job a =>
    have he : a = t := by rw [hc] at ht; exact Option.some.inj ht
    subst t
    left
    apply (DistributedExecution.oracle_ready ..).mpr
    right
    apply (DistributedExecution.communication_ready (Seed := Samples p) (network p) _ _).mpr
    exact ⟨0,i.succ,a,wire job.query,by simp [messages,hc,image,oracleOf,downlink],le_rfl⟩
  | up job a =>
    have he : a = t := by rw [hc] at ht; exact Option.some.inj ht
    subst t
    left
    apply (DistributedExecution.oracle_ready ..).mpr
    right
    apply (DistributedExecution.communication_ready (Seed := Samples p) (network p) _ _).mpr
    exact ⟨i.succ,0,a,jobReply g s i job,by simp [messages,hc,image,oracleOf,uplink],le_rfl⟩
  | work job j a =>
    have he : a = t := by rw [hc] at ht; exact Option.some.inj ht
    subst t
    left
    apply (DistributedExecution.oracle_ready ..).mpr
    left
    refine ⟨i.succ,(DistributedExecution.computation_ready (network p) (evalAt g) i _ _).mpr ?_⟩
    exact ⟨a,jobInput p job,by change (computationOf s i (x.table i)).pending = _; rw [hc]; rfl,le_rfl⟩

lemma timely_event (h : Valid g s out D x n u) (hn : 0 < n) :
    ∃ t, x.now ≤ t ∧ t ≤ u ∧ (event (systemOf g P) (algorithm p D) (image g P s D x) t).isSome := by
  have hroot (hr : rootReady x.table x.program) : (event (systemOf g P) (algorithm p D) (image g P s D x) x.now).isSome :=
    (DistributedExecution.event_ready ..).mpr (Or.inr ⟨0,h.responsive.1 hr⟩)
  generalize hprog : x.program = prog at *
  have hc := h.cert
  rw [hprog] at hc
  cases hc with
  | done => omega
  | post => exact ⟨_,le_rfl,h.current hn,hroot trivial⟩
  | @collect _ i next book _ _ job hj hu _ _ =>
    change booking (x.table i) = .pending job at hj
    cases he : x.table i with
    | free => simp [he,booking] at hj
    | buffered a => exact ⟨_,le_rfl,h.current hn,hroot (by simp [rootReady,he,buffered])⟩
    | down a t | up a t | work a j t | dispatch a j t =>
      have ht : readyTime (x.table i) = some t := by rw [he]; rfl
      have hle := (h.safe i).2 t ht
      exact ⟨t,hle,(ready_before hj (h.safe i).1 ht).trans hu,leaf_ready h.responsive i ht hle⟩

lemma choose {v e os} (h : Valid g s out D x n u) (obs : Observed g P s x v e os) :
    ∃ y, Move g P s D u x v e os y := by
  cases obs with
  | up i a t hc ht => exact ⟨_,.up i a t hc ht⟩
  | down i a t hc ht => exact ⟨_,.down i a t hc ht⟩
  | work i a j t hc ht => exact ⟨_,.computed i a j t hc ht⟩
  | wake v hw =>
    revert hw
    refine Fin.cases (motive := fun w => x.wakes w ≤ x.now → ∃ y, Move g P s D u x w .wake (oracleOf g P s x.table) y)
      (fun hw => ?_) (fun i hw => ?_) v
    · generalize hprog : x.program = prog
      have hc := h.cert
      rw [hprog] at hc
      cases hc with
      | done =>
        refine ⟨_,.sleep 0 hw ?_⟩
        change rootQuery p ⟨x.program,inbox g s x.table,.idle,false⟩ = _
        rw [hprog]; rfl
      | @post _ i bits next book _ _ a hf hb _ _ =>
        cases he : x.table i with
        | free e =>
          exact ⟨_,.post i bits next e hprog he hw hb⟩
        | down | work | up | buffered | dispatch => simp [he,booking] at hf
      | @collect _ i next book _ _ a hf _ _ _ =>
        cases he : x.table i with
        | buffered job => exact ⟨_,.take i job next hprog he hw⟩
        | free | up | down | work | dispatch =>
          refine ⟨_,.sleep 0 hw ?_⟩
          change rootQuery p ⟨x.program,inbox g s x.table,.idle,false⟩ = _
          simp [hprog,rootQuery,inbox,he,mailbox,workersOf]
          rfl
    · cases he : x.table i with
      | dispatch job j t =>
        by_cases hj : j < batch p i
        · exact ⟨_,.evaluate i job j t he hw hj⟩
        · have hle := (h.safe i).1
          rw [he] at hle
          have hEq := le_antisymm hle.1 (Nat.le_of_not_gt hj)
          exact ⟨_,.reply i job t (by simpa [hEq] using he) hw⟩
      | free | work | down | up | buffered =>
        refine ⟨_,.sleep i.succ hw ?_⟩
        change workerQuery p i ⟨.done p.x0,fun _ => none,phaseOf g s i (x.table i),false⟩ = _
        simp [workersOf,he,phaseOf,workerQuery]
        rfl

end LongTails.Proofs.MultirateProgress
