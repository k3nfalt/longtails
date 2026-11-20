import LongTails.Proofs.GraceExecution
import LongTails.Proofs.LeonScheduledExecution

namespace LongTails.Proofs.GraceReservations

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonReservations (Frame posted consumed due usedCount runnable Cursor CompOK)
open LeonTranscript (Trace wire)
open LongTails.Algorithms.GraceRouting (Routes)

noncomputable def duration (p : Params) (i j : Fin p.n) (bits : List Bool) : Time :=
  if i = j then 0 else (wire bits).length / p.b i j

structure Certified {p : Params} (g : Point p → p.Ω → Point p) (s : Samples p)
    (limit : Time) (rows : List (Frame p.base)) : Prop where
  ordered : ∀ pre c rest, rows = pre ++ c :: rest →
    c.start ≤ c.finish ∧ c.finish ≤ due limit rest false
  bounded : ∀ c ∈ rows, c.finish ≤ limit
  sample : ∀ pre c rest, rows = pre ++ c :: rest → ∀ i q vals, c.op i = .sample q vals →
    c.start + (q.2 : ℕ) * p.h i ≤ c.finish ∧
      vals = (List.range q.2).map (fun j => g q.1 (s i (usedCount pre i + j)))
  send : ∀ pre c rest, rows = pre ++ c :: rest → ∀ i j bits, c.op i = .send j bits →
    (i = j ∨ p.G.Adj i j) ∧ c.start + duration p i j bits ≤ c.delivery ∧
      ∀ v ∈ posted pre i j, v.1 + duration p i j bits ≤ c.delivery
  receive : ∀ pre c rest, rows = pre ++ c :: rest → ∀ j i bits, c.op j = .receive i bits →
    c.delivery ≤ c.start ∧ consumed pre i j ++ [(c.delivery,bits)] <+: posted pre i j

structure Consistent {p : Params} (g : Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) (s : Samples p) (rows : List (Frame p.base))
    (out : Fin p.n → Point p) (ws : Fin p.n → State p.base) (o : OracleState (system p g P))
    (cur : Fin p.n → Cursor rows) : Prop where
  trace : ∀ i, Trace (ws i).program ((cur i).rest.map fun c => c.op i) (out i)
  compute : ∀ i, CompOK p.base s i (cur i).past (cur i).rest (ws i) (o.computation i)
  link : ∀ i j, LeonLinkLedger.Ledger (posted (cur i).past i j) (consumed (cur j).past i j)
    ((ws j).inbox i) (o.communication (i,j))

structure Valid {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n}
    (A : Routes p S r) (g : Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (limit horizon : Time) (s : Samples p) (rows : List (Frame p.base)) (out : Fin p.n → Point p)
    (c : GraceExecution.RunState A g P limit) (cur : Fin p.n → Cursor rows) : Prop
    extends Consistent g P s rows out c.workers c.oracle cur where
  time : ∀ i, c.time ≤ due horizon (cur i).rest (c.workers i).busy
  wake : ∀ i, runnable (c.workers i) → c.wakeTime i ≤ c.time

variable {p : Params} {g : Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
  {s : Samples p} {rows : List (Frame p.base)} {out : Fin p.n → Point p}
  {ws : Fin p.n → State p.base} {o : OracleState (system p g P)} {cur : Fin p.n → Cursor rows}

lemma replace (h : Consistent g P s rows out ws o cur) (i : Fin p.n) (w : State p.base)
    (a : Cursor rows) (o' : OracleState (system p g P))
    (ht : Trace w.program (a.rest.map (fun c => c.op i)) (out i))
    (hc : CompOK p.base s i a.past a.rest w (o'.computation i))
    (ho : ∀ j, j ≠ i → o'.computation j = o.computation j)
    (hl : ∀ k j, LeonLinkLedger.Ledger (posted ((Function.update cur i a) k).past k j)
      (consumed ((Function.update cur i a) j).past k j) (((Function.update ws i w) j).inbox k)
      (o'.communication (k,j))) :
    Consistent g P s rows out (Function.update ws i w) o' (Function.update cur i a) := by
  refine ⟨fun j => ?_, fun j => ?_, hl⟩
  · by_cases hj : j = i
    · subst j; simpa using ht
    · simpa [Function.update_of_ne hj] using h.trace j
  · by_cases hj : j = i
    · subst j; simpa using hc
    · simpa only [Function.update_of_ne hj, ho j hj] using h.compute j

lemma arrival_bound (h : Consistent g P s rows out ws o cur) (i j : Fin p.n) (t start d : Time)
    (bits : List Bool) (ht : t ≤ start) (hs : start + duration p i j bits ≤ d)
    (hp : ∀ v ∈ posted (cur i).past i j, v.1 + duration p i j bits ≤ d) :
    max t (((o.communication (i,j)).getLast?.map Prod.fst).getD 0) + duration p i j bits ≤ d := by
  rw [← max_add_add_right]
  refine max_le ((add_le_add_left ht _).trans hs) ?_
  cases hlast : (o.communication (i,j)).getLast? with
  | none => exact (add_le_add_left (zero_le : (0 : Time) ≤ start) _).trans hs
  | some msg =>
    have hflight := LeonLinkLedger.flight_bound (h.link i j) (d - duration p i j bits)
      (fun v hv => le_tsub_of_add_le_right (hp v hv)) msg (List.mem_of_getLast? hlast)
    exact (add_le_add_left hflight (duration p i j bits)).trans_eq
      (tsub_add_cancel_of_le ((le_add_self).trans hs))

end LongTails.Proofs.GraceReservations
