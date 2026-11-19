import LongTails.Proofs.LeonRoundTrace
import LongTails.Proofs.LeonTermination

namespace LongTails.Proofs.LeonLinkLedger

open DistributedTemplate

abbrev Packet := Time × List Bool

def Earlier (a b : Packet) : Prop := a.1 ≤ b.1 ∧ a.2 = b.2

structure Ledger (posted consumed : List Packet) (inbox : List (List Bool)) (flight : List Packet) : Prop where
  split : ∃ stored transit : List Packet, posted = consumed ++ stored ++ transit ∧
    stored.map Prod.snd = inbox ∧ List.Forall₂ Earlier flight transit

lemma empty : Ledger [] [] [] [] := ⟨[], [], rfl, rfl, .nil⟩

lemma append {posted consumed flight : List Packet} {inbox : List (List Bool)}
    (h : Ledger posted consumed inbox flight) (a d : Time) (bits : List Bool) (had : a ≤ d) :
    Ledger (posted ++ [(d,bits)]) consumed inbox (flight ++ [(a,bits)]) := by
  obtain ⟨stored, transit, hp, hs, ht⟩ := h.split
  refine ⟨stored, transit ++ [(d,bits)], by simp [hp, List.append_assoc], hs, ?_⟩
  clear hp hs h
  induction ht with
  | nil => exact .cons ⟨had,rfl⟩ .nil
  | cons he _ ih => exact .cons he ih

lemma deliver {posted consumed : List Packet} {inbox : List (List Bool)} {a : Packet} {rest : List Packet}
    (h : Ledger posted consumed inbox (a :: rest)) :
    Ledger posted consumed (inbox ++ [a.2]) rest := by
  obtain ⟨stored, transit, hp, hs, ht⟩ := h.split
  cases ht with
  | cons he tail =>
    rename_i packet remaining
    refine ⟨stored ++ [packet], remaining, ?_, ?_, tail⟩
    · simpa [List.append_assoc] using hp
    · simp [hs, he.2]

lemma pop {posted consumed : List Packet} {b : List Bool} {inbox : List (List Bool)} {flight : List Packet}
    (h : Ledger posted consumed (b :: inbox) flight) :
    ∃ d, (d,b) ∈ posted ∧ Ledger posted (consumed ++ [(d,b)]) inbox flight := by
  obtain ⟨stored, transit, hp, hs, ht⟩ := h.split
  cases stored with
  | nil => simp at hs
  | cons a st =>
    simp only [List.map_cons, List.cons.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨a.1, by simp [hp], st, transit, ?_, rfl, ht⟩
    simpa [List.append_assoc] using hp

lemma available {posted consumed : List Packet} {flight : List Packet} {d : Time} {bits : List Bool}
    (h : Ledger posted consumed [] flight) (rest : List Packet)
    (hp : posted = consumed ++ (d,bits) :: rest) :
    ∃ a ∈ flight.head?, a.1 ≤ d ∧ a.2 = bits := by
  obtain ⟨stored, transit, he, hs, ht⟩ := h.split
  have hnil : stored = [] := by simpa using hs
  subst stored
  simp only [List.append_nil] at he
  have ht' := List.append_cancel_left (he.symm.trans hp)
  subst transit
  cases ht with
  | cons h _ => exact ⟨_, by simp, h⟩

lemma flight_bound {posted consumed flight : List Packet} {inbox : List (List Bool)}
    (h : Ledger posted consumed inbox flight) (d : Time) (hb : ∀ m ∈ posted, m.1 ≤ d) :
    ∀ m ∈ flight, m.1 ≤ d := by
  obtain ⟨stored, transit, hp, hs, ht⟩ := h.split
  have ht' (m) (hm : m ∈ transit) : m.1 ≤ d := hb m (by simp [hp, hm])
  clear hp hs h hb
  induction ht with
  | nil => simp
  | cons h tail ih =>
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hmem
    · exact h.1.trans (ht' _ (by simp))
    · exact ih (fun a ha => ht' a (by simp [ha])) m hmem

end LongTails.Proofs.LeonLinkLedger

namespace LongTails.Proofs.LeonReservations

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonRoundTrace LeonTranscript LeonLinkLedger

structure Frame (p : Params) where
  op : Fin p.n → Op p
  start : Time
  finish : Time
  delivery : Time

def sends (c : Frame p) (i j : Fin p.n) : List Packet :=
  match c.op i with
  | .send k bits => if k = j then [(c.delivery,wire bits)] else []
  | _ => []

def receives (c : Frame p) (i j : Fin p.n) : List Packet :=
  match c.op j with
  | .receive k bits => if k = i then [(c.delivery,bits)] else []
  | _ => []

def used (c : Frame p) (i : Fin p.n) : ℕ :=
  match c.op i with
  | .sample q _ => q.2
  | _ => 0

abbrev posted (xs : List (Frame p)) (i j : Fin p.n) := xs.flatMap (fun c => sends c i j)
abbrev consumed (xs : List (Frame p)) (i j : Fin p.n) := xs.flatMap (fun c => receives c i j)
abbrev usedCount (xs : List (Frame p)) (i : Fin p.n) := (xs.map (fun c => used c i)).sum

def due (limit : Time) (rest : List (Frame p)) (busy : Bool) : Time :=
  match rest with
  | [] => limit
  | c :: _ => if busy then c.finish else c.start

def runnable (s : State p) : Prop :=
  match s.program with
  | .finish _ => False
  | .sample _ _ => s.busy = false
  | .send _ _ _ => True
  | .receive i _ => s.inbox i ≠ []

structure Certified {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (limit : Time) (rows : List (Frame p)) : Prop where
  ordered : ∀ pre c rest, rows = pre ++ c :: rest →
    c.start ≤ c.finish ∧ c.finish ≤ due limit rest false
  bounded : ∀ c ∈ rows, c.finish ≤ limit
  sample : ∀ pre c rest, rows = pre ++ c :: rest → ∀ i q vals, c.op i = .sample q vals →
    c.start + (q.2 : ℕ) * p.h i ≤ c.finish ∧
      vals = (List.range q.2).map (fun j => g i q.1 (s i (usedCount pre i + j)))
  send : ∀ pre c rest, rows = pre ++ c :: rest → ∀ i j bits, c.op i = .send j bits →
    c.start + p.l + p.b * (wire bits).length ≤ c.delivery ∧
      ∀ v ∈ posted pre i j, v.1 ≤ c.start
  receive : ∀ pre c rest, rows = pre ++ c :: rest → ∀ j i bits, c.op j = .receive i bits →
    c.delivery ≤ c.start ∧ consumed pre i j ++ [(c.delivery,bits)] <+: posted pre i j

structure Cursor {p : Params} (rows : List (Frame p)) where
  past : List (Frame p)
  rest : List (Frame p)
  layout : rows = past ++ rest

def Cursor.shift {rows : List (Frame p)} (a : Cursor rows) {c tail} (h : a.rest = c :: tail) :
    Cursor rows := ⟨a.past ++ [c], tail, a.layout.trans (by rw [h, List.append_assoc]; rfl)⟩

lemma before {rows : List (Frame p)} (a b : Cursor rows) (h : a.past.length ≤ b.past.length) :
    a.past <+: b.past := by
  have he (u : Cursor rows) : rows.take u.past.length = u.past := by
    exact (congrArg (List.take u.past.length) u.layout).trans (by simp)
  rw [← he a, ← he b]
  exact List.take_prefix_take_left h

def CompOK (p : Params) (seed : Samples p) (i : Fin p.n) (past rest : List (Frame p))
    (w : State p) (o : ComputeState p) : Prop :=
  o.samples = seed ∧ o.used = usedCount past i ∧
  if w.busy then ∃ c tail q vals t, rest = c :: tail ∧ c.op i = .sample q vals ∧
    o.pending = some (t,q) ∧ t ≤ c.finish
  else o.pending = none

structure Consistent {p : Params} (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) (seed : Samples p) (rows : List (Frame p)) (out : Point p)
    (ws : Fin p.n → State p) (o : OracleState (system p g P)) (cur : Fin p.n → Cursor rows) : Prop where
  trace : ∀ i, Trace (ws i).program ((cur i).rest.map (fun a => a.op i)) out
  compute : ∀ i, CompOK p seed i (cur i).past (cur i).rest (ws i) (o.computation i)
  link : ∀ i j, Ledger (posted (cur i).past i j) (consumed (cur j).past i j)
    ((ws j).inbox i) (o.communication (i,j))

structure Valid {p : Params} (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) (limit : Time) (seed : Samples p)
    (rows : List (Frame p)) (out : Point p) (c : LeonClock.RunState g P limit)
    (cur : Fin p.n → Cursor rows) : Prop extends Consistent g P seed rows out c.workers c.oracle cur where
  time : ∀ i, c.time ≤ due limit (cur i).rest (c.workers i).busy
  wake : ∀ i, runnable (c.workers i) → c.wakeTime i ≤ c.time

end LongTails.Proofs.LeonReservations

namespace LongTails.Proofs.LeonLocalTrace

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonTranscript LeonReservations

lemma done {pr : Program p} {x} (h : Trace pr [] x) : pr = .finish x := by cases h; rfl

lemma sample {pr : Program p} {x q vals ops} (h : Trace pr (.sample q vals :: ops) x) :
    ∃ k, pr = .sample q k ∧ Trace (k vals) ops x := by cases h with | sample hh => exact ⟨_, rfl, hh⟩

lemma send {pr : Program p} {x j bits ops} (h : Trace pr (.send j bits :: ops) x) :
    ∃ next, pr = .send j bits next ∧ Trace next ops x := by cases h with | send hh => exact ⟨_, rfl, hh⟩

lemma receive {pr : Program p} {x j bits ops} (h : Trace pr (.receive j bits :: ops) x) :
    ∃ k, pr = .receive j k ∧ Trace (k bits) ops x := by cases h with | receive hh => exact ⟨_, rfl, hh⟩

lemma nonbusy {rows : List (Frame p)} {a : Cursor rows} {i : Fin p.n} {w : State p} {o : ComputeState p}
    {s : Samples p} (h : CompOK p s i a.past a.rest w o)
    (hn : ∀ c tail q vals, a.rest = c :: tail → c.op i ≠ .sample q vals) : w.busy = false := by
  cases hb : w.busy with
  | false => rfl
  | true =>
    obtain ⟨c, tail, q, vals, _, hc, he, _, _⟩ := (show ∃ c tail q vals t, a.rest = c :: tail ∧
      c.op i = .sample q vals ∧ o.pending = some (t,q) ∧ t ≤ c.finish from by simpa [hb] using h.2.2)
    exact False.elim (hn c tail q vals hc he)

lemma replace {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
    {s : Samples p} {rows : List (Frame p)} {out : Point p} {ws : Fin p.n → State p}
    {o : OracleState (system p g P)} {cur : Fin p.n → Cursor rows}
    (h : Consistent g P s rows out ws o cur) (i : Fin p.n) (w : State p) (a : Cursor rows)
    (o' : OracleState (system p g P))
    (ht : Trace w.program (a.rest.map (fun c => c.op i)) out)
    (hc : CompOK p s i a.past a.rest w (o'.computation i))
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

lemma pos_eq {xs zs : List α} {a b : α}
    (ha : xs ++ [a] <+: zs) (hb : xs ++ [b] <+: zs) : a = b := by
  obtain ⟨as, he⟩ := ha
  obtain ⟨bs, hf⟩ := hb
  have h := he.trans hf.symm
  simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq,
    List.cons.injEq] at h
  exact h.1

lemma head_in_ledger {rows : List (Frame p)} (a b : Cursor rows) (i j : Fin p.n)
    {inbox : List (List Bool)} {flight : List LeonLinkLedger.Packet}
    {bits : List Bool} (h : LeonLinkLedger.Ledger (posted a.past i j) (consumed b.past i j)
      (bits :: inbox) flight) {d : Time} {want : List Bool}
    (hp : consumed b.past i j ++ [(d,want)] <+: posted b.past i j) :
    bits = want ∧ LeonLinkLedger.Ledger (posted a.past i j) (consumed b.past i j ++ [(d,want)]) inbox flight := by
  obtain ⟨t, _, ht⟩ := LeonLinkLedger.pop h
  have he : (t,bits) = (d,want) := by
    apply pos_eq (zs := posted rows i j)
    · obtain ⟨stored, transit, he, _, _⟩ := ht.split
      refine List.IsPrefix.trans ⟨stored ++ transit, by simpa [List.append_assoc] using he.symm⟩ ?_
      exact ⟨posted a.rest i j, by simpa [posted] using (congrArg (fun xs => posted xs i j) a.layout).symm⟩
    · apply hp.trans
      exact ⟨posted b.rest i j, by simpa [posted] using (congrArg (fun xs => posted xs i j) b.layout).symm⟩
  cases he
  exact ⟨rfl, ht⟩

end LongTails.Proofs.LeonLocalTrace
