import LongTails.Proofs.LeonScheduledExecution

namespace LongTails.Proofs.LocalReservations

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonReservations (Frame Cursor due runnable posted consumed usedCount CompOK)
open LeonTranscript LeonLinkLedger

structure Certified {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (limit : Time) (rows : Fin p.n → List (Frame p)) : Prop where
  ordered : ∀ i pre c rest, rows i = pre ++ c :: rest →
    c.start ≤ c.finish ∧ c.finish ≤ due limit rest false
  bounded : ∀ i, ∀ c ∈ rows i, c.finish ≤ limit
  sample : ∀ i pre c rest, rows i = pre ++ c :: rest → ∀ q vals, c.op i = .sample q vals →
    c.start + (q.2 : ℕ) * p.h i ≤ c.finish ∧
      vals = (List.range q.2).map (fun j => g i q.1 (s i (usedCount pre i + j)))
  send : ∀ i pre c rest, rows i = pre ++ c :: rest → ∀ j bits, c.op i = .send j bits →
    c.start + p.l + p.b * (wire bits).length ≤ c.delivery ∧
      ∀ v ∈ posted pre i j, v.1 ≤ c.start
  receive : ∀ i pre c rest, rows i = pre ++ c :: rest → ∀ j bits, c.op i = .receive j bits →
    c.delivery ≤ c.start ∧ ∃ before send after, rows j = before ++ send :: after ∧
      send.finish < c.start ∧ consumed pre j i ++ [(c.delivery,bits)] <+: posted (before ++ [send]) j i

structure Consistent {p : Params} (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) (seed : Samples p) (rows : Fin p.n → List (Frame p)) (out : Point p)
    (ws : Fin p.n → State p) (o : OracleState (system p g P)) (cur : (i : Fin p.n) → Cursor (rows i)) : Prop where
  trace : ∀ i, Trace (ws i).program ((cur i).rest.map (fun a => a.op i)) out
  compute : ∀ i, CompOK p seed i (cur i).past (cur i).rest (ws i) (o.computation i)
  link : ∀ i j, Ledger (posted (cur i).past i j) (consumed (cur j).past i j)
    ((ws j).inbox i) (o.communication (i,j))

structure Valid {p : Params} (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) (limit : Time) (seed : Samples p)
    (rows : Fin p.n → List (Frame p)) (out : Point p) (c : LeonClock.RunState g P limit)
    (cur : (i : Fin p.n) → Cursor (rows i)) : Prop extends Consistent g P seed rows out c.workers c.oracle cur where
  time : ∀ i, c.time ≤ due limit (cur i).rest (c.workers i).busy
  wake : ∀ i, runnable (c.workers i) → c.wakeTime i ≤ c.time

lemma replace {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
    {s : Samples p} {rows : Fin p.n → List (Frame p)} {out : Point p} {ws : Fin p.n → State p}
    {o : OracleState (system p g P)} {cur : (i : Fin p.n) → Cursor (rows i)}
    (h : Consistent g P s rows out ws o cur) (i : Fin p.n) (w : State p) (a : Cursor (rows i))
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

lemma head_in_ledger {rows recv : List (Frame p)} (a : Cursor rows) (b : Cursor recv) (i j : Fin p.n)
    {inbox : List (List Bool)} {flight : List Packet} {bits : List Bool}
    (h : Ledger (posted a.past i j) (consumed b.past i j) (bits :: inbox) flight)
    {d : Time} {want : List Bool} (hp : consumed b.past i j ++ [(d,want)] <+: posted rows i j) :
    bits = want ∧ Ledger (posted a.past i j) (consumed b.past i j ++ [(d,want)]) inbox flight := by
  obtain ⟨t, _, ht⟩ := LeonLinkLedger.pop h
  have he : (t,bits) = (d,want) := by
    apply LeonLocalTrace.pos_eq (zs := posted rows i j) _ hp
    obtain ⟨stored, transit, he, _, _⟩ := ht.split
    refine List.IsPrefix.trans ⟨stored ++ transit, by simpa [List.append_assoc] using he.symm⟩ ?_
    exact ⟨posted a.rest i j, by simpa [posted] using (congrArg (fun xs => posted xs i j) a.layout).symm⟩
  cases he
  exact ⟨rfl,ht⟩

lemma posted_prefix {pre all : List (Frame p)} (h : pre <+: all) (i j : Fin p.n) :
    posted pre i j <+: posted all i j := by
  obtain ⟨suffix,rfl⟩ := h
  exact ⟨posted suffix i j, List.flatMap_append.symm⟩

structure Suitable (all : Fin p.n → List (Frame p)) (i : Fin p.n) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (pre : List (Frame p)) (c : Frame p) : Prop where
  order : c.start ≤ c.finish
  sample : ∀ q vals, c.op i = .sample q vals →
    c.start + (q.2 : ℕ) * p.h i ≤ c.finish ∧
      vals = (List.range q.2).map (fun j => g i q.1 (s i (usedCount pre i + j)))
  send : ∀ j bits, c.op i = .send j bits →
    c.start + p.l + p.b * (wire bits).length ≤ c.delivery ∧ ∀ m ∈ posted pre i j, m.1 ≤ c.start
  receive : ∀ j bits, c.op i = .receive j bits →
    c.delivery ≤ c.start ∧ ∃ before send after, all j = before ++ send :: after ∧
      send.finish < c.start ∧ consumed pre j i ++ [(c.delivery,bits)] <+: posted (before ++ [send]) j i

inductive Checked (all : Fin p.n → List (Frame p)) (i : Fin p.n) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) : List (Frame p) → Time → Prop
  | nil (T) : Checked all i g s [] T
  | snoc {pre c T} (prior : Checked all i g s pre c.start) (ok : Suitable all i g s pre c)
      (finish : c.finish ≤ T) : Checked all i g s (pre ++ [c]) T

variable {all : Fin p.n → List (Frame p)} {i : Fin p.n}

lemma Checked.later {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p} {rows t u}
    (h : Checked all i g s rows t) (ht : t ≤ u) : Checked all i g s rows u := by
  cases h with
  | nil => exact .nil _
  | snoc prior ok hfin => exact .snoc prior ok (hfin.trans ht)

lemma Checked.lookup {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p} {rows T}
    (h : Checked all i g s rows T) (pre : List (Frame p)) (c : Frame p) (tail : List (Frame p))
    (he : rows = pre ++ c :: tail) :
    Suitable all i g s pre c ∧ c.finish ≤ due T tail false ∧ c.finish ≤ T := by
  induction h generalizing pre c tail with
  | nil => simp at he
  | @snoc past last cap prior ok hfin ih =>
    induction tail using List.reverseRecOn with
    | nil =>
      obtain rfl : past = pre := List.append_inj_left' he (by simp)
      have hl := List.append_cancel_left he
      obtain rfl : last = c := List.cons.inj hl |>.1
      exact ⟨ok, hfin, hfin⟩
    | append_singleton tail e _ =>
      have he' : (past ++ [last]) = (pre ++ c :: tail) ++ [e] := by simpa using he
      have heq := List.append_inj_left' he' (by simp)
      have hl := List.append_cancel_left (heq ▸ he')
      obtain rfl : last = e := List.cons.inj hl |>.1
      obtain ⟨hok, hg, hb⟩ := ih pre c tail heq
      refine ⟨hok, ?_, hb.trans (ok.order.trans hfin)⟩
      cases tail <;> simpa [due] using hg

lemma certificate {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p} {T : Time}
    (h : ∀ i, Checked all i g s (all i) T) : Certified g s T all := by
  refine ⟨fun i pre c rest he => ⟨((h i).lookup pre c rest he).1.order, ((h i).lookup pre c rest he).2.1⟩,
    ?_, fun i pre c rest he => ((h i).lookup pre c rest he).1.sample,
    fun i pre c rest he => ((h i).lookup pre c rest he).1.send,
    fun i pre c rest he => ((h i).lookup pre c rest he).1.receive⟩
  intro i c hc
  obtain ⟨pre,rest,he⟩ := List.append_of_mem hc
  exact ((h i).lookup pre c rest he).2.2

end LongTails.Proofs.LocalReservations
