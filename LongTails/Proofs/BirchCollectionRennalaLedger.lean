import LongTails.Algorithms.BirchCollectionRennala
import LongTails.Proofs.BirchNonEuclideanRennalaScheduling

namespace LongTails.Proofs.BirchCollectionRennalaLedger

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionRennala

local notation "OEvent" => LongTails.Algorithms.BirchNonEuclideanRennala.Event
local notation "ostep" => LongTails.Algorithms.BirchNonEuclideanRennala.step
local notation "orun" => LongTails.Algorithms.BirchNonEuclideanRennala.run
local notation "CompleteTrace" => LongTails.Algorithms.BirchNonEuclideanRennala.CompleteTrace

open LongTails.Proofs.BirchNonEuclideanRennalaScheduling
  (completeTrace_query_count completeTrace_query_bound)

lemma calls_append (xs ys : List Event) : calls (xs ++ ys) = calls xs + calls ys := by
  simp [calls]

lemma emissions_calls {m : ℕ} (K B : ℕ) (s : Translation m) (e : OEvent m) :
    calls (emissions K B s e) = match e with | .query _ => 1 | .reply _ => 0 := by
  cases e <;> simp only [emissions] <;> split_ifs <;> simp [calls, Event.calls]

lemma advance_represented {m : ℕ} (K B : ℕ) (s : Translation m) (e : OEvent m)
    (hs : run s.events = s.trace) : run (advance K B s e).events = (advance K B s e).trace := by
  simp only [advance, run, List.foldl_append] at *
  rw [hs]

lemma advance_query_delta {m : ℕ} (K B : ℕ) (s : Translation m) (e : OEvent m) :
    (advance K B s e).original.queries.length =
      s.original.queries.length + calls (emissions K B s e) := by
  rw [emissions_calls]
  cases e
  · simp [advance, LongTails.Algorithms.BirchNonEuclideanRennala.step]
  · simp only [advance, LongTails.Algorithms.BirchNonEuclideanRennala.step]
    split_ifs <;> rfl

lemma fold_refines_ledger {m : ℕ} (K B : ℕ) (s : Translation m) (events : List (OEvent m))
    (hs : calls s.events = s.original.queries.length) :
    let out := events.foldl (advance K B) s
    out.original = events.foldl (ostep K B) s.original ∧
      calls out.events = out.original.queries.length := by
  induction events generalizing s with
  | nil => exact ⟨rfl, hs⟩
  | cons e events ih =>
    apply ih
    rw [show (advance K B s e).events = s.events ++ emissions K B s e from rfl,
      calls_append, hs, advance_query_delta]

lemma translate_ledger {m : ℕ} (K B : ℕ) (events : List (OEvent m)) :
    let t := translate K B events
    t.original = orun K B events ∧ calls t.events = (orun K B events).queries.length := by
  have h := fold_refines_ledger K B (initial m B) events rfl
  exact ⟨h.1, h.2.trans (congrArg (fun s => s.queries.length) h.1)⟩

lemma translate_calls {m : ℕ} (K B : ℕ) (events : List (OEvent m))
    (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    calls (translate K B events).events =
      K * B + (orun K B events).stale.length + (m - 1) :=
  (translate_ledger K B events).2.trans (completeTrace_query_count K B events hK hB he)

lemma translate_calls_bound {m : ℕ} (K B : ℕ) (events : List (OEvent m))
    (hm : 0 < m) (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    calls (translate K B events).events ≤ K * (B + m - 1) := by
  rw [(translate_ledger K B events).2]
  exact completeTrace_query_bound K B events hm hK hB he

end LongTails.Proofs.BirchCollectionRennalaLedger
