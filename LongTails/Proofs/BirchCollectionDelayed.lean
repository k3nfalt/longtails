import LongTails.Proofs.BirchCollectionDelayedTrace
import LongTails.Proofs.BirchCollectionSerialCertificate
import LongTails.Proofs.BirchCollectionBounds

namespace LongTails.Proofs.BirchCollectionDelayed

open Finset OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed
open LongTails.Algorithms.BirchCollectionBatches (vanillaOrdering)
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionDelayedTrace
open LongTails.Proofs.BirchCollectionExecution (run_raw program_calls)
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Proofs.BirchCollectionScaledReset (window_structural)
open LongTails.Proofs.BirchCollectionSerialCertificate (vanilla_label)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Theorems.BirchCollections (budget)
open LongTails.Proofs.BirchCollectionBounds (scaled_budget)

lemma delayed_ordering {s : TraceState} {fs : List ℕ} {B window : ℕ} {move : ℝ}
    (hp : Path s fs B window move) (hpos : 0 < s.nextDirection) :
    let o := delayedOrdering fs
    o.Valid s s.nextDirection ∧
      (∀ n, n < o.labels.length → o.frontier n ≤ n ∧ n - o.frontier n ≤ window ∧
        range (o.frontier n) ⊆ o.history s n) ∧
      (∀ n, n < o.labels.length → o.refresh s n = 1 ∧ o.movement s n = move ∧
        (s.directions (o.label n)).raw.length = B) := by
  let o := delayedOrdering fs
  let K := s.nextDirection
  have hlen : o.labels.length = K := List.length_range.trans hp.size.symm
  have hlabel (n : ℕ) (hn : n < K) : o.label n = n :=
    vanilla_label fs.length n (hp.size ▸ hn)
  have hh (n : ℕ) (hn : n < K) : o.history s n = range (frontier fs n) := by
    obtain ⟨ha, _, _, hd, _, _, _⟩ := hp.direction n hn
    unfold Ordering.history
    rw [hlen, ite_eq_left hn, hlabel n hn, hd]
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hj, h⟩
      simpa only [hlabel j hj] using h
    · intro hj
      have hjK := (hj.trans_le ha).trans hn
      exact ⟨hjK, by rwa [hlabel j hjK]⟩
  change o.Valid s K ∧ _
  refine ⟨⟨hlen.symm ▸ hpos, List.nodup_range, ?_, rfl, hlen.symm,
    fun k _ => Nat.lt_succ_self k, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp.marks]
    simp [K]
  · intro n hn
    have hn' : n < K := hlen ▸ hn
    rw [hlabel n hn']
    exact hn'
  · intro k hk
    have hidx : k < (List.range (K + 1)).length := by simp [Nat.lt_succ_of_le hk]
    rw [hp.marks]
    have hsidx : k < ((List.range (K + 1)).map (2 * ·)).length := by simpa using hidx
    rw [List.getElem?_eq_getElem hsidx, Option.getD_some, List.getElem_map, List.getElem_range,
      hp.history k hk]
    change range k = (range k).image o.label
    ext i
    constructor
    · intro hi
      exact mem_image.mpr ⟨i, hi, hlabel i ((mem_range.mp hi).trans_le hk)⟩
    · intro hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      simpa only [hlabel j ((mem_range.mp hj).trans_le hk)] using hj
  · intro n
    by_cases hn : n < K
    · rw [hh n hn]
      exact range_mono (hp.direction n hn).1
    · simp only [Ordering.history, hlen, ite_eq_right hn]
      exact le_rfl
  · intro n hn
    have hn' : n < K := hlen ▸ hn
    obtain ⟨ha, hw, _⟩ := hp.direction n hn'
    change frontier fs n ≤ n ∧ n - frontier fs n ≤ window ∧ _
    rw [hh n hn']
    exact ⟨ha, hw, le_rfl⟩
  · intro n hn
    have hn' : n < K := hlen ▸ hn
    obtain ⟨_, _, _, _, hr, hm, hb⟩ := hp.direction n hn'
    change o.refresh s n = 1 ∧ o.movement s n = move ∧ (s.directions (o.label n)).raw.length = B
    simp only [Ordering.refresh, Ordering.movement, hlen, ite_eq_left hn', hlabel n hn']
    exact ⟨hr, hm, hb⟩

lemma delayed_valid (p : Params) (m window : ℕ) (events : List (OriginalEvent m))
    (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (he : Complete p m window events) : spec.valid (delayed p m window events) := by
  let q := tuned p m window
  let K := horizon q
  let B := batchSize q
  let move : ℝ := 1 / divisor 1 window
  let s := runController K B window move events
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hc : (1 : ℝ) ≤ divisor 1 window := by
    exact_mod_cast (show 1 ≤ divisor 1 window by unfold divisor; omega)
  have hcp : (0 : ℝ) < divisor 1 window := by linarith
  have hs : Data B window move s := data_run move events hB (by positivity) ((div_le_one hcp).2 hc) he.1
  have hround : s.trace.nextDirection = K := he.2
  have hp : 0 < s.trace.nextDirection := hround.symm ▸ hK
  obtain ⟨ho, hf, hm⟩ := delayed_ordering hs.path hp
  let o := delayedOrdering s.frontiers
  have ho' : o.Valid s.trace K := hround ▸ ho
  have hlen : o.labels.length = K := List.length_range.trans (hs.path.size.symm.trans hround)
  let D := s.trace.nextRaw - B * K
  have hs' : Structural s.trace (resetOrdering o) (controls 1 1 window D) K B := by
    have h := window_structural (m + 1) K B 1 1 window D s.events o hs.legal
      (hs.represented.symm ▸ ho') Nat.one_pos le_rfl
    rw [hs.represented] at h
    refine h hf ?_ (fun n hn => (hm n hn).1) (fun n hn => (hm n hn).2.1)
      (fun n hn => (hm n hn).2.2) ?_
    · intro k _
      change 1 ≤ k + 1 - k ∧ k + 1 - k ≤ 1
      omega
    · rw [hlen]
      dsimp [D]
      omega
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.legal,
    hs.represented.symm ▸ hs'⟩

lemma delayed_success (p : Params) (m window : ℕ) (events : List (OriginalEvent m))
    (hp : spec.valid (delayed p m window events))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (delayed p m window events) I O) :
    let q := delayed p m window events
    let Q := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => Q) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (delayed p m window events) hp _ le_rfl I O hI

def launches {m : ℕ} (events : List (OriginalEvent m)) : ℕ :=
  (events.map (fun e => match e with | .query _ => 1 | .reply _ => 0)).sum

lemma packet_calls {m K B window : ℕ} (move : ℝ) (s : Controller m) (e : OriginalEvent m) :
    calls (advance K B window move s e).events =
      calls s.events + B * launches [e] := by
  have happend (xs ys : List Event) : calls (xs ++ ys) = calls xs + calls ys := by simp [calls]
  cases e with
  | query w =>
    simp [advance, Controller.append, queryEvents, calls, Event.calls, launches]
  | reply w =>
    cases h : s.pending w with
    | none => simp [advance, h, launches]
    | some t =>
      have hr : calls (replyEvents K B window s w t) = 0 := by
        unfold replyEvents
        dsimp
        split_ifs <;> simp [calls, Event.calls, List.map_map, Function.comp_def]
      simp [advance, h, Controller.append, happend, hr, launches]

lemma delayed_calls {m K B window : ℕ} (move : ℝ) (events : List (OriginalEvent m)) :
    calls (runController K B window move events).events = B * launches events := by
  have h (s : Controller m) (es : List (OriginalEvent m)) :
      calls (es.foldl (advance K B window move) s).events = calls s.events + B * launches es := by
    induction es generalizing s with
    | nil => simp [launches]
    | cons e es ih =>
      rw [List.foldl_cons, ih, packet_calls]
      have he : launches (e :: es) = launches [e] + launches es := by simp [launches]
      rw [he, Nat.mul_add, Nat.add_assoc]
  simpa [runController, calls] using h {} events

lemma ringmaster_age {m K : ℕ} (G : ℕ) (s : Controller m) (w : Fin m) (hG : 0 < G) :
    accepts K (G - 1) s w ↔ s.round < K ∧ s.round - (s.saved w).round < G := by
  unfold accepts
  omega

lemma delayed_budget (p : Params) (m window : ℕ) (events : List (OriginalEvent m)) :
    let q := delayed p m window events
    budget q 0 = q.controls.waste + batchSize q * horizon q := by
  let q := delayed p m window events
  change budget q 0 = _
  have h := scaled_budget q 1 1 window q.controls.waste Nat.one_pos rfl
  simpa only [Nat.mul_one] using h

lemma delayed_physical_calls (p : Params) (m window : ℕ) (events : List (OriginalEvent m)) :
    let q := delayed p m window events
    (program q).oracleCalls = batchSize q * launches events := by
  let q := delayed p m window events
  change (program q).oracleCalls = _
  rw [program_calls]
  exact delayed_calls (K := horizon q) (B := batchSize q) (window := window)
    (1 / (divisor 1 window : ℝ)) events

end LongTails.Proofs.BirchCollectionDelayed
