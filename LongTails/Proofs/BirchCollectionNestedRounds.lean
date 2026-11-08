import LongTails.Proofs.BirchCollectionNestedExport

namespace LongTails.Proofs.BirchCollectionNestedRounds

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested
open LongTails.Proofs.BirchCollectionNestedRun
open LongTails.Proofs.BirchCollectionNestedExport
open LongTails.Proofs.BirchCollectionLocalRounds
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionBatches (RetiredPast)

lemma arrival_fold {m start Q B : ℕ} {move : ℝ} (layout : Layout m) (s : State m)
    (arrivals : List (Fin m)) (hs : Data layout s start B move)
    (hcount : s.outer.completed + arrivals.length ≤ Q)
    (hp : s.outer.completed < Q → ∀ w, (s.outer.pending w).isSome)
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    let out := arrivals.foldl (advance layout Q B move) s
    Data layout out start B move ∧ Extends s.outer.trace out.outer.trace ∧
      out.outer.completed = s.outer.completed + arrivals.length ∧
      out.outer.trace.markers = s.outer.trace.markers ∧
      (out.outer.completed < Q → ∀ w, (out.outer.pending w).isSome) := by
  induction arrivals generalizing s with
  | nil => exact ⟨hs, extends_refl _, rfl, rfl, hp⟩
  | cons w arrivals ih =>
    have hlt : s.outer.completed < Q := by simp only [List.length_cons] at hcount; omega
    obtain ⟨hd, hx, hc, hm, hr⟩ := advance_data layout s w hs hlt (hp hlt) hB hm0 hm1
    have hc' : (advance layout Q B move s w).outer.completed + arrivals.length ≤ Q := by
      rw [hc]
      simp only [List.length_cons] at hcount
      omega
    obtain ⟨hf, he, hcf, hmf, hp'⟩ := ih (advance layout Q B move s w) hd hc' hr
    refine ⟨hf, hx.trans he, ?_, hmf.trans hm, hp'⟩
    exact hcf.trans (by rw [hc, List.length_cons]; omega)

lemma nested_round {m K Q B : ℕ} {move : ℝ} (layout : Layout m) (s : Round m)
    (arrivals : List (Fin m)) (hs : History s K Q B move) (hQ : 0 < Q) (hB : 0 < B)
    (hm0 : 0 ≤ move) (hm1 : move ≤ 1) (ha : arrivals.length = Q) :
    History (runRound layout Q B move s arrivals) (K + 1) Q B move := by
  let root := start layout B move s.trace s.events
  let t := arrivals.foldl (advance layout Q B move) root
  let out := collectAll layout t (LongTails.Algorithms.BirchCollectionLocal.abortPending B t.outer)
  obtain ⟨hd, hx, hc, hm, hp⟩ :=
    start_data layout s.trace s.events hs.represented hs.legal hs.retired hs.directions hs.last.1 hs.last.2
      hB hm0 hm1
  have hcount : root.outer.completed + arrivals.length ≤ Q := by
    change root.outer.completed = 0 at hc
    rw [hc, ha, zero_add]
  obtain ⟨ht, he, hct, hmt, _⟩ := arrival_fold layout root arrivals hd hcount (fun _ => hp) hB hm0 hm1
  obtain ⟨ho, he', hco, hmo⟩ := collect_all layout t ht
  have htotal : out.completed = Q := by
    change out.completed = t.outer.completed at hco
    rw [hco, hct, hc, ha, zero_add]
  exact history_publish s out hs hQ ho htotal (hx.trans (he.trans he')) (hmo.trans (hmt.trans hm))

lemma nested_fold {m K Q B : ℕ} {move : ℝ} (layout : Layout m) (s : Round m)
    (arrivals : List (List (Fin m))) (hs : History s K Q B move) (hQ : 0 < Q) (hB : 0 < B)
    (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (ha : ∀ order ∈ arrivals, order.length = Q) :
    History (arrivals.foldl (runRound layout Q B move) s) (K + arrivals.length) Q B move := by
  induction arrivals generalizing s K with
  | nil => exact hs
  | cons order orders ih =>
    have h := nested_round layout s order hs hQ hB hm0 hm1 (ha order (by simp))
    have ht := ih _ h (fun e he => ha e (by simp [he]))
    simpa only [List.foldl_cons, List.length_cons, Nat.add_right_comm K 1 orders.length, Nat.add_assoc] using ht

lemma nested_history {m Q B : ℕ} {move : ℝ} (layout : Layout m)
    (arrivals : List (List (Fin m))) (hQ : 0 < Q) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (ha : ∀ order ∈ arrivals, order.length = Q) :
    History (runRounds layout Q B move arrivals) arrivals.length Q B move := by
  simpa only [runRounds, zero_add] using
    nested_fold layout (Round.initial m {} []) arrivals (initial_history m Q B move) hQ hB hm0 hm1 ha


structure BlockEffect {m : ℕ} (s t : Round m) (Q B : ℕ) (move : ℝ) : Prop where
  represented : run t.events = t.trace
  legal : ValidFrom (m + 1) {} t.events
  retired : RetiredPast t.trace
  extension : Extends s.trace t.trace
  count : t.trace.nextDirection = s.trace.nextDirection + Q
  mark : ∃ head < t.trace.nextState, t.trace.markers = s.trace.markers ++ [head] ∧
    (t.trace.states head).history = Finset.range t.trace.nextDirection
  direction : ∀ n, s.trace.nextDirection ≤ n → n < t.trace.nextDirection →
    Finset.range s.trace.nextDirection ⊆ (t.trace.directions n).history ∧
    (t.trace.directions n).history ⊆ Finset.range n ∧ (t.trace.directions n).refresh = 1 ∧
    (t.trace.directions n).movement = move ∧ (t.trace.directions n).raw.length = B

lemma nested_block {m Q B : ℕ} {move : ℝ} (layout : Layout m) (s : Round m)
    (arrivals : List (Fin m)) (hr : run s.events = s.trace) (hl : ValidFrom (m + 1) {} s.events)
    (hs : RetiredPast s.trace) (hb : s.trace.markers.getLast?.getD 0 < s.trace.nextState)
    (hh : (s.trace.states (s.trace.markers.getLast?.getD 0)).history = Finset.range s.trace.nextDirection)
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) (ha : arrivals.length = Q) :
    BlockEffect s (runRound layout Q B move s arrivals) Q B move := by
  let root := start layout B move s.trace s.events
  let t := arrivals.foldl (advance layout Q B move) root
  let out := collectAll layout t (LongTails.Algorithms.BirchCollectionLocal.abortPending B t.outer)
  obtain ⟨hd, hx, hc, hm, hp⟩ :=
    start_data layout s.trace s.events hr hl hs rfl hb hh hB hm0 hm1
  have hcount : root.outer.completed + arrivals.length ≤ Q := by
    change root.outer.completed = 0 at hc
    rw [hc, ha, zero_add]
  obtain ⟨ht, he, hct, hmt, _⟩ := arrival_fold layout root arrivals hd hcount (fun _ => hp) hB hm0 hm1
  obtain ⟨ho, he', hco, hmo⟩ := collect_all layout t ht
  have htotal : out.completed = Q := by
    change out.completed = t.outer.completed at hco
    rw [hco, hct, hc, ha, zero_add]
  obtain ⟨hr', hl', hs', hp'⟩ := LongTails.Proofs.BirchCollectionLocalPublish.publish_round_info out ho
  change BlockEffect s (LongTails.Algorithms.BirchCollectionLocal.publish B out) Q B move
  refine ⟨hr', hl', hs', hx.trans (he.trans (he'.trans hp'.extension)), ?_, ?_, ?_⟩
  · exact hp'.directionCount.trans (ho.forest.count.trans (congrArg (s.trace.nextDirection + ·) htotal))
  · obtain ⟨head, hb', hm', hh'⟩ := hp'.mark
    exact ⟨head, hb', hm'.trans (congrArg (· ++ [head]) (hmo.trans (hmt.trans hm))), hh'⟩
  · intro n hn hn'
    rw [hp'.directions]
    exact ho.forest.direction n hn (hp'.directionCount ▸ hn')


end LongTails.Proofs.BirchCollectionNestedRounds
