import LongTails.Proofs.BirchCollectionDelayedPackets
import LongTails.Proofs.BirchCollectionScaledReset

namespace LongTails.Proofs.BirchCollectionDelayedTrace

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionPackets
open LongTails.Proofs.BirchCollectionDelayedPackets

def frontier (fs : List ℕ) (n : ℕ) : ℕ := fs[n]?.getD 0

structure Path (s : TraceState) (fs : List ℕ) (B window : ℕ) (move : ℝ) : Prop where
  size : s.nextDirection = fs.length
  states : s.nextState = 2 * s.nextDirection + 1
  marks : s.markers = (List.range (s.nextDirection + 1)).map (2 * ·)
  history : ∀ k ≤ s.nextDirection, (s.states (2 * k)).history = range k
  direction : ∀ k < s.nextDirection, let a := frontier fs k
    a ≤ k ∧ k - a ≤ window ∧
    (s.directions k).source = 2 * a ∧ (s.directions k).history = range a ∧
      (s.directions k).refresh = 1 ∧ (s.directions k).movement = move ∧
      (s.directions k).raw.length = B

structure Data {m : ℕ} (B window : ℕ) (move : ℝ) (s : Controller m) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  path : Path s.trace s.frontiers B window move
  saved : ∀ w, (s.saved w).round ≤ s.round ∧ (s.saved w).point = 2 * (s.saved w).round
  ticket : ∀ w t, s.pending w = some t → TicketData s.trace t (s.saved w).point (w.val + 1) B move
  distinct : ∀ w v t u, s.pending w = some t → s.pending v = some u → w ≠ v →
    t.collection ≠ u.collection

lemma path_same (s t : TraceState) (fs : List ℕ) (B window : ℕ) (move : ℝ)
    (h : Path s fs B window move)
    (hsc : t.nextState = s.nextState) (hdc : t.nextDirection = s.nextDirection)
    (hstates : t.states = s.states) (hdirs : t.directions = s.directions)
    (hmarks : t.markers = s.markers) : Path t fs B window move := by
  refine ⟨hdc.trans h.size, ?_, ?_, ?_, ?_⟩
  · rw [hsc, hdc]
    exact h.states
  · rw [hmarks, hdc]
    exact h.marks
  · rw [hdc, hstates]
    exact h.history
  · rw [hdc, hdirs]
    exact h.direction

lemma head_eq {m B window : ℕ} {move : ℝ} {s : Controller m} (h : Data B window move s) :
    s.head = 2 * s.round := by
  unfold Controller.head Controller.round
  rw [h.path.marks, List.range_succ, List.map_append]
  simp

lemma saved_bound {m B window : ℕ} {move : ℝ} {s : Controller m}
    (h : Data B window move s) (w : Fin m) : (s.saved w).point < s.trace.nextState := by
  rw [(h.saved w).2, h.path.states]
  have hround : (s.saved w).round ≤ s.trace.nextDirection := (h.saved w).1
  omega

lemma initial_data (m B window : ℕ) (move : ℝ) : Data (m := m) B window move {} := by
  refine ⟨rfl, trivial, by simp [RetiredPast], ⟨rfl, rfl, rfl, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · intro k hk
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    rfl
  · intro k hk
    exact (Nat.not_lt_zero _ hk).elim
  · intro _
    exact ⟨le_rfl, rfl⟩
  · simp
  · simp

lemma append_legal {m B window : ℕ} {move : ℝ} {s : Controller m} (hs : Data B window move s)
    (events : List Event) (he : ValidFrom (m + 1) s.trace events) :
    run (s.append events).events = (s.append events).trace ∧
      ValidFrom (m + 1) {} (s.append events).events ∧ RetiredPast (s.append events).trace := by
  have hr : run (s.events ++ events) = events.foldl step (run s.events) := List.foldl_append
  rw [hs.represented] at hr
  have hv : ValidFrom (m + 1) {} (s.events ++ events) := by
    apply (valid_append _ _ _ _).2
    refine ⟨hs.legal, ?_⟩
    change ValidFrom (m + 1) (run s.events) events
    rwa [hs.represented]
  exact ⟨hr, hv, retired_past_fold _ _ _ hs.retired he⟩

lemma query_data {m K B window : ℕ} {move : ℝ} (s : Controller m) (w : Fin m)
    (hs : Data B window move s) (_hw : Enabled K s (.query w))
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    Data B window move (advance K B window move s (.query w)) := by
  let es := queryEvents B move s w
  let out := advance K B window move s (.query w)
  let t := step s.trace (.capture (w.val + 1) (s.saved w).point B 1 move)
  let ticket : Ticket := ⟨s.trace.nextCollection, s.trace.nextRaw⟩
  obtain ⟨hv, hl⟩ := launch_data (m + 1) s w B move (Nat.succ_lt_succ w.isLt)
    (saved_bound hs w) hB hm0 hm1 hs.retired
  have hi : IssueData t out.trace s.trace.nextCollection (w.val + 1) B := hl.issue
  have hfield := hi.fields
  have hcoll : out.trace.nextCollection = s.trace.nextCollection + 1 :=
    congrArg TraceState.nextCollection hfield
  have hround : out.trace.nextDirection = s.trace.nextDirection := by
    simpa only [t, step] using congrArg TraceState.nextDirection hfield
  have ht (v : Fin m) : out.pending v = Function.update s.pending w (some ticket) v := rfl
  obtain ⟨hr, hv', hret⟩ := append_legal hs es hv
  change Data B window move out
  refine ⟨hr, hv', hret, path_same _ _ _ _ _ _ hs.path
    (by simpa only [t, step] using congrArg TraceState.nextState hfield) hround
    (by simpa only [t, step] using congrArg TraceState.states hfield)
    (by simpa only [t, step] using congrArg TraceState.directions hfield)
    (by simpa only [t, step] using congrArg TraceState.markers hfield), ?_, ?_, ?_⟩
  · intro v
    change (s.saved v).round ≤ out.trace.nextDirection ∧ _
    rw [hround]
    exact hs.saved v
  · intro v j hj
    by_cases he : v = w
    · subst v
      rw [ht, Function.update_self, Option.some.injEq] at hj
      subst j
      exact hl.ticket
    · rw [ht, Function.update_of_ne he] at hj
      have hp := hs.ticket v j hj
      refine ⟨?_, ?_, ?_⟩
      · rw [hcoll]
        exact hp.collection.trans (Nat.lt_succ_self _)
      · rw [congrArg TraceState.collections hfield]
        change (Function.update s.trace.collections s.trace.nextCollection _ j.collection) = _
        rw [Function.update_of_ne (Nat.ne_of_lt hp.collection)]
        exact hp.header
      · intro q hq
        obtain ⟨hqr, hqf, hqc⟩ := hp.raw q hq
        refine ⟨?_, ?_, ?_⟩
        · rw [hi.nextRaw]
          exact hqr.trans_le (Nat.le_add_right _ _)
        · rw [congrArg TraceState.retired hfield]
          exact hqf
        · rw [hi.oldRaw q hqr]
          exact hqc
  · intro v u j j' hj hj' hne
    by_cases h₁ : v = w
    · subst v
      have h₂ : u ≠ w := Ne.symm hne
      rw [ht, Function.update_self, Option.some.injEq] at hj
      rw [ht, Function.update_of_ne h₂] at hj'
      subst j
      exact Nat.ne_of_gt (hs.ticket u j' hj').collection
    · rw [ht, Function.update_of_ne h₁] at hj
      by_cases h₂ : u = w
      · subst u
        rw [ht, Function.update_self, Option.some.injEq] at hj'
        subst j'
        exact Nat.ne_of_lt (hs.ticket v j hj).collection
      · rw [ht, Function.update_of_ne h₂] at hj'
        exact hs.distinct v u j j' hj hj' hne

lemma path_commit (s t : TraceState) (fs : List ℕ) (ticket : Ticket)
    (source B window a : ℕ) (move : ℝ) (hp : Path s fs B window move)
    (hc : CommitData s t ticket source B s.nextDirection a move)
    (ha : a ≤ s.nextDirection) (hw : s.nextDirection - a ≤ window) (hs : source = 2 * a) :
    Path t (fs ++ [a]) B window move := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.directionCount, hp.size, List.length_append, List.length_singleton]
  · rw [hc.stateCount, hc.directionCount, hp.states]
    omega
  · rw [hc.markers, hp.marks, hp.states, hc.directionCount]
    have hr : List.range (s.nextDirection + 1 + 1) =
        List.range (s.nextDirection + 1) ++ [s.nextDirection + 1] := List.range_succ
    rw [hr, List.map_append]
    congr 1
  · intro k hk
    rw [hc.directionCount] at hk
    by_cases h : k = s.nextDirection + 1
    · subst k
      have he : 2 * (s.nextDirection + 1) = s.nextState + 1 := by rw [hp.states]; omega
      rw [he]
      exact hc.newMain
    · have hle : k ≤ s.nextDirection := by omega
      rw [hc.oldState _ (by rw [hp.states]; omega)]
      exact hp.history k hle
  · intro k hk
    rw [hc.directionCount] at hk
    by_cases h : k = s.nextDirection
    · subst k
      have hget : frontier (fs ++ [a]) s.nextDirection = a := by
        simp [frontier, hp.size]
      change a ≤ s.nextDirection at ha
      simpa only [hget, hc.newDirection, hs, List.length_range', true_and, and_self, and_true] using
        (show a ≤ s.nextDirection ∧ s.nextDirection - a ≤ window from ⟨ha, hw⟩)
    · have hlt : k < s.nextDirection := by omega
      have hget : frontier (fs ++ [a]) k = frontier fs k := by
        unfold frontier
        rw [List.getElem?_append_left (hp.size ▸ hlt)]
      simpa only [hget, hc.oldDirection _ hlt] using hp.direction k hlt

lemma reply_after_landing {m B window : ℕ} {move : ℝ} (s : Controller m)
    (w : Fin m) (ticket : Ticket) (es : List Event) (fs : List ℕ)
    (hs : Data B window move s) (hw : s.pending w = some ticket)
    (he : ValidFrom (m + 1) s.trace es)
    (hl : LandingData s.trace (s.append es).trace ticket B)
    (hp : Path (s.append es).trace fs B window move)
    (hround : s.round ≤ (s.append es).round) :
    let t := s.append es
    Data B window move {t with
      saved := Function.update s.saved w ⟨t.round, t.head⟩
      pending := Function.update s.pending w none
      frontiers := fs } := by
  let t := s.append es
  let out : Controller m := {t with
    saved := Function.update s.saved w ⟨t.round, t.head⟩
    pending := Function.update s.pending w none
    frontiers := fs }
  change Data B window move out
  obtain ⟨hr, hv, hret⟩ := append_legal hs es he
  have hl' : LandingData s.trace out.trace ticket B := hl
  have hhead : t.head = 2 * t.round := by
    unfold Controller.head Controller.round
    rw [hp.marks]
    have hrange : List.range (t.trace.nextDirection + 1) =
        List.range t.trace.nextDirection ++ [t.trace.nextDirection] := List.range_succ
    rw [hrange, List.map_append]
    simp
  have hsave (v : Fin m) : out.saved v = Function.update s.saved w ⟨t.round, t.head⟩ v := rfl
  have hkeep (v : Fin m) (j : Ticket) (hj : out.pending v = some j) :
      v ≠ w ∧ s.pending v = some j := by
    change Function.update s.pending w none v = some j at hj
    by_cases h : v = w
    · subst v
      simp at hj
    · rw [Function.update_of_ne h] at hj
      exact ⟨h, hj⟩
  refine ⟨hr, hv, hret, hp, ?_, ?_, ?_⟩
  · intro v
    rw [hsave]
    by_cases h : v = w
    · subst v
      rw [Function.update_self]
      exact ⟨le_rfl, hhead⟩
    · rw [Function.update_of_ne h]
      exact ⟨(hs.saved v).1.trans hround, (hs.saved v).2⟩
  · intro v j hj
    obtain ⟨hne, hj⟩ := hkeep v j hj
    have hdata := hs.ticket v j hj
    have hdistinct := hs.distinct v w j ticket hj hw hne
    rw [hsave, Function.update_of_ne hne]
    refine ⟨?_, ?_, ?_⟩
    · rw [hl'.collectionCount]
      exact hdata.collection
    · rw [hl'.oldCollection _ hdistinct]
      exact hdata.header
    · intro q hq
      obtain ⟨hqr, hqf, hqc⟩ := hdata.raw q hq
      rw [hl'.rawCount, hl'.raw, hl'.retired]
      refine ⟨hqr, ?_, hqc⟩
      intro h
      rcases mem_union.mp h with h | h
      · exact hqf h
      · have heq := (hs.ticket w ticket hw).raw q (List.mem_toFinset.mp h)
        exact hdistinct (congrArg RawRecord.collection (hqc.symm.trans heq.2.2))
  · intro v u j j' hv hu hne
    exact hs.distinct v u j j' (hkeep v j hv).2 (hkeep u j' hu).2 hne

lemma reply_data {m K B window : ℕ} {move : ℝ} (s : Controller m) (w : Fin m)
    (hs : Data B window move s) (hw : Enabled K s (.reply w)) :
    Data B window move (advance K B window move s (.reply w)) := by
  cases hticket : s.pending w with
  | none =>
    have h : (s.pending w).isSome := hw
    simp [hticket] at h
  | some ticket =>
    let es := replyEvents K B window s w ticket
    let fs := if accepts K window s w then s.frontiers ++ [(s.saved w).round] else s.frontiers
    have ht := hs.ticket w ticket hticket
    suffices ValidFrom (m + 1) s.trace es ∧
        LandingData s.trace (s.append es).trace ticket B ∧
        Path (s.append es).trace fs B window move ∧ s.round ≤ (s.append es).round by
      obtain ⟨he, hl, hp, hround⟩ := this
      simpa only [advance, hticket] using
        reply_after_landing s w ticket es fs hs hticket he hl hp hround
    by_cases ha : accepts K window s w
    · have hhead : s.head < s.trace.nextState := by
        rw [head_eq hs, hs.path.states]
        exact Nat.lt_succ_self _
      have hcur : (s.trace.states s.head).history = range s.round := by
        rw [head_eq hs]
        exact hs.path.history _ le_rfl
      have hquery : (s.trace.states (s.saved w).point).history = range (s.saved w).round := by
        rw [(hs.saved w).2]
        exact hs.path.history _ (hs.saved w).1
      obtain ⟨hv, hc⟩ := commit_data (m + 1) s.trace ticket s.head (s.saved w).point (w.val + 1) B
        s.round (s.saved w).round move (Nat.zero_lt_succ _) ht hhead
        (saved_bound hs w) rfl hcur hquery rfl (hs.saved w).1
      have heq : es = (List.range' ticket.firstRaw B).map Event.receive ++
          [.finish ticket.collection, .merge 0 s.head s.trace.nextState (s.saved w).point,
            .mark (s.trace.nextState + 1)] := by simp [es, replyEvents, ha]
      have hfs : fs = s.frontiers ++ [(s.saved w).round] := ite_eq_left ha
      rw [heq, hfs]
      refine ⟨hv, hc.landing, path_commit _ _ _ _ _ _ _ _ _ hs.path hc
        (hs.saved w).1 ha.2 (hs.saved w).2, ?_⟩
      change s.round ≤ (((List.range' ticket.firstRaw B).map Event.receive ++
        [Event.finish ticket.collection, Event.merge 0 s.head s.trace.nextState (s.saved w).point,
          Event.mark (s.trace.nextState + 1)]).foldl step s.trace).nextDirection
      rw [hc.directionCount]
      exact Nat.le_succ _
    · obtain ⟨hv, hd, he⟩ := rejected_data (m + 1) s.trace ticket (s.saved w).point (w.val + 1) B move ht
      have heq : es = (List.range' ticket.firstRaw B).map Event.discard ++ [.cancel ticket.collection] := by
        simp [es, replyEvents, ha]
      have hfs : fs = s.frontiers := ite_eq_right ha
      have hrun : (s.append es).trace = { s.trace with
          retired := s.trace.retired ∪ (List.range' ticket.firstRaw B).toFinset
          collections := Function.update s.trace.collections ticket.collection
            { s.trace.collections ticket.collection with closed := true } } := by
        change es.foldl step s.trace = _
        rw [heq]
        exact he
      have hround : (s.append es).round = s.round := by
        change (s.append es).trace.nextDirection = s.trace.nextDirection
        rw [hrun]
      refine ⟨heq.symm ▸ hv, ?_, ?_, hround.ge⟩
      · change LandingData s.trace (es.foldl step s.trace) ticket B
        rwa [heq]
      · rw [hfs, hrun]
        exact path_same _ _ _ _ _ _ hs.path rfl rfl rfl rfl rfl

lemma data_run {m K B window : ℕ} (move : ℝ) (events : List (OriginalEvent m))
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : LegalFrom K B window move {} events) :
    Data B window move (runController K B window move events) := by
  have aux (s : Controller m) (xs : List (OriginalEvent m)) (hs : Data B window move s)
      (he : LegalFrom K B window move s xs) :
      Data B window move (xs.foldl (advance K B window move) s) := by
    induction xs generalizing s with
    | nil => exact hs
    | cons e xs ih =>
      apply ih _ _ he.2
      cases e with
      | query w => exact query_data s w hs he.1 hB hm0 hm1
      | reply w => exact reply_data s w hs he.1
  exact aux {} events (initial_data m B window move) he

end LongTails.Proofs.BirchCollectionDelayedTrace
