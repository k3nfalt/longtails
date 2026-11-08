import LongTails.Proofs.BirchCollectionLocalPublish
import LongTails.Proofs.BirchCollectionOrdering

namespace LongTails.Proofs.BirchCollectionLocalRounds

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionLocalTrace
open LongTails.Proofs.BirchCollectionLocalPublish
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionOrdering

def marks (es : List Event) : List ℕ :=
  es.filterMap fun e => match e with | .mark n => some n | _ => none

lemma fold_marks (s : TraceState) (es : List Event) :
    (es.foldl step s).markers = s.markers ++ marks es := by
  induction es generalizing s with
  | nil => simp [marks]
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    cases e <;> simp [marks, step, List.append_assoc]

lemma private_frame_step {m B : ℕ} (move : ℝ) (s : Round m) (e : OriginalEvent m) :
    let t := advance B move s e
    Extends s.trace t.trace ∧ t.trace.markers = s.trace.markers := by
  cases e with
  | query w =>
    change Extends s.trace ((localCapture B move s w).foldl step s.trace) ∧
      ((localCapture B move s w).foldl step s.trace).markers = _
    refine ⟨extends_fold _ _, ?_⟩
    rw [fold_marks]
    simp [marks, localCapture]
  | reply w =>
    cases h : s.pending w with
    | none => simp [advance, h, extends_refl]
    | some t =>
      simp only [advance, h]
      change Extends s.trace ((localComplete B t).foldl step s.trace) ∧
        ((localComplete B t).foldl step s.trace).markers = _
      refine ⟨extends_fold _ _, ?_⟩
      rw [fold_marks]
      simp [marks, localComplete, List.filterMap_map]

lemma private_frame {m B : ℕ} (move : ℝ) (s : Round m) (es : List (OriginalEvent m)) :
    let t := es.foldl (advance B move) s
    Extends s.trace t.trace ∧ t.trace.markers = s.trace.markers := by
  induction es generalizing s with
  | nil => exact ⟨extends_refl _, rfl⟩
  | cons e es ih =>
    obtain ⟨he, hm⟩ := private_frame_step (B := B) move s e
    obtain ⟨he', hm'⟩ := ih (advance B move s e)
    exact ⟨he.trans he', hm'.trans hm⟩

structure History {m : ℕ} (s : Round m) (K Q B : ℕ) (move : ℝ) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  directions : s.trace.nextDirection = K * Q
  markers : s.trace.markers.length = K + 1
  last : s.trace.markers.getLast?.getD 0 < s.trace.nextState ∧
    (s.trace.states (s.trace.markers.getLast?.getD 0)).history = range (K * Q)
  history : ∀ k ≤ K, (s.trace.states (s.trace.markers[k]?.getD 0)).history = range (k * Q)
  direction : ∀ n < K * Q,
    range ((n / Q) * Q) ⊆ (s.trace.directions n).history ∧
      (s.trace.directions n).history ⊆ range n ∧ (s.trace.directions n).refresh = 1 ∧
      (s.trace.directions n).movement = move ∧ (s.trace.directions n).raw.length = B

lemma initial_history (m Q B : ℕ) (move : ℝ) :
    History (Round.initial m {} []) 0 Q B move := by
  refine ⟨rfl, trivial, by simp [RetiredPast, Round.initial], by simp [Round.initial], rfl, ?_, ?_, ?_⟩
  · exact ⟨Nat.one_pos, by simp [Round.initial]⟩
  · intro k hk
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp [Round.initial]
  · simp

lemma history_publish {m K Q B : ℕ} {move : ℝ} (s privateRound : Round m)
    (hs : History s K Q B move) (hQ : 0 < Q)
    (hp : RoundInfo privateRound (K * Q) B move) (hc : privateRound.completed = Q)
    (hx : Extends s.trace privateRound.trace)
    (hmarks : privateRound.trace.markers = s.trace.markers) :
    History (publish B privateRound) (K + 1) Q B move := by
  let out := publish B privateRound
  obtain ⟨hr, hl, hret, hpub⟩ := publish_round_info privateRound hp
  change Published privateRound.trace out.trace at hpub
  have hprev := hx.trans hpub.extension
  have hcount : privateRound.trace.nextDirection = (K + 1) * Q := by
    rw [hp.forest.count, hc, Nat.add_mul, Nat.one_mul]
  obtain ⟨head, hhead, hheadMarks, hheadHistory⟩ := hpub.mark
  have hmarkers : out.trace.markers = s.trace.markers ++ [head] := hheadMarks.trans
    (congrArg (· ++ [head]) hmarks)
  have hdirs : out.trace.nextDirection = (K + 1) * Q := hpub.directionCount.trans hcount
  have hlast : out.trace.markers.getLast?.getD 0 = head := by rw [hmarkers]; simp
  change History out (K + 1) Q B move
  refine ⟨hr, hl, hret, hdirs, by simp [hmarkers, hs.markers], ?_, ?_, ?_⟩
  · rw [hlast]
    exact ⟨hhead, hheadHistory.trans (congrArg range hdirs)⟩
  · intro k hk
    by_cases hk' : k ≤ K
    · have hk'' : k < s.trace.markers.length := by rw [hs.markers]; omega
      have hmem : s.trace.markers[k]?.getD 0 ∈ s.trace.markers := by simp [hk'']
      have hb := markers_bound_run (m + 1) s.events hs.legal
      rw [hs.represented] at hb
      rw [hmarkers, List.getElem?_append_left hk'', hprev.oldState _ (hb _ hmem)]
      exact hs.history k hk'
    · have heq : k = K + 1 := by omega
      have hi : k = s.trace.markers.length := heq.trans hs.markers.symm
      have hget : (s.trace.markers ++ [head])[k]?.getD 0 = head := by simp [hi]
      rw [hmarkers, hget, heq]
      exact hheadHistory.trans (congrArg range hdirs)
  · intro n hn
    by_cases hn' : n < K * Q
    · rw [hprev.oldDirection _ (hs.directions.symm ▸ hn')]
      exact hs.direction n hn'
    · have hlo : K ≤ n / Q := (Nat.le_div_iff_mul_le hQ).2 (Nat.le_of_not_gt hn')
      have hhi : n / Q < K + 1 := (Nat.div_lt_iff_lt_mul hQ).2 hn
      have hindex : n / Q = K := by omega
      rw [hindex, hpub.directions]
      exact hp.forest.direction n (Nat.le_of_not_gt hn') (hcount.symm ▸ hn)

lemma history_round {m K Q B : ℕ} {move : ℝ} (s : Round m) (es : List (OriginalEvent m))
    (hs : History s K Q B move) (hQ : 0 < Q) (hB : 0 < B)
    (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : LegalFrom Q B move (Round.initial m s.trace s.events) es)
    (hc : (es.foldl (advance B move) (Round.initial m s.trace s.events)).completed = Q) :
    History (runRound B move (Round.initial m s.trace s.events) es) (K + 1) Q B move := by
  let root := Round.initial m s.trace s.events
  let privateRound := es.foldl (advance B move) root
  have hi : Data root (K * Q) B move := by
    have hh := hs.last.2
    rw [← hs.directions] at hh
    have h := round_initial m B move s.trace s.events hs.represented hs.legal hs.retired hs.last.1 hh
    simpa only [hs.directions] using h
  have hp : Data privateRound (K * Q) B move := run_data root es hi hB hm0 hm1 he
  obtain ⟨hx, hmarks⟩ := private_frame (B := B) move root es
  exact history_publish s privateRound hs hQ (round_info hp) hc hx hmarks

lemma history_fold {m K Q B : ℕ} {move : ℝ} (s : Round m)
    (es : List (List (OriginalEvent m))) (hs : History s K Q B move)
    (hQ : 0 < Q) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : CompleteRounds Q B move s es) :
    History (es.foldl (fun t xs => runRound B move (Round.initial m t.trace t.events) xs) s)
      (K + es.length) Q B move := by
  induction es generalizing s K with
  | nil => exact hs
  | cons e es ih =>
    obtain ⟨hle, hc, hrest⟩ := he
    have hout := history_round s e hs hQ hB hm0 hm1 hle hc
    have h := ih _ hout hrest
    simpa only [List.foldl_cons, List.length_cons, Nat.add_right_comm K 1 es.length, Nat.add_assoc] using h

lemma history_run {m Q B : ℕ} {move : ℝ} (es : List (List (OriginalEvent m)))
    (hQ : 0 < Q) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : CompleteRounds Q B move (Round.initial m {} []) es) :
    History (runRounds B move es) es.length Q B move := by
  simpa only [runRounds, zero_add] using
    history_fold (Round.initial m {} []) es (initial_history m Q B move) hQ hB hm0 hm1 he

end LongTails.Proofs.BirchCollectionLocalRounds
