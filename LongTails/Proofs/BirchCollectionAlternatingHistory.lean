import LongTails.Algorithms.BirchCollectionAlternating
import LongTails.Proofs.BirchCollectionNestedRounds
import LongTails.Proofs.BirchCollectionRetune

namespace LongTails.Proofs.BirchCollectionAlternatingHistory

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested (Layout)
open LongTails.Algorithms.BirchCollectionBatches (batchAndMarkWithMove)
open LongTails.Algorithms.BirchCollectionAlternating
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionNestedRounds
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionOrdering

lemma cut_succ (B k : ℕ) :
    cut B (k + 1) = cut B k + if k % 2 = 0 then 1 else B := by
  unfold cut
  split
  · rename_i h
    have hd : (k + 1) / 2 = k / 2 := by omega
    have hm : (k + 1) % 2 = 1 := by omega
    rw [hd, hm, h, add_zero]
  · rename_i h
    have hd : (k + 1) / 2 = k / 2 + 1 := by omega
    have hm : k % 2 = 1 := by omega
    have hm' : (k + 1) % 2 = 0 := by omega
    rw [hd, hm, hm', Nat.add_mul, Nat.one_mul, add_zero]
    omega

lemma cut_strict {B : ℕ} (hB : 0 < B) : StrictMono (cut B) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [cut_succ]
  split <;> omega

def Batch (B k : ℕ) := if k % 2 = 0 then B else 1

noncomputable def move (k : ℕ) : ℝ := if k % 2 = 0 then 1 / 2 else 1 / 4

structure History {m : ℕ} (s : Round m) (B K : ℕ) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  count : s.trace.nextDirection = cut B K
  markers : s.trace.markers.length = K + 1
  last : s.trace.markers.getLast?.getD 0 < s.trace.nextState ∧
    (s.trace.states (s.trace.markers.getLast?.getD 0)).history = range (cut B K)
  mark : ∀ k ≤ K, (s.trace.states (s.trace.markers[k]?.getD 0)).history = range (cut B k)
  direction : ∀ k < K, ∀ n ∈ Ico (cut B k) (cut B (k + 1)),
    range (cut B k) ⊆ (s.trace.directions n).history ∧
    (s.trace.directions n).history ⊆ range n ∧
    (s.trace.directions n).movement = move k ∧ (s.trace.directions n).raw.length = Batch B k

lemma reset_block {m B : ℕ} {move : ℝ} (s : Round m) (hB : 0 < B)
    (hm0 : 0 ≤ move) (hm1 : move ≤ 1) (hr : run s.events = s.trace)
    (hl : ValidFrom (m + 1) {} s.events) (hs : RetiredPast s.trace)
    (hb : s.trace.markers.getLast?.getD 0 < s.trace.nextState)
    (hh : (s.trace.states (s.trace.markers.getLast?.getD 0)).history = range s.trace.nextDirection) :
    BlockEffect s (s.append (batchAndMarkWithMove s.trace 0 (s.trace.markers.getLast?.getD 0)
      (List.replicate B 0) move)) 1 B move := by
  let source := s.trace.markers.getLast?.getD 0
  let events := batchAndMarkWithMove s.trace 0 source (List.replicate B 0) move
  let t := s.append events
  obtain ⟨he, hb'⟩ := batch_and_mark_with_move (m + 1) s.trace 0 source
    (List.replicate B 0) move hm0 hm1 hs (Nat.zero_lt_succ _) hb
    (by simpa using hB) (by simp) (by rfl) hb
  change ValidFrom (m + 1) s.trace events at he
  change BatchEffect s.trace t.trace 0 source (List.replicate B 0).length move at hb'
  have hr' : run t.events = t.trace := by
    change run (s.events ++ events) = events.foldl step s.trace
    rw [run, List.foldl_append]
    exact congrArg (events.foldl step) hr
  have hl' : ValidFrom (m + 1) {} t.events :=
    by
    apply (valid_append _ _ _ _).2
    refine ⟨hl, ?_⟩
    change ValidFrom (m + 1) (run s.events) events
    rwa [hr]
  refine ⟨hr', hl', retired_past_fold _ _ _ hs he, extends_fold _ _, hb'.directionCount, ?_, ?_⟩
  · refine ⟨s.trace.nextState, ?_, hb'.markers, ?_⟩
    · rw [hb'.stateCount]
      exact Nat.lt_succ_self _
    · rw [hb'.state]
      change insert s.trace.nextDirection (s.trace.states source).history = _
      rw [hh, hb'.directionCount]
      ext n
      simp only [mem_insert, mem_range]
      omega
  · intro n hlo hhi
    rw [hb'.directionCount] at hhi
    have hn : n = s.trace.nextDirection := by omega
    subst n
    rw [hb'.direction]
    change range s.trace.nextDirection ⊆ (s.trace.states source).history ∧
      (s.trace.states source).history ⊆ range s.trace.nextDirection ∧
      (1 : ℝ) = 1 ∧ move = move ∧ (List.range' s.trace.nextRaw (List.replicate B 0).length).length = B
    rw [hh]
    simp

lemma extend_history {m B K Q b : ℕ} {w : ℝ} {s t : Round m} (hs : History s B K)
    (ht : BlockEffect s t Q b w) (hB : 0 < B)
    (hcut : cut B (K + 1) = cut B K + Q) (hb : b = Batch B K) (hw : w = move K) :
    History t B (K + 1) := by
  have hcount : t.trace.nextDirection = cut B (K + 1) := by rw [ht.count, hs.count, hcut]
  obtain ⟨head, hhead, hm, hh⟩ := ht.mark
  refine ⟨ht.represented, ht.legal, ht.retired, hcount, by simp [hm, hs.markers], ?_, ?_, ?_⟩
  · rw [show t.trace.markers.getLast?.getD 0 = head by simp [hm]]
    exact ⟨hhead, hh.trans (congrArg range hcount)⟩
  · intro k hk
    by_cases h : k ≤ K
    · have hi : k < s.trace.markers.length := by rw [hs.markers]; omega
      have hmem : s.trace.markers[k]?.getD 0 ∈ s.trace.markers := by simp [hi]
      have hb' := markers_bound_run (m + 1) s.events hs.legal
      rw [hs.represented] at hb'
      rw [hm, List.getElem?_append_left hi, ht.extension.oldState _ (hb' _ hmem)]
      exact hs.mark k h
    · have hk' : k = K + 1 := by omega
      rw [hm, hk', show K + 1 = s.trace.markers.length from hs.markers.symm]
      simp only [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      exact hh.trans (congrArg range (by rw [hcount, hs.markers]))
  · intro k hk n hn
    obtain ⟨hnl, hnu⟩ := mem_Ico.mp hn
    by_cases h : k < K
    · have hn' : n < s.trace.nextDirection := by
        rw [hs.count]
        exact hnu.trans_le ((cut_strict hB).monotone (by omega))
      rw [ht.extension.oldDirection _ hn']
      exact hs.direction k h n hn
    · have hk' : k = K := by omega
      subst k
      obtain ⟨ha, hp, _, hm', hb'⟩ := ht.direction n (hs.count.symm ▸ hnl) (hcount.symm ▸ hnu)
      exact ⟨hs.count ▸ ha, hp, hm'.trans hw, hb'.trans hb⟩

lemma rounds_history {m B : ℕ} (layout : Layout m) (orders : ℕ → List (Fin m))
    (hB : 0 < B) (K : ℕ) (ho : ∀ k < K, k % 2 ≠ 0 → (orders k).length = B) :
    History (rounds layout B orders K) B K := by
  induction K with
  | zero =>
    refine ⟨rfl, trivial, by simp [RetiredPast, rounds, Round.initial], by simp [rounds, Round.initial, cut], rfl, ?_, ?_, ?_⟩
    · exact ⟨Nat.one_pos, by simp [rounds, Round.initial, cut]⟩
    · intro k hk
      have : k = 0 := by omega
      subst k
      simp [rounds, Round.initial, cut]
    · simp
  | succ k ih =>
    let s := rounds layout B orders k
    have hs : History s B k := ih (fun n hn => ho n (by omega))
    have hh := hs.last.2
    rw [← hs.count] at hh
    by_cases h : k % 2 = 0
    · simp only [rounds, stepRound, h, ite_true]
      exact extend_history hs (reset_block s hB (by norm_num) (by norm_num)
        hs.represented hs.legal hs.retired hs.last.1 hh) hB
        (by simp [cut_succ, h]) (by simp [Batch, h]) (by simp [move, h])
    · simp only [rounds, stepRound, h, ite_false]
      exact extend_history hs (nested_block layout s (orders k) hs.represented hs.legal hs.retired
        hs.last.1 hh Nat.one_pos (by norm_num) (by norm_num) (ho k (by omega) h)) hB
        (by simp [cut_succ, h]) (by simp [Batch, h]) (by simp [move, h])

end LongTails.Proofs.BirchCollectionAlternatingHistory
