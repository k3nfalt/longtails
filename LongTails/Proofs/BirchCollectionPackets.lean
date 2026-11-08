import LongTails.Proofs.BirchCollectionBatches

namespace LongTails.Proofs.BirchCollectionPackets

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionExecution

structure IssueData (s t : TraceState) (c w count : ℕ) : Prop where
  nextRaw : t.nextRaw = s.nextRaw + count
  fields : t = { s with raws := t.raws, nextRaw := t.nextRaw }
  oldRaw : ∀ q < s.nextRaw, t.raws q = s.raws q
  newRaw : ∀ q ∈ List.range' s.nextRaw count, t.raws q = { collection := c, worker := w }

lemma issue_data (workers : ℕ) (s : TraceState) (c w count : ℕ)
    (h : (Event.issue c w).Valid workers s) :
    let events := List.replicate count (Event.issue c w)
    ValidFrom workers s events ∧ IssueData s (events.foldl step s) c w count := by
  induction count generalizing s with
  | zero => exact ⟨trivial, ⟨by simp, rfl, fun _ _ => rfl, by simp⟩⟩
  | succ count ih =>
    let t := step s (.issue c w)
    obtain ⟨hv, he⟩ := ih t h
    let u := (List.replicate count (Event.issue c w)).foldl step t
    change ValidFrom workers s (.issue c w :: List.replicate count (.issue c w)) ∧
      IssueData s u c w (count + 1)
    change IssueData t u c w count at he
    have hcount : u.nextRaw = s.nextRaw + (count + 1) := by
      rw [he.nextRaw]
      change s.nextRaw + 1 + count = _
      omega
    refine ⟨⟨h, hv⟩, ⟨hcount, ?_, ?_, ?_⟩⟩
    · rw [he.fields]
      rfl
    · intro q hq
      rw [he.oldRaw q (hq.trans (Nat.lt_succ_self _))]
      simp [t, step, Nat.ne_of_lt hq]
    · intro q hq
      rw [List.range'_succ] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [he.oldRaw _ (Nat.lt_succ_self _)]
        simp [t, step]
      · exact he.newRaw q hq

structure ReceiveData (s t : TraceState) (c : ℕ) (qs : List ℕ) : Prop where
  fields : t = {s with collections := t.collections, retired := t.retired}
  retired : t.retired = s.retired ∪ qs.toFinset
  collection : t.collections c =
    {s.collections c with delivered := (s.collections c).delivered ++ qs}
  other : ∀ i ≠ c, t.collections i = s.collections i

lemma receive_data (workers : ℕ) (s : TraceState) (c : ℕ) (qs : List ℕ)
    (hopen : (s.collections c).closed = false) (hn : qs.Nodup)
    (hq : ∀ q ∈ qs, q < s.nextRaw ∧ q ∉ s.retired ∧ (s.raws q).collection = c) :
    let events := qs.map Event.receive
    ValidFrom workers s events ∧ ReceiveData s (events.foldl step s) c qs := by
  induction qs generalizing s with
  | nil => exact ⟨trivial, ⟨rfl, by simp, by simp, fun _ _ => rfl⟩⟩
  | cons q qs ih =>
    obtain ⟨hqr, hqf, hqc⟩ := hq q (by simp)
    let t := step s (.receive q)
    have he : (Event.receive q).Valid workers s := ⟨hqr, hqf, hqc.symm ▸ hopen⟩
    have ht : t.collections c =
        {s.collections c with delivered := (s.collections c).delivered ++ [q]} := by
      simp [t, step, hqc]
    have hother (i : ℕ) (hi : i ≠ c) : t.collections i = s.collections i := by
      simp [t, step, hqc, Function.update_of_ne hi]
    have hret : t.retired = insert q s.retired := rfl
    have hpred (j : ℕ) (hj : j ∈ qs) :
        j < t.nextRaw ∧ j ∉ t.retired ∧ (t.raws j).collection = c := by
      obtain ⟨hj1, hj2, hj3⟩ := hq j (List.mem_cons_of_mem _ hj)
      exact ⟨hj1, fun h => (mem_insert.mp h).elim
        (fun e => (List.nodup_cons.mp hn).1 (e ▸ hj)) hj2, hj3⟩
    obtain ⟨hv, hd⟩ := ih t (by rw [ht]; exact hopen) (List.nodup_cons.mp hn).2 hpred
    let u := (qs.map Event.receive).foldl step t
    change ReceiveData t u c qs at hd
    change ValidFrom workers s (.receive q :: qs.map Event.receive) ∧ ReceiveData s u c (q :: qs)
    refine ⟨⟨he, hv⟩, ⟨?_, ?_, ?_, fun i hi => (hd.other i hi).trans (hother i hi)⟩⟩
    · rw [hd.fields]
      rfl
    · rw [hd.retired, hret]
      ext j
      simp only [List.toFinset_cons, mem_union, mem_insert]
      tauto
    · rw [hd.collection, ht]
      simp [List.append_assoc]

lemma discard_data (workers : ℕ) (s : TraceState) (qs : List ℕ)
    (hn : qs.Nodup) (hq : ∀ q ∈ qs, q < s.nextRaw ∧ q ∉ s.retired) :
    let events := qs.map Event.discard
    let t := events.foldl step s
    ValidFrom workers s events ∧ t = {s with retired := s.retired ∪ qs.toFinset} := by
  induction qs generalizing s with
  | nil => exact ⟨trivial, by simp⟩
  | cons q qs ih =>
    let t := step s (.discard q)
    have hret : t.retired = insert q s.retired := rfl
    have hpred (j : ℕ) (hj : j ∈ qs) : j < t.nextRaw ∧ j ∉ t.retired := by
      obtain ⟨hj1, hj2⟩ := hq j (List.mem_cons_of_mem _ hj)
      exact ⟨hj1, fun h => (mem_insert.mp h).elim
        (fun e => (List.nodup_cons.mp hn).1 (e ▸ hj)) hj2⟩
    obtain ⟨hv, hd⟩ := ih t (List.nodup_cons.mp hn).2 hpred
    change ValidFrom workers s (.discard q :: qs.map Event.discard) ∧
      (qs.map Event.discard).foldl step t = _
    refine ⟨⟨hq q (by simp), hv⟩, ?_⟩
    rw [hd]
    have hf : t.retired ∪ qs.toFinset = s.retired ∪ (q :: qs).toFinset := by
      rw [hret]
      ext j
      simp only [List.toFinset_cons, mem_union, mem_insert]
      tauto
    rw [hf]
    rfl

end LongTails.Proofs.BirchCollectionPackets
