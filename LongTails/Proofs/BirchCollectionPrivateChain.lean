import LongTails.Proofs.BirchCollectionPrivatePacket
import LongTails.Proofs.BirchCollectionPublication

namespace LongTails.Proofs.BirchCollectionPrivateChain

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionPrivatePacket
open LongTails.Proofs.BirchCollectionPublication

structure Chain (s : TraceState) (base head : ℕ) (labels : List ℕ) (B : ℕ) (move : ℝ) : Prop where
  baseBound : base < s.nextState
  headBound : head < s.nextState
  nodup : labels.Nodup
  bounded : ∀ d ∈ labels, d < s.nextDirection
  history : (s.states head).history = (s.states base).history ∪ labels.toFinset
  direction : ∀ n (hn : n < labels.length),
    let d := s.directions labels[n]
    d.history = (s.states base).history ∪ (labels.take n).toFinset ∧
      d.refresh = 1 ∧ d.movement = move ∧ d.raw.length = B

lemma chain_initial (s : TraceState) (base B : ℕ) (move : ℝ) (hb : base < s.nextState) :
    Chain s base base [] B move := by
  refine ⟨hb, hb, List.nodup_nil, by simp, by simp, ?_⟩
  intro n hn
  simp at hn

lemma Chain.extend {s t : TraceState} {base head B : ℕ} {move : ℝ} {labels : List ℕ}
    (h : Chain s base head labels B move) (he : Extends s t) : Chain t base head labels B move := by
  refine ⟨h.baseBound.trans_le he.stateCount, h.headBound.trans_le he.stateCount, h.nodup,
    fun d hd => (h.bounded d hd).trans_le he.directionCount, ?_, ?_⟩
  · rw [he.oldState _ h.headBound, he.oldState _ h.baseBound]
    exact h.history
  · intro n hn
    change (t.directions labels[n]).history = (t.states base).history ∪ (labels.take n).toFinset ∧
      (t.directions labels[n]).refresh = 1 ∧ (t.directions labels[n]).movement = move ∧
      (t.directions labels[n]).raw.length = B
    rw [he.oldState _ h.baseBound, he.oldDirection _ (h.bounded _ (List.getElem_mem hn))]
    exact h.direction n hn

lemma finish_extends {s t : TraceState} {c first owner source B : ℕ} {move : ℝ}
    (h : FinishData s t c first owner source B move) : Extends s t :=
  ⟨h.nextState.symm ▸ Nat.le_succ _, h.nextDirection.symm ▸ Nat.le_succ _,
    h.oldState, h.oldDirection, h.nextRaw.ge⟩

lemma chain_finish {s t : TraceState} {base head c first owner B : ℕ} {move : ℝ} {labels : List ℕ}
    (h : Chain s base head labels B move) (hf : FinishData s t c first owner head B move) :
    Chain t base s.nextState (labels ++ [s.nextDirection]) B move := by
  let d := s.nextDirection
  have hlt : d ∉ labels := fun hd => Nat.lt_irrefl d (h.bounded d hd)
  have hn : (labels ++ [d]).Nodup := by
    rw [List.nodup_append]
    exact ⟨h.nodup, by simp, fun j hj k hk => by
      have he : k = d := by simpa using hk
      subst k
      exact fun h => hlt (h ▸ hj)⟩
  have hb : ∀ j ∈ labels ++ [d], j < t.nextDirection := by
    intro j hj
    rw [hf.nextDirection]
    rcases List.mem_append.mp hj with hj | hj
    · exact (h.bounded j hj).trans (Nat.lt_succ_self _)
    · have he : j = d := by simpa using hj
      exact he.symm ▸ Nat.lt_succ_self _
  have hbase := hf.oldState base h.baseBound
  refine ⟨h.baseBound.trans_le (finish_extends hf).stateCount, hf.nextState.symm ▸ Nat.lt_succ_self _,
    hn, hb, ?_, ?_⟩
  · rw [hf.newState, hbase, h.history]
    ext q
    have hsingle : ([s.nextDirection] : List ℕ).toFinset = {s.nextDirection} := by simp
    simp only [mem_insert, mem_union, List.toFinset_append, hsingle, mem_singleton]
    tauto
  · intro n hn
    by_cases hbefore : n < labels.length
    · have hget : (labels ++ [d])[n]'hn = labels[n] := List.getElem_append_left hbefore
      have htake : (labels ++ [d]).take n = labels.take n :=
        List.take_append_of_le_length hbefore.le
      have hd : t.directions ((labels ++ [d])[n]'hn) = s.directions labels[n] := by
        rw [hget, hf.oldDirection _ (h.bounded _ (List.getElem_mem hbefore))]
      let direction := t.directions ((labels ++ [d])[n]'hn)
      change direction.history = (t.states base).history ∪ ((labels ++ [d]).take n).toFinset ∧
        direction.refresh = 1 ∧ direction.movement = move ∧ direction.raw.length = B
      dsimp only [direction]
      rw [hd, htake, hbase]
      exact h.direction n hbefore
    · have hlast : n = labels.length := by
        simp only [List.length_append, List.length_singleton] at hn
        omega
      subst n
      have hget : (labels ++ [d])[labels.length]'hn = d := by simp
      have htake : (labels ++ [d]).take labels.length = labels := by simp
      let direction := t.directions ((labels ++ [d])[labels.length]'hn)
      change direction.history = (t.states base).history ∪ ((labels ++ [d]).take labels.length).toFinset ∧
        direction.refresh = 1 ∧ direction.movement = move ∧ direction.raw.length = B
      dsimp only [direction]
      rw [hget, htake, hbase]
      change (t.directions s.nextDirection).history = _ ∧
        (t.directions s.nextDirection).refresh = 1 ∧
        (t.directions s.nextDirection).movement = move ∧ (t.directions s.nextDirection).raw.length = B
      rw [hf.newDirection]
      exact ⟨h.history, rfl, rfl, List.length_range'⟩

lemma Chain.merge_history {s : TraceState} {base head main B : ℕ} {move : ℝ} {labels : List ℕ}
    (h : Chain s base head labels B move)
    (hsub : (s.states base).history ⊆ (s.states main).history)
    (hsep : Disjoint labels.toFinset (s.states main).history) :
    (s.states base).history = (s.states main).history ∩ (s.states head).history ∧
      (s.states main).history ∪ (s.states head).history =
        (s.states main).history ∪ labels.toFinset := by
  rw [h.history]
  constructor
  · ext q
    simp only [mem_inter, mem_union]
    constructor
    · intro h
      exact ⟨hsub h, Or.inl h⟩
    · rintro ⟨hm, hb | hd⟩
      · exact hb
      · exact (disjoint_left.mp hsep hd hm).elim
  · ext q
    simp only [mem_union]
    constructor
    · rintro (hm | hb | hd)
      · exact Or.inl hm
      · exact Or.inl (hsub hb)
      · exact Or.inr hd
    · rintro (hm | hd)
      · exact Or.inl hm
      · exact Or.inr (Or.inr hd)

end LongTails.Proofs.BirchCollectionPrivateChain
