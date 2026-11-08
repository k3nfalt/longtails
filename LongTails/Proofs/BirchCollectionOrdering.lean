import LongTails.Proofs.BirchCollectionStructure

namespace LongTails.Proofs.BirchCollectionOrdering

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure

lemma markers_bound_step (workers : ℕ) (s : TraceState) (e : Event)
    (he : e.Valid workers s) (h : ∀ a ∈ s.markers, a < s.nextState) :
    ∀ a ∈ (step s e).markers, a < (step s e).nextState := by
  have hm := step_state_mono s e
  cases e with
  | mark source =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact h a ha
      · have hae : a = source := by simpa using ha
        simpa only [hae, step] using he.1
  | _ => simpa only [step] using fun a ha => (h a ha).trans_le hm

lemma markers_bound_fold (workers : ℕ) (events : List Event) (s : TraceState)
    (hv : ValidFrom workers s events) (h : ∀ a ∈ s.markers, a < s.nextState) :
    ∀ a ∈ (events.foldl step s).markers, a < (events.foldl step s).nextState := by
  induction events generalizing s with
  | nil => exact h
  | cons e rest ih =>
      exact ih (step s e) hv.2 (markers_bound_step workers s e hv.1 h)

lemma markers_bound_run (workers : ℕ) (events : List Event) (hv : ValidFrom workers {} events) :
    ∀ a ∈ (run events).markers, a < (run events).nextState :=
  markers_bound_fold workers events {} hv (by simp)

lemma label_eq_getElem (o : LongTails.Setups.BirchCollections.Ordering) (n : ℕ) (hn : n < o.labels.length) :
    o.label n = o.labels[n] := by simp [Ordering.label, hn]

lemma label_injective (o : LongTails.Setups.BirchCollections.Ordering) (h : o.labels.Nodup) :
    Set.InjOn o.label (Set.Iio o.labels.length) := by
  intro i hi j hj he
  rw [label_eq_getElem o i hi, label_eq_getElem o j hj] at he
  exact h.getElem_inj_iff.mp he

lemma ordering_history_mem (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (n q : ℕ)
    (hn : n < o.labels.length) :
    q ∈ o.history s n ↔ q < o.labels.length ∧ o.label q ∈ (s.directions (o.label n)).history := by
  simp [Ordering.history, hn]

lemma ordering_history_closed (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (K : ℕ)
    (h : Histories s) (ho : o.Valid s K) :
    ∀ n q, q ∈ o.history s n → o.history s q ⊆ o.history s n := by
  obtain ⟨_, _, _, _, _, _, hlabel, _, hpast⟩ := ho
  intro n q hq
  by_cases hn : n < o.labels.length
  · obtain ⟨hqN, hqhistory⟩ := (ordering_history_mem s o n q hn).mp hq
    obtain ⟨hs, heq, _⟩ := h.direction (o.label n) (hlabel n hn)
    intro i hi
    obtain ⟨hiN, hihistory⟩ := (ordering_history_mem s o q i hqN).mp hi
    apply (ordering_history_mem s o n i hn).mpr
    refine ⟨hiN, ?_⟩
    rw [heq] at hqhistory ⊢
    exact h.state_closed _ hs _ hqhistory hihistory
  · have hqn : q < n := by simpa [Ordering.history, hn] using hq
    simpa [Ordering.history, hn] using (hpast q).trans (range_mono hqn.le)

lemma ordering_final_history (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (K : ℕ)
    (ho : o.Valid s K) :
    (s.states (s.markers[K]?.getD 0)).history = (range o.labels.length).image o.label := by
  obtain ⟨_, _, _, _, hend, _, _, hmarkers, _⟩ := ho
  simpa only [hend] using hmarkers K le_rfl

lemma ordering_query_history (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (K : ℕ)
    (h : Histories s) (ho : o.Valid s K)
    (hm : ∀ a ∈ s.markers, a < s.nextState) (n : ℕ) (hn : n < o.labels.length) :
    (s.directions (o.label n)).history = (o.history s n).image o.label := by
  have hlen := ho.2.2.1
  have hK : K < s.markers.length := by omega
  have hlast : s.markers[K]?.getD 0 ∈ s.markers := by
    simp [hK]
  have hfinal := ordering_final_history s o K ho
  have hnin : o.label n ∈ (s.states (s.markers[K]?.getD 0)).history := by
    rw [hfinal]
    exact mem_image.mpr ⟨n, mem_range.mpr hn, rfl⟩
  apply Subset.antisymm
  · intro q hq
    have hqfinal := h.state_closed _ (hm _ hlast) _ hnin hq
    rw [hfinal] at hqfinal
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hqfinal
    exact mem_image.mpr ⟨j,
      (ordering_history_mem s o n j hn).mpr ⟨mem_range.mp hj, hq⟩, rfl⟩
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
    exact ((ordering_history_mem s o n j hn).mp hj).2

lemma ordering_raw_disjoint (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (K : ℕ)
    (hraw : RawLedger s) (hc : CompletedLedger s) (ho : o.Valid s K) :
    ((range o.labels.length : Finset ℕ) : Set ℕ).PairwiseDisjoint (o.raw s) := by
  obtain ⟨_, hnodup, _, _, _, _, hlabel, _, _⟩ := ho
  intro i hi j hj hij
  have hiN : i < o.labels.length := mem_range.mp hi
  have hjN : j < o.labels.length := mem_range.mp hj
  exact completed_raw_disjoint s hraw hc _ _ (hlabel i hiN) (hlabel j hjN)
    (fun he => hij (label_injective o hnodup hiN hjN he))

lemma ordering_raw_subset (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (K : ℕ)
    (hraw : RawLedger s) (hc : CompletedLedger s) (ho : o.Valid s K)
    (j : ℕ) (hj : j < o.labels.length) : o.raw s j ⊆ range s.nextRaw := by
  obtain ⟨_, _, _, _, _, _, hlabel, _, _⟩ := ho
  intro q hq
  exact mem_range.mpr (((completed_raw s hraw hc _ (hlabel j hj)).2 q
    (List.mem_toFinset.mp hq)).1)

lemma ordering_raw_ledger (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (K : ℕ)
    (hraw : RawLedger s) (hc : CompletedLedger s) (ho : o.Valid s K) :
    s.nextRaw = (∑ j ∈ range o.labels.length, (o.raw s j).card) +
      (s.nextRaw - ((range o.labels.length).biUnion (o.raw s)).card) := by
  have hsub : (range o.labels.length).biUnion (o.raw s) ⊆ range s.nextRaw := by
    intro q hq
    obtain ⟨j, hj, hq⟩ := mem_biUnion.mp hq
    exact ordering_raw_subset s o K hraw hc ho j (mem_range.mp hj) hq
  have hcard := card_le_card hsub
  rw [card_range] at hcard
  have he := card_biUnion (ordering_raw_disjoint s o K hraw hc ho)
  omega

end LongTails.Proofs.BirchCollectionOrdering
