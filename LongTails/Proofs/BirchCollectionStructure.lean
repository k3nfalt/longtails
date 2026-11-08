import LongTails.Proofs.BirchCollectionExecution
import LongTails.Proofs.BirchCausalMerges

namespace LongTails.Proofs.BirchCollectionStructure

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionExecution

def collectionHeader (c : Collection) : ℕ × ℕ × ℕ × ℝ × ℝ :=
  (c.owner, c.source, c.size, c.refresh, c.movement)

lemma step_old_collection (s : TraceState) (e : Event) (c : ℕ)
    (hc : c < s.nextCollection) :
    collectionHeader ((step s e).collections c) = collectionHeader (s.collections c) := by
  have hn := ne_of_lt hc
  cases e <;> simp [step, collectionHeader, Function.update_apply, hn] <;>
    split_ifs <;> simp_all

lemma step_old_collection_source (s : TraceState) (e : Event) (c : ℕ)
    (hc : c < s.nextCollection) :
    ((step s e).collections c).source = (s.collections c).source :=
  congrArg (fun h => h.2.1) (step_old_collection s e c hc)

structure Histories (s : TraceState) : Prop where
  root_exists : 0 < s.nextState
  root : (s.states 0).history = ∅
  source : ∀ c, c < s.nextCollection → (s.collections c).source < s.nextState
  state_past : ∀ a, a < s.nextState → (s.states a).history ⊆ range s.nextDirection
  state_closed : ∀ a, a < s.nextState → ∀ j, j ∈ (s.states a).history →
    (s.directions j).history ⊆ (s.states a).history
  direction : ∀ j, j < s.nextDirection →
    (s.directions j).source < s.nextState ∧
      (s.directions j).history = (s.states (s.directions j).source).history ∧
      (s.directions j).history ⊆ range j

lemma histories_initial : Histories ({} : TraceState) := by
  constructor <;> simp

lemma histories_source_step (workers : ℕ) (s : TraceState) (e : Event)
    (h : Histories s) (he : e.Valid workers s) :
    ∀ c, c < (step s e).nextCollection → ((step s e).collections c).source < (step s e).nextState := by
  intro c hc
  by_cases hold : c < s.nextCollection
  · rw [step_old_collection_source s e c hold]
    exact (h.source c hold).trans_le (step_state_mono s e)
  · cases e <;> simp only [step] at hc ⊢
    all_goals try omega
    rename_i worker source size refresh movement
    have hc' : c = s.nextCollection := by omega
    simp only [hc', Function.update_self]
    exact he.2.1

lemma histories_step (workers : ℕ) (s : TraceState) (e : Event)
    (h : Histories s) (he : e.Valid workers s) : Histories (step s e) := by
  have hroot := h.root_exists.trans_le (step_state_mono s e)
  have hsource := histories_source_step workers s e h he
  have hold (a : ℕ) (ha : a < s.nextState) :
      (step s e).states a = s.states a := step_old_state s e a ha
  have hdir (j : ℕ) (hj : j < s.nextDirection) :
      (step s e).directions j = s.directions j := step_old_direction s e j hj
  refine ⟨hroot, ?_, hsource, ?_, ?_, ?_⟩
  · rw [hold 0 h.root_exists]
    exact h.root
  · intro a ha
    by_cases hoa : a < s.nextState
    · rw [hold a hoa]
      exact (h.state_past a hoa).trans (range_mono (step_direction_mono s e))
    · cases e <;> simp only [step] at ha ⊢
      all_goals try omega
      · rename_i c
        have hae : a = s.nextState := by omega
        rw [hae, Function.update_self]
        apply insert_subset
        · simp
        · exact (h.state_past _ (h.source c he.1)).trans (range_mono (by omega))
      · rename_i w l r common
        have hae : a = s.nextState := by omega
        rw [hae, Function.update_self]
        exact union_subset (h.state_past l he.2.1) (h.state_past r he.2.2.1)
  · intro a ha j hj
    by_cases hoa : a < s.nextState
    · rw [hold a hoa] at hj ⊢
      rw [hdir j (mem_range.mp (h.state_past a hoa hj))]
      exact h.state_closed a hoa j hj
    · cases e <;> simp only [step] at ha hj ⊢
      all_goals try omega
      · rename_i c
        have hae : a = s.nextState := by omega
        simp only [hae, Function.update_self] at hj ⊢
        rcases mem_insert.mp hj with rfl | hj
        · simp only [Function.update_self]
          exact subset_insert _ _
        · have hjd := mem_range.mp (h.state_past _ (h.source c he.1) hj)
          rw [Function.update_of_ne (ne_of_lt hjd)]
          exact (h.state_closed _ (h.source c he.1) j hj).trans (subset_insert _ _)
      · rename_i w l r common
        have hae : a = s.nextState := by omega
        simp only [hae, Function.update_self] at hj ⊢
        exact LongTails.Proofs.BirchCausalMerges.closed_union
          (fun q => (s.directions q).history) _ _
          (h.state_closed l he.2.1) (h.state_closed r he.2.2.1) j hj
  · intro j hj
    by_cases hoj : j < s.nextDirection
    · rw [hdir j hoj]
      obtain ⟨hs, heq, hp⟩ := h.direction j hoj
      exact ⟨hs.trans_le (step_state_mono s e), by rw [hold _ hs]; exact heq, hp⟩
    · cases e <;> simp only [step] at hj ⊢
      all_goals try omega
      rename_i c
      have hje : j = s.nextDirection := by omega
      simp only [hje, Function.update_self]
      have hs := h.source c he.1
      refine ⟨by omega, ?_, h.state_past _ hs⟩
      rw [Function.update_of_ne (ne_of_lt hs)]

lemma histories_fold (workers : ℕ) (events : List Event) (s : TraceState)
    (h : Histories s) (hv : ValidFrom workers s events) : Histories (events.foldl step s) := by
  induction events generalizing s with
  | nil => exact h
  | cons e rest ih =>
      exact ih (step s e) (histories_step workers s e h hv.1) hv.2

lemma histories_run (workers : ℕ) (events : List Event) (hv : ValidFrom workers {} events) :
    Histories (run events) := histories_fold workers events {} histories_initial hv

lemma step_retired_mono (s : TraceState) (e : Event) : s.retired ⊆ (step s e).retired := by
  cases e <;> simp [step]

lemma step_delivered (s : TraceState) (e : Event) (c : ℕ) (hc : c < s.nextCollection) :
    ((step s e).collections c).delivered = (s.collections c).delivered ∨
      ∃ q, e = .receive q ∧ (s.raws q).collection = c ∧
        ((step s e).collections c).delivered = (s.collections c).delivered ++ [q] := by
  have hn := ne_of_lt hc
  cases e <;> simp [step, Function.update_apply, hn]
  all_goals split_ifs <;> simp_all

lemma step_closed_collection (workers : ℕ) (s : TraceState) (e : Event)
    (he : e.Valid workers s) (c : ℕ) (hc : c < s.nextCollection)
    (hclosed : (s.collections c).closed = true) :
    ((step s e).collections c).closed = true ∧
      ((step s e).collections c).delivered = (s.collections c).delivered := by
  have hn := ne_of_lt hc
  cases e <;> simp [step, Function.update_apply, hn, hclosed]
  all_goals split_ifs <;> simp_all [Event.Valid]

structure RawLedger (s : TraceState) : Prop where
  assignment : ∀ q, q < s.nextRaw → (s.raws q).collection < s.nextCollection
  delivered : ∀ c, c < s.nextCollection → (s.collections c).delivered.Nodup ∧
    ∀ q ∈ (s.collections c).delivered,
      q < s.nextRaw ∧ q ∈ s.retired ∧ (s.raws q).collection = c

lemma rawLedger_initial : RawLedger ({} : TraceState) := by
  constructor <;> simp

lemma rawLedger_step (workers : ℕ) (s : TraceState) (e : Event)
    (h : RawLedger s) (he : e.Valid workers s) : RawLedger (step s e) := by
  have hraw : s.nextRaw ≤ (step s e).nextRaw := by rw [step_raw]; omega
  have hcollection := step_collection_mono s e
  have hold (c : ℕ) (hc : c < s.nextCollection) (q : ℕ)
      (hq : q ∈ (s.collections c).delivered) :
      q < (step s e).nextRaw ∧ q ∈ (step s e).retired ∧
        ((step s e).raws q).collection = c := by
    obtain ⟨hqold, hretired, hassigned⟩ := (h.delivered c hc).2 q hq
    exact ⟨hqold.trans_le hraw, step_retired_mono s e hretired,
      by rw [step_old_raw s e q hqold]; exact hassigned⟩
  constructor
  · intro q hq
    by_cases hqold : q < s.nextRaw
    · rw [step_old_raw s e q hqold]
      exact (h.assignment q hqold).trans_le hcollection
    · cases e <;> simp only [step] at hq ⊢
      all_goals try omega
      rename_i c worker
      have hqe : q = s.nextRaw := by omega
      simp only [hqe, Function.update_self]
      exact he.1
  · intro c hc
    by_cases hcold : c < s.nextCollection
    · rcases step_delivered s e c hcold with hs | ⟨q, rfl, hqc, hs⟩
      · rw [hs]
        exact ⟨(h.delivered c hcold).1, hold c hcold⟩
      · rw [hs]
        have hnew : q ∉ (s.collections c).delivered := by
          intro hq
          exact he.2.1 ((h.delivered c hcold).2 q hq).2.1
        refine ⟨(List.nodup_append).mpr ⟨(h.delivered c hcold).1,
          by simp, ?_⟩, ?_⟩
        · intro a ha b hb
          have hbq : b = q := by simpa using hb
          subst b
          intro heq
          exact hnew (heq ▸ ha)
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hold c hcold t ht
        · have htq : t = q := by simpa using ht
          subst t
          simpa [step, hqc] using he.1
    · cases e <;> simp only [step] at hc ⊢
      all_goals try omega
      rename_i worker source size refresh movement
      have hce : c = s.nextCollection := by omega
      simp [hce]

lemma rawLedger_fold (workers : ℕ) (events : List Event) (s : TraceState)
    (h : RawLedger s) (hv : ValidFrom workers s events) : RawLedger (events.foldl step s) := by
  induction events generalizing s with
  | nil => exact h
  | cons e rest ih =>
      exact ih (step s e) (rawLedger_step workers s e h hv.1) hv.2

lemma rawLedger_run (workers : ℕ) (events : List Event) (hv : ValidFrom workers {} events) :
    RawLedger (run events) := rawLedger_fold workers events {} rawLedger_initial hv

structure CompletedLedger (s : TraceState) : Prop where
  records : ∀ j, j < s.nextDirection →
    let d := s.directions j
    let c := s.collections d.collection
    d.collection < s.nextCollection ∧ c.closed = true ∧ d.raw = c.delivered ∧
      collectionHeader c = (c.owner, d.source, d.raw.length, d.refresh, d.movement)
  distinct : ∀ i, i < s.nextDirection → ∀ j, j < s.nextDirection → i ≠ j →
    (s.directions i).collection ≠ (s.directions j).collection

lemma completedLedger_initial : CompletedLedger ({} : TraceState) := by
  constructor <;> simp

lemma completedLedger_step (workers : ℕ) (s : TraceState) (e : Event)
    (h : CompletedLedger s) (he : e.Valid workers s) : CompletedLedger (step s e) := by
  have hold (j : ℕ) (hj : j < s.nextDirection) :
      (step s e).directions j = s.directions j := step_old_direction s e j hj
  constructor
  · intro j hj
    by_cases hjold : j < s.nextDirection
    · rw [hold j hjold]
      obtain ⟨hc, hclosed, hraw, hheader⟩ := h.records j hjold
      obtain ⟨hclosed', hraw'⟩ := step_closed_collection workers s e he
        (s.directions j).collection hc hclosed
      refine ⟨hc.trans_le (step_collection_mono s e), hclosed', hraw.trans hraw'.symm, ?_⟩
      have hh := step_old_collection s e (s.directions j).collection hc
      have howner := congrArg Prod.fst hh
      simp only [collectionHeader] at howner
      rw [hh, howner]
      exact hheader
    · cases e <;> simp only [step] at hj ⊢
      all_goals try omega
      rename_i c
      have hje : j = s.nextDirection := by omega
      simp only [hje, Function.update_self]
      exact ⟨he.1, trivial, trivial, by simp [collectionHeader, he.2.2]⟩
  · intro i hi j hj hij
    by_cases hiold : i < s.nextDirection
    · rw [hold i hiold]
      by_cases hjold : j < s.nextDirection
      · rw [hold j hjold]
        exact h.distinct i hiold j hjold hij
      · cases e <;> simp only [step] at hj ⊢
        all_goals try omega
        rename_i c
        have hje : j = s.nextDirection := by omega
        simp only [hje, Function.update_self]
        intro heq
        have hc := (h.records i hiold).2.1
        rw [heq, he.2.1] at hc
        contradiction
    · by_cases hjold : j < s.nextDirection
      · rw [hold j hjold]
        cases e <;> simp only [step] at hi ⊢
        all_goals try omega
        rename_i c
        have hie : i = s.nextDirection := by omega
        simp only [hie, Function.update_self]
        intro heq
        have hc := (h.records j hjold).2.1
        rw [← heq, he.2.1] at hc
        contradiction
      · cases e <;> simp only [step] at hi hj <;> omega

lemma completedLedger_fold (workers : ℕ) (events : List Event) (s : TraceState)
    (h : CompletedLedger s) (hv : ValidFrom workers s events) :
    CompletedLedger (events.foldl step s) := by
  induction events generalizing s with
  | nil => exact h
  | cons e rest ih =>
      exact ih (step s e) (completedLedger_step workers s e h hv.1) hv.2

lemma completedLedger_run (workers : ℕ) (events : List Event) (hv : ValidFrom workers {} events) :
    CompletedLedger (run events) := completedLedger_fold workers events {} completedLedger_initial hv

lemma completed_raw (s : TraceState) (hraw : RawLedger s) (hfinish : CompletedLedger s)
    (j : ℕ) (hj : j < s.nextDirection) :
    (s.directions j).raw.Nodup ∧ ∀ q ∈ (s.directions j).raw,
      q < s.nextRaw ∧ (s.raws q).collection = (s.directions j).collection := by
  obtain ⟨hc, _, he, _⟩ := hfinish.records j hj
  rw [he]
  exact ⟨(hraw.delivered _ hc).1, fun q hq =>
    ⟨((hraw.delivered _ hc).2 q hq).1, ((hraw.delivered _ hc).2 q hq).2.2⟩⟩

lemma completed_raw_disjoint (s : TraceState) (hraw : RawLedger s) (hfinish : CompletedLedger s)
    (i j : ℕ) (hi : i < s.nextDirection) (hj : j < s.nextDirection) (hij : i ≠ j) :
    Disjoint (s.directions i).raw.toFinset (s.directions j).raw.toFinset := by
  apply disjoint_left.mpr
  intro q hqi hqj
  have hei := ((completed_raw s hraw hfinish i hi).2 q (List.mem_toFinset.mp hqi)).2
  have hej := ((completed_raw s hraw hfinish j hj).2 q (List.mem_toFinset.mp hqj)).2
  exact hfinish.distinct i hi j hj hij (hei.symm.trans hej)

def CollectionParameters (s : TraceState) : Prop :=
  ∀ c, c < s.nextCollection → 0 < (s.collections c).size ∧
    0 ≤ (s.collections c).movement ∧ (s.collections c).movement ≤ (s.collections c).refresh ∧
      (s.collections c).refresh ≤ 1

lemma collectionParameters_initial : CollectionParameters {} := by simp [CollectionParameters]

lemma collectionParameters_step (workers : ℕ) (s : TraceState) (e : Event)
    (h : CollectionParameters s) (he : e.Valid workers s) : CollectionParameters (step s e) := by
  intro c hc
  by_cases hold : c < s.nextCollection
  · have hh := step_old_collection s e c hold
    have hsize := congrArg (fun v => v.2.2.1) hh
    have hrefresh := congrArg (fun v => v.2.2.2.1) hh
    have hmovement := congrArg (fun v => v.2.2.2.2) hh
    simp only [collectionHeader] at hsize hrefresh hmovement
    rw [hsize, hrefresh, hmovement]
    exact h c hold
  · cases e <;> simp only [step] at hc ⊢
    all_goals try omega
    rename_i worker source size refresh movement
    have hce : c = s.nextCollection := by omega
    simp only [hce, Function.update_self]
    exact he.2.2

lemma collectionParameters_fold (workers : ℕ) (events : List Event) (s : TraceState)
    (h : CollectionParameters s) (he : ValidFrom workers s events) :
    CollectionParameters (events.foldl step s) := by
  induction events generalizing s with
  | nil => exact h
  | cons e rest ih => exact ih (step s e) (collectionParameters_step workers s e h he.1) he.2

lemma collectionParameters_run (workers : ℕ) (events : List Event)
    (he : ValidFrom workers {} events) : CollectionParameters (run events) :=
  collectionParameters_fold workers events {} collectionParameters_initial he

lemma direction_parameters (s : TraceState) (hp : CollectionParameters s)
    (hc : CompletedLedger s) (j : ℕ) (hj : j < s.nextDirection) :
    0 < (s.directions j).raw.length ∧ 0 ≤ (s.directions j).movement ∧
      (s.directions j).movement ≤ (s.directions j).refresh ∧ (s.directions j).refresh ≤ 1 := by
  obtain ⟨hcollection, _, _, hheader⟩ := hc.records j hj
  have hsize := congrArg (fun v => v.2.2.1) hheader
  have hrefresh := congrArg (fun v => v.2.2.2.1) hheader
  have hmovement := congrArg (fun v => v.2.2.2.2) hheader
  simp only [collectionHeader] at hsize hrefresh hmovement
  simpa only [hsize, hrefresh, hmovement] using hp _ hcollection

end LongTails.Proofs.BirchCollectionStructure
