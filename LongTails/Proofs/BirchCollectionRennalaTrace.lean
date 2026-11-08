import LongTails.Proofs.BirchCollectionRennalaLedger
import LongTails.Proofs.BirchCollectionBatches

namespace LongTails.Proofs.BirchCollectionRennalaTrace

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionRennala
open LongTails.Proofs.BirchCollectionRennalaLedger
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure

local notation "OEvent" => LongTails.Algorithms.BirchNonEuclideanRennala.Event
local notation "Enabled" => LongTails.Algorithms.BirchNonEuclideanRennala.Event.Enabled
local notation "ostep" => LongTails.Algorithms.BirchNonEuclideanRennala.step
local notation "Invariant" => LongTails.Proofs.BirchNonEuclideanRennalaScheduling.Invariant

open LongTails.Proofs.BirchNonEuclideanRennalaScheduling (invariant_initial step_invariant)

structure MainData (s : TraceState) (B rounds : ℕ) : Prop where
  states : s.nextState = rounds + 1
  directions : s.nextDirection = rounds
  markers : s.markers = List.range (rounds + 1)
  history : ∀ k ≤ rounds, (s.states k).history = range k
  direction : ∀ k < rounds, (s.directions k).source = k ∧ (s.directions k).target = k + 1 ∧
    (s.directions k).history = range k ∧ (s.directions k).refresh = 1 ∧
    (s.directions k).movement = 1 ∧ (s.directions k).raw.length = B

structure ActiveData (s : TraceState) (c B round batch : ℕ) : Prop where
  existsCollection : c < s.nextCollection
  openCollection : (s.collections c).closed = false
  source : (s.collections c).source = round
  size : (s.collections c).size = B
  count : (s.collections c).delivered.length = batch
  refresh : (s.collections c).refresh = 1
  movement : (s.collections c).movement = 1

structure PendingData (s : TraceState) (q worker source : ℕ) : Prop where
  existsRaw : q < s.nextRaw
  freshRaw : q ∉ s.retired
  existsCollection : (s.raws q).collection < s.nextCollection
  source : (s.collections (s.raws q).collection).source = source
  worker : (s.raws q).worker = worker

structure Data {m : ℕ} (K B : ℕ) (s : Translation m) : Prop where
  schedule : Invariant K B s.original
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  main : MainData s.trace B s.original.round
  active : s.original.round < K → ActiveData s.trace s.active B s.original.round s.original.batch
  pending : ∀ w ∈ s.original.ready,
    PendingData s.trace (s.raw w) (w.val + 1) (s.original.source w)
  fresh : ∀ w ∈ s.original.ready, s.original.round < K → s.original.source w = s.original.round →
    (s.trace.raws (s.raw w)).collection = s.active
  distinct : ∀ w ∈ s.original.ready, ∀ v ∈ s.original.ready, w ≠ v → s.raw w ≠ s.raw v

lemma data_initial (m K B : ℕ) (hK : 0 < K) (hB : 0 < B) :
    Data K B (initial m B) := by
  refine ⟨invariant_initial K B hK hB, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initial, ValidFrom, Event.Valid, hB]
  · simp [RetiredPast, initial, step]
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro k hk
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      rfl
    · intro k hk
      exact (Nat.not_lt_zero _ hk).elim
  · intro _
    constructor <;> simp [initial, step]
  · simp [initial]
  · simp [initial]

  · simp [initial]

lemma legal_advance {m K B : ℕ} (s : Translation m) (e : OEvent m) (hs : Data K B s)
    (he : ValidFrom (m + 1) s.trace (emissions K B s e)) :
    ValidFrom (m + 1) {} (advance K B s e).events := by
  apply (valid_append _ _ _ _).2
  refine ⟨hs.legal, ?_⟩
  change ValidFrom (m + 1) (run s.events) _
  rw [hs.represented]
  exact he

structure IssueEffect (s t : TraceState) (worker source : ℕ) : Prop where
  rawCount : t.nextRaw = s.nextRaw + 1
  retired : t.retired = s.retired
  stateCount : t.nextState = s.nextState
  directionCount : t.nextDirection = s.nextDirection
  states : t.states = s.states
  directions : t.directions = s.directions
  markers : t.markers = s.markers
  collectionCount : s.nextCollection ≤ t.nextCollection
  oldCollection : ∀ c < s.nextCollection, t.collections c = s.collections c
  oldRaw : ∀ q < s.nextRaw, t.raws q = s.raws q
  newRaw : PendingData t s.nextRaw worker source

lemma issue_effect {m K B : ℕ} (s : Translation m) (w : Fin m) (hs : Data K B s) :
    let events := emissions K B s (.query w)
    ValidFrom (m + 1) s.trace events ∧
      IssueEffect s.trace (events.foldl step s.trace) (w.val + 1) (s.original.source w) := by
  have hw : w.val + 1 < m + 1 := Nat.succ_lt_succ w.isLt
  have hr : s.trace.nextRaw ∉ s.trace.retired := fun h =>
    Nat.lt_irrefl _ (mem_range.mp (hs.retired h))
  simp only [emissions]
  split
  · rename_i hf
    have ha := hs.active hf.1
    refine ⟨⟨⟨ha.existsCollection, hw, ha.openCollection⟩, trivial⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, fun _ _ => rfl, ?_, ?_⟩⟩
    · intro q hq
      simp [step, Nat.ne_of_lt hq]
    · refine ⟨Nat.lt_succ_self _, hr, ?_, ?_, ?_⟩
      · simpa [step] using ha.existsCollection
      · simpa [step, hf.2] using ha.source
      · simp [step]
  · let capture := Event.capture 0 (s.original.source w) 1 1 0
    let t := step s.trace capture
    let u := step t (.issue s.trace.nextCollection (w.val + 1))
    let v := step u (.cancel s.trace.nextCollection)
    have hsource : s.original.source w < s.trace.nextState := by
      rw [hs.main.states]
      exact Nat.lt_succ_of_le (hs.schedule.source_le w)
    have hopen : (t.collections s.trace.nextCollection).closed = false := by
      simp [t, capture, step]
    change ValidFrom (m + 1) s.trace
        [capture, .issue s.trace.nextCollection (w.val + 1), .cancel s.trace.nextCollection] ∧
      IssueEffect s.trace v (w.val + 1) (s.original.source w)
    refine ⟨⟨⟨Nat.zero_lt_succ _, hsource, Nat.one_pos, le_rfl, zero_le_one, le_rfl⟩,
      ⟨Nat.lt_succ_self _, hw, hopen⟩, ⟨Nat.lt_succ_self _, hopen⟩, trivial⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_succ _, ?_, ?_, ?_⟩⟩
    · intro c hc
      simp [v, u, t, capture, step, Nat.ne_of_lt hc]
    · intro q hq
      simp [v, u, t, capture, step, Nat.ne_of_lt hq]
    · refine ⟨Nat.lt_succ_self _, hr, ?_, ?_, ?_⟩ <;> simp [v, u, t, capture, step]

lemma data_query {m K B : ℕ} (s : Translation m) (w : Fin m) (hs : Data K B s)
    (he : Enabled s.original (.query w)) : Data K B (advance K B s (.query w)) := by
  let out := advance K B s (.query w)
  obtain ⟨hv, hx⟩ := issue_effect s w hs
  change IssueEffect s.trace out.trace (w.val + 1) (s.original.source w) at hx
  have ha : out.active = s.active := by
    simp [out, advance, LongTails.Algorithms.BirchNonEuclideanRennala.step]
  have hr : out.original.round = s.original.round := rfl
  have hready (v : Fin m) : v ∈ out.original.ready ↔ v = w ∨ v ∈ s.original.ready := mem_insert
  have hraw (v : Fin m) : out.raw v = Function.update s.raw w s.trace.nextRaw v := rfl
  have hbatch : out.original.batch = s.original.batch := rfl
  change Data K B out
  refine ⟨step_invariant K B _ _ hs.schedule he, advance_represented K B s _ hs.represented,
    legal_advance s _ hs hv, retired_past_fold _ _ _ hs.retired hv, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hx.stateCount.trans hs.main.states, hx.directionCount.trans hs.main.directions,
      hx.markers.trans hs.main.markers,
      fun k hk => by rw [hx.states]; exact hs.main.history k hk,
      fun k hk => by rw [hx.directions]; exact hs.main.direction k hk⟩
  · intro hk
    have ho := hs.active (hr ▸ hk)
    rw [ha, hr, hbatch]
    refine ⟨ho.existsCollection.trans_le hx.collectionCount, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [hx.oldCollection _ ho.existsCollection]
    · exact ho.openCollection
    · exact ho.source
    · exact ho.size
    · exact ho.count
    · exact ho.refresh
    · exact ho.movement
  · intro v hv
    rcases (hready v).1 hv with rfl | hv
    · rw [hraw, Function.update_self]
      exact hx.newRaw
    · have hne : v ≠ w := fun h => he.2 (h ▸ hv)
      have hp := hs.pending v hv
      rw [hraw, Function.update_of_ne hne]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hx.rawCount]
        exact hp.existsRaw.trans (Nat.lt_succ_self _)
      · rw [hx.retired]
        exact hp.freshRaw
      · rw [hx.oldRaw _ hp.existsRaw]
        exact hp.existsCollection.trans_le hx.collectionCount
      · rw [hx.oldRaw _ hp.existsRaw, hx.oldCollection _ hp.existsCollection]
        exact hp.source
      · rw [hx.oldRaw _ hp.existsRaw]
        exact hp.worker
  · intro v hv hk hf
    rcases (hready v).1 hv with rfl | hv
    · have hf' : s.original.round < K ∧ s.original.source v = s.original.round := ⟨hk, hf⟩
      rw [ha, hraw, Function.update_self]
      change (((emissions K B s (.query v)).foldl step s.trace).raws s.trace.nextRaw).collection = s.active
      simp [emissions, hf', step]
    · have hne : v ≠ w := fun h => he.2 (h ▸ hv)
      rw [ha, hraw, Function.update_of_ne hne, hx.oldRaw _ (hs.pending v hv).existsRaw]
      exact hs.fresh v hv hk hf

  · intro v hv u hu hne
    have hv' := (hready v).1 hv
    have hu' := (hready u).1 hu
    rw [hraw, hraw]
    rcases hv' with rfl | hv'
    · have huNe : u ≠ v := Ne.symm hne
      rw [Function.update_self, Function.update_of_ne huNe]
      rcases hu' with h | hu'
      · exact (huNe h).elim
      · exact Nat.ne_of_gt (hs.pending u hu').existsRaw
    · rcases hu' with rfl | hu'
      · rw [Function.update_self, Function.update_of_ne hne]
        exact Nat.ne_of_lt (hs.pending v hv').existsRaw
      · have hvNe : v ≠ w := fun h => he.2 (h ▸ hv')
        have huNe : u ≠ w := fun h => he.2 (h ▸ hu')
        rw [Function.update_of_ne hvNe, Function.update_of_ne huNe]
        exact hs.distinct v hv' u hu' hne

end LongTails.Proofs.BirchCollectionRennalaTrace
