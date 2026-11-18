import LongTails.Proofs.MultiscaleAggregateCodec
import LongTails.Proofs.MultiscaleAggregateClock

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateCodec

variable (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (samples : Samples p)

noncomputable abbrev workerBits (k : ℕ) (i : Fin p.n) :=
  workerMessage p g samples k i (trajectory p g samples k).point

noncomputable abbrev rootBits (k : ℕ) :=
  rootMessage p g samples k (trajectory p g samples k).point

noncomputable abbrev totalCode (k : ℕ) : Code p :=
  ∑ i, readPacket p k (workerBits p g samples k i)

lemma worker_frame (k : ℕ) (i : Fin p.n) (suffix : List Bool) :
    readPacket p k (workerBits p g samples k i ++ suffix) =
      readPacket p k (workerBits p g samples k i) := by
  rw [workerBits, workerMessage, read_packet, read_packet_self]

lemma root_frame (k : ℕ) (suffix : List Bool) :
    readPacket p k (rootBits p g samples k ++ suffix) =
      readPacket p k (rootBits p g samples k) := by
  rw [rootBits, rootMessage, read_packet, read_packet_self]

structure RootPoints (selected : Indices p) (s : State p) : Prop where
  model : s.model = trajectory p g samples s.iteration
  index : s.outputIndex = selected.val
  selected_point : s.selected =
    if selected.val ≤ s.iteration then (trajectory p g samples selected.val).point else p.x0

structure RootData (selected : Indices p) (s : State p) : Prop extends RootPoints p g samples selected s where
  total : s.total = ∑ i ∈ s.arrived, readPacket p s.iteration (workerBits p g samples s.iteration i)

structure WorkerData (i : Fin p.n) (s : State p) : Prop where
  model : s.model = trajectory p g samples s.iteration
  count : s.samples ≤ batch p i
  accumulator : s.accumulator = ∑ j ∈ Finset.range s.samples,
    g i s.model.point (samples i (s.iteration * batch p i + j))

lemma initial_root_data (selected : Indices p) :
    RootData p g samples selected
      { model := initialModel p, selected := p.x0, outputIndex := selected.val } := by
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · dsimp only
    split_ifs with h
    · rw [Nat.eq_zero_of_le_zero h]
      rfl
    · rfl
  · simp

lemma initial_worker_data (selected : Indices p) (i : Fin p.n) :
    WorkerData p g samples i
      { model := initialModel p, selected := p.x0, outputIndex := selected.val } := by
  refine ⟨rfl, Nat.zero_le _, ?_⟩
  simp

lemma receive_worker_data (s : State p) (i : Fin p.n) (padding : List Bool)
    (hs : WorkerData p g samples i s) :
    WorkerData p g samples i (receive p s (rootBits p g samples s.iteration ++ padding)) := by
  refine ⟨?_, Nat.zero_le _, ?_⟩
  · change advance p s.model s.iteration _ = _
    rw [hs.model, root_frame]
    rfl
  · simp [receive]

lemma completed_aggregate (selected : Indices p) (s : State p) (i : Fin p.n)
    (hs : RootData p g samples selected s) (hi : i ∉ s.arrived)
    (hall : insert i s.arrived = Finset.univ) :
    s.total + readPacket p s.iteration (workerBits p g samples s.iteration i) =
      totalCode p g samples s.iteration := by
  rw [hs.total, add_comm, ← Finset.sum_insert hi (f := fun j => readPacket p s.iteration
    (workerBits p g samples s.iteration j)), hall]

lemma finish_root_data (selected : Indices p) (s : State p) (z : Code p)
    (hs : RootPoints p g samples selected s) (hz : z = totalCode p g samples s.iteration) :
    RootData p g samples selected (finish p s z) := by
  have hmodel : (finish p s z).model = trajectory p g samples (s.iteration + 1) := by
    change advance p s.model s.iteration _ = _
    rw [hs.model, hz]
    rfl
  refine ⟨⟨hmodel, hs.index, ?_⟩, ?_⟩
  · change (if s.iteration + 1 = s.outputIndex then (finish p s z).model.point else s.selected) =
      if selected.val ≤ s.iteration + 1 then (trajectory p g samples selected.val).point else p.x0
    rw [hmodel, hs.index, hs.selected_point]
    by_cases he : s.iteration + 1 = selected.val
    · simp [he]
    · have hle : selected.val ≤ s.iteration + 1 ↔ selected.val ≤ s.iteration := by omega
      simp [he, hle]
  · simp [finish]

lemma partial_root_data (selected : Indices p) (s : State p) (i : Fin p.n)
    (hs : RootData p g samples selected s) (hi : i ∉ s.arrived) :
    RootData p g samples selected
      { s with
        total := s.total + readPacket p s.iteration (workerBits p g samples s.iteration i)
        arrived := insert i s.arrived } := by
  refine ⟨⟨hs.model, hs.index, hs.selected_point⟩, ?_⟩
  simp [hs.total, Finset.sum_insert hi, add_comm]

end LongTails.Proofs.MultiscaleAggregateExecution
