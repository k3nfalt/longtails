import LongTails.Proofs.BirchCausalRecords
import LongTails.Proofs.BirchCausalControllers

namespace LongTails.Proofs.BirchCausalProgram

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchCausalConstruction
open LongTails.Proofs.BirchCausalMerges
open LongTails.Proofs.BirchCausalStates
open LongTails.Proofs.BirchCausalRecords
open LongTails.Proofs.BirchCausalControllers

lemma initialBatch_points (B : ℕ) (t : Tuning) :
    (codeSymbolic t ((localBatch 0 0 B).run {}).2).points = fun _ => 0 := by
  rw [localBatch_prefix]
  dsimp only
  rw [codeSymbolic_emit]
  change (codeSymbolic t (batchPrefix 0 0 B B {}).2).points = _
  rw [batchPrefix_points]
  rfl

lemma initialBatch_sets (B : ℕ) (t : Tuning) :
    let s := ((localBatch 0 0 B).run {}).2
    (codeSymbolic t s).queries = (range B).image (fun j => 1 + j) ∧
      (codeSymbolic t s).sharps = ∅ ∧ (codeSymbolic t s).units = ∅ := by
  rw [localBatch_prefix]
  dsimp only
  rw [codeSymbolic_emit]
  have h := batchPrefix_sets 0 0 B B {} t rfl
  simpa only [InstructionTemplate.instantiate, symbolicPerform, symbolicStore, codeSymbolic,
    codeInstructions, List.map_nil, List.foldl_nil, empty_union] using h

lemma initialBatch_queryPoints (B : ℕ) (t : Tuning) (j : ℕ) (hj : j < B) :
    (codeSymbolic t ((localBatch 0 0 B).run {}).2).queryPoints (1 + j) = 0 := by
  rw [localBatch_prefix]
  dsimp only
  rw [codeSymbolic_emit]
  exact (batchPrefix_records 0 0 B B {} t rfl j hj).2

lemma initialBatch_valid (workers B : ℕ) (t : Tuning) (hw : 0 < workers) :
    let z := (localBatch 0 0 B).run {}
    CodeValid workers t z.2 ∧ OwnedValid workers t z.2 ⟨0, 0, z.1⟩ := by
  have hx : 0 ∈ (codeLayout t {}).points 0 := by simp [codeLayout, finalLayout, codeInstructions]
  have h := localBatch_valid workers t 0 0 B {} (codeValid_initial workers t) hw hx
  exact ⟨h.1, hw, (h.2.1 0).1 hx, h.2.2⟩

lemma graphValid_workers (workers : ℕ) (nodes : List GraphNode) (state : HistoryState)
    (h : GraphValidFrom workers state nodes) : ∀ node ∈ nodes, node.worker < workers := by
  induction nodes generalizing state with
  | nil => simp
  | cons node rest ih =>
      intro other ho
      rcases List.mem_cons.mp ho with rfl | ho
      · cases other <;> exact h.1.1
      · exact ih (historyStep node state) h.2 other ho

lemma initialized_runtime (workers H B : ℕ) (η : ℝ) (ht : (canonicalTuning η B).Valid)
    (hw : 0 < workers) (nodes : List GraphNode) (hvalid : GraphValidFrom workers {} nodes) :
    let init := (localBatch 0 0 B).run {}
    let labels0 : GraphLabels := ⟨init.2.next, 0, fun _ => 0, fun _ => 0⟩
    let labels := labelFold nodes labels0
    let raw := fun i => ((Finsupp.single (labels.raw i) 1, 0) : LinearValue)
    let sharp := fun i => ((0, Finsupp.single (labels.sharp i) 1) : LinearValue)
    let momentum : LinearValue := (1 / (B : ℝ)) • ∑ j ∈ range B, (Finsupp.single (1 + j) 1, 0)
    let values := nodes.foldl (flip (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η) raw sharp))
      (initialValues 0 momentum)
    let z := graphRun H 0 nodes ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩ init.2
    RuntimeInvariant workers B η z.1 z.2 labels values labels.raw labels.sharp ∧
      ModelInvariant (graphHistory nodes) values 0 momentum (1 / (B : ℝ))
        (1 / (H : ℝ) * η) raw sharp := by
  let t := canonicalTuning η B
  let init := (localBatch 0 0 B).run {}
  let labels0 : GraphLabels := ⟨init.2.next, 0, fun _ => 0, fun _ => 0⟩
  let labels := labelFold nodes labels0
  let raw := fun i => ((Finsupp.single (labels.raw i) 1, 0) : LinearValue)
  let sharp := fun i => ((0, Finsupp.single (labels.sharp i) 1) : LinearValue)
  let momentum : LinearValue := (1 / (B : ℝ)) • ∑ j ∈ range B, (Finsupp.single (1 + j) 1, 0)
  have hm : (codeSymbolic t init.2).vectors init.1 = momentum := localBatch_symbolic 0 0 B {} t rfl
  have hp : (codeSymbolic t init.2).points 0 = 0 := congrFun (initialBatch_points B t) 0
  have hi := initialBatch_valid workers B t hw
  constructor
  · apply runtimeInvariant_fold workers H 0 B η ht nodes (graphValid_workers workers nodes {} hvalid)
      _ init.2 labels0 (initialValues 0 momentum) labels.raw labels.sharp
    · refine ⟨hi.1, fun _ => hi.2, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · exact ⟨fun _ => hp, fun _ => hm⟩
      · constructor <;> intro i h <;> exact (Nat.not_lt_zero i h).elim
    · exact labelsMatch_final nodes labels0
  · exact modelInvariant_fold workers nodes {} (initialValues 0 momentum) 0 momentum
      (1 / (B : ℝ)) (1 / (H : ℝ) * η) raw sharp hvalid historyInvariant_initial
      (modelInvariant_initial 0 momentum _ _ raw sharp)

end LongTails.Proofs.BirchCausalProgram
