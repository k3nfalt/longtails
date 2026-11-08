import LongTails.Proofs.BirchCausalProgram
import LongTails.Proofs.BirchCausalPlans

namespace LongTails.Proofs.BirchCausalOutputs

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
open LongTails.Proofs.BirchCausalProgram
open LongTails.Proofs.BirchCausalPlans

lemma sendPoints_symbolic (t : Tuning) (state : GraphState) (main : ℕ → ℕ)
    (indices : List ℕ) (s : CodeState) :
    codeSymbolic t (sendPoints state main indices s).2 =
      { codeSymbolic t s with next := (codeSymbolic t s).next + indices.length } := by
  induction indices generalizing s with
  | nil => simp only [sendPoints, state_pure_apply, List.length_nil, Nat.add_zero]
  | cons k rest ih =>
      simp only [sendPoints, state_bind_apply]
      rw [ih, codeSymbolic_emit]
      simp only [InstructionTemplate.instantiate, symbolicPerform, List.length_cons]
      congr 1
      omega

lemma sendPoints_calls (state : GraphState) (main : ℕ → ℕ) (indices : List ℕ) (s : CodeState) :
    codeCalls (sendPoints state main indices s).2 = codeCalls s := by
  induction indices generalizing s with
  | nil => rfl
  | cons k rest ih =>
      simp only [sendPoints, state_bind_apply]
      rw [ih]
      exact emit_calls _ s

lemma sendPoints_extends (state : GraphState) (main : ℕ → ℕ) (indices : List ℕ) :
    BuildExtends (sendPoints state main indices) := by
  induction indices with
  | nil => exact buildExtends_pure ()
  | cons k rest ih =>
      apply buildExtends_bind _ _ (buildExtends_emit _)
      intro _
      exact ih

lemma sendPoints_valid (workers : ℕ) (t : Tuning) (state : GraphState) (main : ℕ → ℕ)
    (indices : List ℕ) (s : CodeState) (hw : 0 < workers) (hs : CodeValid workers t s)
    (howned : ∀ i, OwnedValid workers t s (state.states i)) :
    let final := (sendPoints state main indices s).2
    CodeValid workers t final ∧ Retains t s final ∧
      ∀ k ∈ indices, (state.states (main k)).point ∈ (codeLayout t final).points 0 := by
  induction indices generalizing s with
  | nil => exact ⟨hs, retains_refl t s, by simp⟩
  | cons k rest ih =>
      let point := state.states (main k)
      let mid := (emit (.sendPoint point.worker 0 point.point) s).2
      have hp := howned (main k)
      have hm := sendPoint_valid workers t s hs point.worker 0 point.point hp.1 hw hp.2.1
      have hr := retains_emit t (.sendPoint point.worker 0 point.point) s
      have hnext : ∀ i, OwnedValid workers t mid (state.states i) := by
        intro i
        exact ⟨(howned i).1, (hr _).1 (howned i).2.1, (hr _).2 (howned i).2.2⟩
      have hf := ih mid hm.1 hnext
      refine ⟨hf.1, retains_trans t s mid _ hr hf.2.1, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact (hf.2.1 0).1 hm.2
      · exact hf.2.2 j hj

lemma graphStep_old_state (H round : ℕ) (node : GraphNode) (state : GraphState)
    (s : CodeState) (i : ℕ) (hi : i < state.next) :
    (graphStep H round node state s).1.states i = state.states i := by
  simp only [graphStep, state_bind_apply, state_pure_apply, Function.update_of_ne (ne_of_lt hi)]

lemma graphRun_old_state (H round : ℕ) (nodes : List GraphNode) (state : GraphState)
    (s : CodeState) (i : ℕ) (hi : i < state.next) :
    (graphRun H round nodes state s).1.states i = state.states i := by
  induction nodes generalizing state s with
  | nil => rfl
  | cons node rest ih =>
      unfold graphRun
      rw [state_forIn_cons]
      change (graphRun H round rest (graphStep H round node state s).1
        (graphStep H round node state s).2).1.states i = _
      rw [ih, graphStep_old_state H round node state s i hi]
      simpa only [graphStep, state_bind_apply, state_pure_apply] using Nat.lt_succ_of_lt hi

lemma graphProgram_output_zero (H K B : ℕ) (nodes : List GraphNode) (main : ℕ → ℕ)
    (hmain : main 0 = 0) : (graphProgramCode H K B nodes main {}).1 0 = 0 := by
  let init := (localBatch 0 0 B).run {}
  let initial : GraphState := ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩
  change ((graphRun H 0 nodes initial init.2).1.states (main 0)).point = 0
  rw [hmain, graphRun_old_state H 0 nodes initial init.2 0 (by exact Nat.zero_lt_one)]

lemma graphProgram_legal (workers H K B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw : 0 < workers)
    (nodes : List GraphNode) (main : ℕ → ℕ) (hvalid : GraphValidFrom workers {} nodes) :
    ((graphProgramTemplate H K B nodes main).instantiate (canonicalTuning η B)).Legal workers := by
  let init := (localBatch 0 0 B).run {}
  let z := graphRun H 0 nodes ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩ init.2
  have hr := (initialized_runtime workers H B η ht hw nodes hvalid).1
  have hs := sendPoints_valid workers (canonicalTuning η B) z.1 main (List.range (K + 1)) z.2 hw hr.valid hr.owned
  refine ⟨hs.1.2, hw, ?_⟩
  intro j
  exact hs.2.2 j.val (List.mem_range.mpr (by have hj : j.val < K - 1 + 1 := j.isLt; omega))

lemma graphRun_extends (H round : ℕ) (nodes : List GraphNode) (state : GraphState) :
    BuildExtends (graphRun H round nodes state) := by
  intro s
  induction nodes generalizing state s with
  | nil => exact codeExtends_refl s
  | cons node rest ih =>
      unfold graphRun
      rw [state_forIn_cons]
      exact codeExtends_trans s _ _ (graphStep_extends H round node state s) (ih _ _)

lemma graphRun_calls (H round : ℕ) (nodes : List GraphNode) (state : GraphState) (s : CodeState) :
    codeCalls (graphRun H round nodes state s).2 =
      codeCalls s + (nodes.map GraphNode.calls).sum := by
  induction nodes generalizing state s with
  | nil => simp only [graphRun, List.forIn_nil, state_pure_apply, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons node rest ih =>
      unfold graphRun
      rw [state_forIn_cons]
      change codeCalls (graphRun H round rest (graphStep H round node state s).1
        (graphStep H round node state s).2).2 = _
      rw [ih]
      have hn := graphNodeCode_calls H round node state s
      change codeCalls (graphNodeCode H round node state s).2 + _ = _
      rw [hn]
      simp [Nat.add_assoc]

lemma graphProgram_calls (H K B : ℕ) (nodes : List GraphNode) (main : ℕ → ℕ) (t : Tuning) :
    ((graphProgramTemplate H K B nodes main).instantiate t).oracleCalls =
      B + (nodes.map GraphNode.calls).sum := by
  rw [template_tuning_oracleCalls _ t (canonicalTuning 0 1)]
  change codeCalls (graphProgramCode H K B nodes main {}).2 = _
  let init := (localBatch 0 0 B).run {}
  let z := graphRun H 0 nodes ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩ init.2
  change codeCalls (sendPoints z.1 main (List.range (K + 1)) z.2).2 = _
  rw [sendPoints_calls]
  change codeCalls (graphRun H 0 nodes ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩ init.2).2 = _
  rw [graphRun_calls]
  have hi : codeCalls init.2 = B := by
    rw [localBatch_calls]
    simp [codeCalls]
  rw [hi]

end LongTails.Proofs.BirchCausalOutputs
