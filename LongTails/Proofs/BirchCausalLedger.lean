import LongTails.Algorithms.BirchCausalPhysical
import LongTails.Proofs.BirchCausalDiscarded
import LongTails.Proofs.BirchNonEuclideanScheduling

namespace LongTails.Proofs.BirchCausalLedger

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Algorithms.BirchCausalPhysical
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanUnused
open LongTails.Proofs.BirchNonEuclideanScheduling
open LongTails.Proofs.BirchCausalConstruction
open LongTails.Proofs.BirchCausalMerges
open LongTails.Proofs.BirchCausalControllers
open LongTails.Proofs.BirchCausalPlans
open LongTails.Proofs.BirchCausalOutputs
open LongTails.Proofs.BirchCausalDiscarded

lemma physicalPlan_invariant {m : ℕ} (workers H K B : ℕ) (word : ℕ → Fin m)
    (recipe : Packet m → PacketExpr) (hw : 0 < workers)
    (hp : ∀ job, (recipe job).Valid workers) (hc : ∀ job, (recipe job).calls = H) :
    PlanInvariant workers H (packetCutoff H B) K (physicalPlan H K B word recipe) := by
  apply planRun_invariant workers H (packetCutoff H B) K _ _ hw
  · intro k; exact hp _
  · intro k; exact hc _
  · exact fun k => (packetSource_valid _ _ (scheduleRun_accepted_valid K _ word _) k).1
  · exact fun k => (packetSource_valid _ _ (scheduleRun_accepted_valid K _ word _) k).2

lemma drainGraph_calls {m : ℕ} (H : ℕ) (recipe : Packet m → PacketExpr)
    (state : GraphState) (main : ℕ → ℕ) (job : Packet m) (s : CodeState) :
    codeCalls (drainGraph H recipe state main job s).2 = codeCalls s + (recipe job).calls := by
  change codeCalls (graphCode H 0 ((recipe job).compile 0 1).nodes ((recipe job).compile 0 1).output
    (state.states (main job.source)).worker (state.states (main job.source)).point
    (state.states (main job.source)).momentum s).2 = _
  rw [graphCode_calls, compile_calls]

lemma drainGraphs_calls {m : ℕ} (H : ℕ) (recipe : Packet m → PacketExpr)
    (state : GraphState) (main : ℕ → ℕ) (jobs : List (Packet m)) (s : CodeState)
    (hc : ∀ job ∈ jobs, (recipe job).calls = H) :
    codeCalls (drainGraphs H recipe state main jobs s).2 = codeCalls s + jobs.length * H := by
  induction jobs generalizing s with
  | nil => simp only [drainGraphs, state_pure_apply, List.length_nil, zero_mul, Nat.add_zero]
  | cons job rest ih =>
      simp only [drainGraphs, state_bind_apply]
      rw [ih _ (fun j hj => hc j (List.mem_cons_of_mem _ hj)), drainGraph_calls, hc job List.mem_cons_self]
      simp only [List.length_cons]
      ring

lemma drainGraph_extends {m : ℕ} (H : ℕ) (recipe : Packet m → PacketExpr)
    (state : GraphState) (main : ℕ → ℕ) (job : Packet m) :
    BuildExtends (drainGraph H recipe state main job) := by
  unfold drainGraph
  apply buildExtends_bind _ _ (graphCode_extends _ _ _ _ _ _ _)
  intro _
  exact buildExtends_pure ()

lemma drainGraphs_extends {m : ℕ} (H : ℕ) (recipe : Packet m → PacketExpr)
    (state : GraphState) (main : ℕ → ℕ) (jobs : List (Packet m)) :
    BuildExtends (drainGraphs H recipe state main jobs) := by
  induction jobs with
  | nil => exact buildExtends_pure ()
  | cons job rest ih =>
      apply buildExtends_bind _ _ (drainGraph_extends H recipe state main job)
      intro _
      exact ih

lemma drainGraph_properties {m : ℕ} (workers H B : ℕ) (η : ℝ)
    (recipe : Packet m → PacketExpr) (state : GraphState) (main : ℕ → ℕ) (job : Packet m)
    (s : CodeState) (ht : (canonicalTuning η B).Valid)
    (hs : CodeValid workers (canonicalTuning η B) s)
    (hc : Clean (codeSymbolic (canonicalTuning η B) s))
    (hp : (recipe job).Valid workers)
    (ho : OwnedValid workers (canonicalTuning η B) s (state.states (main job.source)))
    (hx : ((codeSymbolic (canonicalTuning η B) s).points (state.states (main job.source)).point).1 = 0)
    (hv : RawAffine ((codeSymbolic (canonicalTuning η B) s).vectors (state.states (main job.source)).momentum)) :
    let final := (drainGraph H recipe state main job s).2
    CodeValid workers (canonicalTuning η B) final ∧ Retains (canonicalTuning η B) s final ∧
      CodeExtends s final ∧ Clean (codeSymbolic (canonicalTuning η B) final) := by
  let block := (recipe job).compile 0 1
  let root := state.states (main job.source)
  have hn : ∀ node ∈ block.nodes, node.worker < workers := compile_workers workers (recipe job) hp 0 1
  have hl := graphCode_valid workers H 0 block.output (canonicalTuning η B) ht block.nodes hn
    root.worker root.point root.momentum s hs ho.1 ho.2.1 ho.2.2
  exact ⟨hl.1, hl.2.1, drainGraph_extends H recipe state main job s,
    graphCode_clean workers H 0 B block.output root.worker root.point root.momentum η ht block.nodes hn s
      hs ho.1 ho.2.1 ho.2.2 hc hx hv⟩

lemma drainGraphs_properties {m : ℕ} (workers H B : ℕ) (η : ℝ)
    (recipe : Packet m → PacketExpr) (state : GraphState) (main : ℕ → ℕ) (jobs : List (Packet m))
    (s : CodeState) (ht : (canonicalTuning η B).Valid)
    (hs : CodeValid workers (canonicalTuning η B) s)
    (hc : Clean (codeSymbolic (canonicalTuning η B) s))
    (hp : ∀ job ∈ jobs, (recipe job).Valid workers)
    (ho : ∀ job ∈ jobs, OwnedValid workers (canonicalTuning η B) s (state.states (main job.source)))
    (hx : ∀ job ∈ jobs, ((codeSymbolic (canonicalTuning η B) s).points (state.states (main job.source)).point).1 = 0)
    (hv : ∀ job ∈ jobs, RawAffine ((codeSymbolic (canonicalTuning η B) s).vectors (state.states (main job.source)).momentum)) :
    let final := (drainGraphs H recipe state main jobs s).2
    CodeValid workers (canonicalTuning η B) final ∧ Retains (canonicalTuning η B) s final ∧
      CodeExtends s final ∧ Clean (codeSymbolic (canonicalTuning η B) final) := by
  induction jobs generalizing s with
  | nil => exact ⟨hs, retains_refl _ s, codeExtends_refl s, hc⟩
  | cons job rest ih =>
      let mid := (drainGraph H recipe state main job s).2
      have hh := drainGraph_properties workers H B η recipe state main job s ht hs hc
        (hp job List.mem_cons_self) (ho job List.mem_cons_self)
        (hx job List.mem_cons_self) (hv job List.mem_cons_self)
      have hob : ∀ j ∈ rest, OwnedValid workers (canonicalTuning η B) mid (state.states (main j.source)) := by
        intro j hj
        exact OwnedValid.retains _ _ s mid _ (ho j (List.mem_cons_of_mem _ hj)) hh.2.1
      have hbound := codeValid_register_bound workers (canonicalTuning η B) s hs
      have hn := codeValid_symbolic_next workers (canonicalTuning η B) s hs
      have hxb : ∀ j ∈ rest, ((codeSymbolic (canonicalTuning η B) mid).points (state.states (main j.source)).point).1 = 0 := by
        intro j hj
        have hmem := ho j (List.mem_cons_of_mem _ hj)
        rw [(codeExtends_symbolic _ s mid hh.2.2.1 _ (by rw [← hn]; exact hbound.1 _ _ hmem.2.1)).1]
        exact hx j (List.mem_cons_of_mem _ hj)
      have hvb : ∀ j ∈ rest, RawAffine ((codeSymbolic (canonicalTuning η B) mid).vectors (state.states (main j.source)).momentum) := by
        intro j hj
        have hmem := ho j (List.mem_cons_of_mem _ hj)
        rw [(codeExtends_symbolic _ s mid hh.2.2.1 _ (by rw [← hn]; exact hbound.2 _ _ hmem.2.2)).2.1]
        exact hv j (List.mem_cons_of_mem _ hj)
      have hf := ih mid hh.1 hh.2.2.2 (fun j hj => hp j (List.mem_cons_of_mem _ hj)) hob hxb hvb
      exact ⟨hf.1, retains_trans _ s mid _ hh.2.1 hf.2.1,
        codeExtends_trans s mid _ hh.2.2.1 hf.2.2.1, hf.2.2.2⟩

lemma physicalGraphCode_run {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (recipe : Packet m → PacketExpr) :
    (physicalGraphCode H K B word recipe).run {} =
      let plan := physicalPlan H K B word recipe
      let init := (localBatch 0 0 B).run {}
      let state := graphRun H 0 plan.nodes ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩ init.2
      let base := (sendMainPoints K state.1 plan.main state.2).2
      let tail := drainGraphs H recipe state.1 plan.main (ignored (finalSchedule H K B word)) base
      (fun k => (state.1.states (plan.main k)).point, tail.2) := rfl

lemma physicalGraphCode_calls {m : ℕ} (workers H K B : ℕ) (word : ℕ → Fin m)
    (recipe : Packet m → PacketExpr) (hw : 0 < workers)
    (hp : ∀ job, (recipe job).Valid workers) (hc : ∀ job, (recipe job).calls = H) :
    codeCalls ((physicalGraphCode H K B word recipe).run {}).2 =
      B + H * (K + (ignored (finalSchedule H K B word)).length) := by
  let plan := physicalPlan H K B word recipe
  have hi := physicalPlan_invariant workers H K B word recipe hw hp hc
  rw [physicalGraphCode_run]
  dsimp only
  rw [drainGraphs_calls H recipe _ _ _ _ (fun job _ => hc job)]
  change codeCalls (graphProgramCode H K B plan.nodes plan.main {}).2 + _ = _
  have hc0 := graphProgram_calls H K B plan.nodes plan.main (canonicalTuning 0 1)
  change codeCalls (graphProgramCode H K B plan.nodes plan.main {}).2 = _ at hc0
  rw [hc0, ← graphHistory_atoms, hi.atoms]
  ring

end LongTails.Proofs.BirchCausalLedger
