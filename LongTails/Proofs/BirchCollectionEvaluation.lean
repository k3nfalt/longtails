import LongTails.Proofs.BirchCollectionSampling
import LongTails.Proofs.BirchCollectionWeights

namespace LongTails.Proofs.BirchCollectionEvaluation

open Finset
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Setups.BirchNonEuclidean (Memory initialMemory)
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionReplay
open LongTails.Proofs.BirchCollectionSampling
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionWeights
open LongTails.Proofs.BirchNonEuclideanExecution (interpret queryCount)
open LongTails.Proofs.BirchNonEuclideanSymbolic (Represents traceEvaluation)
open LongTails.Proofs.BirchNonEuclideanRecords

noncomputable def compiled (p : Params) : Compilation := compile (1 / (20 * p.L)) p.events

noncomputable def executed (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) : Memory p.d :=
  interpret (native p) lmo response (program p).instructions (initialMemory (native p))

lemma executed_represents (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) :
    Represents (native p) (traceEvaluation (executed p lmo response))
      (program p).symbolic (executed p lmo response) :=
  LongTails.Proofs.BirchNonEuclideanSymbolic.symbolic_represents_sampled_execution
    (native p) (program p) lmo response

lemma executed_point (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (a : ℕ) (ha : a < (compiled p).trace.nextState) :
    let c := compiled p
    let m := executed p lmo response
    m.points (c.registers.point a) = p.x0 +
      ∑ j ∈ (c.trace.states a).history,
        (1 / (20 * p.L) * (c.trace.directions j).movement) • m.vectors (c.registers.sharp j) := by
  have hv := stateValues_compile (1 / (20 * p.L)) p.workers p.events he
  have hr := executed_represents p lmo response
  dsimp only
  erw [hr.2.1]
  change p.x0 + traceEvaluation (executed p lmo response)
      (((compiled p).code.foldl LongTails.Setups.BirchNonEuclidean.symbolicPerform {}).points
        ((compiled p).registers.point a)) = _
  erw [hv.point a ha]
  simp only [map_sum, pointIncrement, map_smul]
  congr 1
  apply sum_congr rfl
  intro j _
  erw [hr.2.2]
  rfl

lemma executed_momentum (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (a : ℕ) (ha : a < (compiled p).trace.nextState) :
    let c := compiled p
    let m := executed p lmo response
    m.vectors (c.registers.momentum a) =
      ∑ j ∈ (c.trace.states a).history,
        (m.vectors (c.registers.estimator j) -
          m.vectors (c.registers.momentum (c.trace.directions j).source)) := by
  have hv := stateValues_compile (1 / (20 * p.L)) p.workers p.events he
  have hr := executed_represents p lmo response
  dsimp only
  erw [hr.2.2]
  change traceEvaluation (executed p lmo response)
      (((compiled p).code.foldl LongTails.Setups.BirchNonEuclidean.symbolicPerform {}).vectors
        ((compiled p).registers.momentum a)) = _
  erw [hv.momentum a ha]
  simp only [map_sum, momentumIncrement, map_sub]
  apply sum_congr rfl
  intro j _
  erw [hr.2.2, hr.2.2]
  rfl

lemma executed_mean (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (j : ℕ) (hj : j < (compiled p).trace.nextDirection) :
    let c := compiled p
    let m := executed p lmo response
    m.vectors (c.registers.mean j) =
      (1 / ((c.trace.directions j).raw.length : ℝ)) •
        ((c.trace.directions j).raw.map (fun q => m.vectors (c.registers.raw q))).sum := by
  have hv := directionValues_compile (1 / (20 * p.L)) p.workers p.events he
  have hr := executed_represents p lmo response
  dsimp only
  erw [hr.2.2]
  change traceEvaluation (executed p lmo response)
      (((compiled p).code.foldl LongTails.Setups.BirchNonEuclidean.symbolicPerform {}).vectors
        ((compiled p).registers.mean j)) = _
  erw [hv.mean j hj]
  simp only [directionAverage, map_smul, map_list_sum, List.map_map, Function.comp_def]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  exact (hr.2.2 _).symm

lemma executed_estimator (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (j : ℕ) (hj : j < (compiled p).trace.nextDirection) :
    let c := compiled p
    let m := executed p lmo response
    m.vectors (c.registers.estimator j) =
      (c.trace.directions j).refresh • m.vectors (c.registers.mean j) +
        (1 - (c.trace.directions j).refresh) •
          m.vectors (c.registers.momentum (c.trace.directions j).source) := by
  have hv := directionValues_compile (1 / (20 * p.L)) p.workers p.events he
  have hr := executed_represents p lmo response
  dsimp only
  erw [hr.2.2]
  change traceEvaluation (executed p lmo response)
      (((compiled p).code.foldl LongTails.Setups.BirchNonEuclidean.symbolicPerform {}).vectors
        ((compiled p).registers.estimator j)) = _
  erw [hv.estimator j hj]
  simp only [map_add, map_smul]
  erw [hr.2.2, hr.2.2]
  rfl

lemma executed_sharp (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (j : ℕ) (hj : j < (compiled p).trace.nextDirection) :
    let c := compiled p
    let m := executed p lmo response
    m.vectors (c.registers.sharp j) =
      LongTails.Setups.UscgConstant.dualNorm p.N (m.vectors (c.registers.estimator j)) •
        lmo (m.vectors (c.registers.estimator j)) := by
  have hs := labelSets_compile (1 / (20 * p.L)) p.events
  have hv := directionValues_compile (1 / (20 * p.L)) p.workers p.events he
  have hr := executed_represents p lmo response
  have hmem : (compiled p).registers.sharp j ∈ (program p).symbolic.sharps := by
    erw [hs.sharps]
    exact mem_image.mpr ⟨j, mem_range.mpr hj, rfl⟩
  have hsharp := sampled_sharp_identity (native p) (program p) lmo response
    ((compiled p).registers.sharp j) hmem
  dsimp only at hsharp ⊢
  erw [hv.input j hj, ← hr.2.2] at hsharp
  exact hsharp

lemma executed_raw {Ω : Type} (p : Params) (lmo : Point p.d → Point p.d)
    (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω) (he : ValidFrom p.workers {} p.events)
    (q : ℕ) (hq : q < (compiled p).trace.nextRaw) :
    let c := compiled p
    let m := executed p lmo (fun k x => g x (ξ k))
    m.vectors (c.registers.raw q) =
      g (m.points (c.registers.point (c.trace.collections (c.trace.raws q).collection).source))
        (ξ q) := by
  have hs := labelSets_compile (1 / (20 * p.L)) p.events
  have hv := rawValues_compile (1 / (20 * p.L)) p.workers p.events he
  have hr := executed_represents p lmo (fun k x => g x (ξ k))
  have hmem : (compiled p).registers.raw q ∈ (program p).symbolic.queries := by
    erw [hs.queries]
    exact mem_image.mpr ⟨q, mem_range.mpr hq, rfl⟩
  have hquery := sampled_query_identity (native p) (program p) lmo g
    ((compiled p).registers.raw q) hmem ξ
  have hpoint := sampledQueryPoint_identity (native p) (program p) lmo g
    ((compiled p).registers.raw q) hmem ξ
  erw [hv.query q hq, ← hr.2.1] at hpoint
  erw [hpoint, rawChronology_compile (1 / (20 * p.L)) p.events q hq] at hquery
  exact hquery

noncomputable def sourceVector (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (n : ℕ) : Point p.d :=
  (executed p lmo response).vectors ((compiled p).registers.momentum
    ((compiled p).trace.directions (p.ordering.label n)).source)

noncomputable def meanVector (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (n : ℕ) : Point p.d :=
  (executed p lmo response).vectors ((compiled p).registers.mean (p.ordering.label n))

noncomputable def estimatorVector (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (n : ℕ) : Point p.d :=
  (executed p lmo response).vectors ((compiled p).registers.estimator (p.ordering.label n))

lemma logical_source_recurrence (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    sourceVector p lmo response n =
      ∑ j ∈ p.ordering.history (compiled p).trace n,
        p.ordering.refresh (compiled p).trace j •
          (meanVector p lmo response j - sourceVector p lmo response j) := by
  have hh : Histories (compiled p).trace := by
    simpa only [compiled, compile_trace] using histories_run p.workers p.events he
  have hm : ∀ a ∈ (compiled p).trace.markers, a < (compiled p).trace.nextState := by
    simpa only [compiled, compile_trace] using markers_bound_run p.workers p.events he
  have hlabel := ho.2.2.2.2.2.2.1 n hn
  have hsource := (hh.direction _ hlabel).1
  have hstate := (hh.direction _ hlabel).2.1
  have hhistory := ordering_query_history (compiled p).trace p.ordering K hh ho hm n hn
  have hindex (j : ℕ) (hj : j ∈ p.ordering.history (compiled p).trace n) :
      j < p.ordering.labels.length :=
    (mem_range.mp (ho.2.2.2.2.2.2.2.2 n hj)).trans hn
  have hsum := executed_momentum p lmo response he _ hsource
  dsimp only at hsum
  erw [← hstate, hhistory, sum_image] at hsum
  · unfold sourceVector
    rw [hsum]
    apply sum_congr rfl
    intro j hj
    have hjN := hindex j hj
    have hest := executed_estimator p lmo response he (p.ordering.label j)
      (ho.2.2.2.2.2.2.1 j hjN)
    dsimp only at hest
    erw [hest]
    simp only [Ordering.refresh, hjN, ite_true, meanVector]
    module
  · intro i hi j hj heq
    exact label_injective p.ordering ho.2.1 (hindex i hi) (hindex j hj) heq

lemma logical_estimator_expansion (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K B : ℕ) (hs : Structural (compiled p).trace p.ordering p.controls K B)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    estimatorVector p lmo response n =
      ∑ q ∈ range (n + 1),
        row (compiled p).trace p.ordering hs.1.2.2.2.2.2.2.2.2 n q •
          meanVector p lmo response q := by
  have hrec := logical_source_recurrence p lmo response he K hs.1
  have hrow := structural_estimator_expansion (compiled p).trace p.ordering p.controls K B hs
    (meanVector p lmo response) (sourceVector p lmo response) hrec n hn
  have hest := executed_estimator p lmo response he (p.ordering.label n)
    (hs.1.2.2.2.2.2.2.1 n hn)
  dsimp only at hest
  unfold estimatorVector
  rw [hest, ← hrow]
  simp only [Ordering.refresh, hn, ite_true, meanVector, sourceVector]
  exact add_comm _ _

end LongTails.Proofs.BirchCollectionEvaluation
