import LongTails.Proofs.BirchCollectionEvaluation

namespace LongTails.Proofs.BirchCollectionNoise

open Finset
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionReplay
open LongTails.Proofs.BirchCollectionSampling
open LongTails.Proofs.BirchCollectionWeights
open LongTails.Proofs.BirchCollectionEvaluation
open LongTails.Proofs.BirchRetainedSampling
open LongTails.Proofs.BirchNonEuclideanRecords
open LongTails.Proofs.BirchNonEuclideanExecution (queryCount)
open LongTails.Setups.UscgConstant (dualNorm)
open MeasureTheory

lemma instruction_raw_properties (p : Params) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K) :
    let raw := instructionRaw p.ordering (compiled p).trace (compiled p).registers
    ((range p.ordering.labels.length : Finset ℕ) : Set ℕ).PairwiseDisjoint raw ∧
      ∀ n, n < p.ordering.labels.length →
        raw n ⊆ (program p).symbolic.queries ∧ (raw n).Nonempty ∧
          (raw n).card = (p.ordering.raw (compiled p).trace n).card := by
  have hl : RawLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using rawLedger_run p.workers p.events he
  have hc : CompletedLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hp : CollectionParameters (compiled p).trace := by
    simpa only [compiled, compile_trace] using collectionParameters_run p.workers p.events he
  have hi := labelInjective_compile (1 / (20 * p.L)) p.events
  have hlab := labelSets_compile (1 / (20 * p.L)) p.events
  refine ⟨instructionRaw_disjoint _ _ _ K hl hc ho hi, ?_⟩
  intro n hn
  exact ⟨instructionRaw_subset _ _ _ _ K hl hc ho hlab n hn,
    instructionRaw_nonempty _ _ _ K hp hc ho n hn,
    instructionRaw_card _ _ _ K hl hc ho hi n hn⟩

lemma executed_instruction_mean (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    let raw := instructionRaw p.ordering (compiled p).trace (compiled p).registers n
    meanVector p lmo response n =
      (1 / (raw.card : ℝ)) • ∑ q ∈ raw, (executed p lmo response).vectors q := by
  have hl : RawLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using rawLedger_run p.workers p.events he
  have hc : CompletedLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hi := labelInjective_compile (1 / (20 * p.L)) p.events
  have hd := (completed_raw _ hl hc _ (ho.2.2.2.2.2.2.1 n hn)).1
  have hcard := (instruction_raw_properties p he K ho).2 n hn |>.2.2
  have hm := executed_mean p lmo response he (p.ordering.label n)
    (ho.2.2.2.2.2.2.1 n hn)
  dsimp only at hm ⊢
  unfold meanVector
  rw [hm, hcard]
  simp only [Ordering.raw, List.toFinset_card_of_nodup hd]
  congr 1
  rw [← List.sum_toFinset _ hd]
  symm
  apply sum_image
  exact hi.raw.mono (ordering_raw_subset _ _ K hl hc ho n hn)

noncomputable def coefficients (p : Params)
    (hpast : ∀ n, p.ordering.history (compiled p).trace n ⊆ range n)
    (n : ℕ) : ℕ →₀ ℝ :=
  rawRow (range (n + 1))
    (instructionRaw p.ordering (compiled p).trace (compiled p).registers)
    (row (compiled p).trace p.ordering hpast n)

lemma coefficient_mass (p : Params) (he : ValidFrom p.workers {} p.events)
    (K B : ℕ) (hs : Structural (compiled p).trace p.ordering p.controls K B)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    ∑ q ∈ (program p).symbolic.queries,
      coefficients p hs.1.2.2.2.2.2.2.2.2 n q = 1 := by
  have hp : CollectionParameters (compiled p).trace := by
    simpa only [compiled, compile_trace] using collectionParameters_run p.workers p.events he
  have hc : CompletedLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hh : Histories (compiled p).trace := by
    simpa only [compiled, compile_trace] using histories_run p.workers p.events he
  have hr := instruction_raw_properties p he K hs.1
  have hsub : range (n + 1) ⊆ range p.ordering.labels.length := range_mono (by omega)
  rw [coefficients, rawRow_mass _ _ _ _ (fun i hi j hj hij => hr.1 (hsub hi) (hsub hj) hij)
    (fun j hj => (hr.2 j (mem_range.mp (hsub hj))).1)
    (fun j hj => (hr.2 j (mem_range.mp (hsub hj))).2.1)]
  exact (structural_row_bounds _ _ _ K B hp hc hh hs).2.2.1 n

lemma executed_estimator_raw (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K B : ℕ) (hs : Structural (compiled p).trace p.ordering p.controls K B)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    estimatorVector p lmo response n =
      ∑ q ∈ (program p).symbolic.queries,
        coefficients p hs.1.2.2.2.2.2.2.2.2 n q • (executed p lmo response).vectors q := by
  have hr := instruction_raw_properties p he K hs.1
  have hsub : range (n + 1) ⊆ range p.ordering.labels.length := range_mono (by omega)
  rw [coefficients, rawRow_smul _ _ _ _ _ (fun i hi j hj hij => hr.1 (hsub hi) (hsub hj) hij)
    (fun j hj => (hr.2 j (mem_range.mp (hsub hj))).1),
    logical_estimator_expansion p lmo response he K B hs n hn]
  apply sum_congr rfl
  intro j hj
  rw [executed_instruction_mean p lmo response he K hs.1 j (mem_range.mp (hsub hj))]

lemma coefficient_noise {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (he : ValidFrom p.workers {} p.events) (K B : ℕ)
    (hs : Structural (compiled p).trace p.ordering p.controls K B) (hB : 0 < B)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (ho : LongTails.Setups.BirchNonEuclidean.StochasticGradient (native p) (μ : Measure Ω) f g)
    (regular : LongTails.Setups.BirchNonEuclidean.DualRegularityWitness p.N p.κ)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    let b := coefficients p hs.1.2.2.2.2.2.2.2.2 n
    let noise := fun ξ => dualNorm p.N (∑ q ∈ (program p).symbolic.queries, b q •
      (g (sampledQueryPoint (native p) (program p) lmo g q ξ)
        (ξ (queryCount ((program p).instructions.take (q - 1)))) -
        gradient f (sampledQueryPoint (native p) (program p) lmo g q ξ))) ^ 2
    Integrable noise (P : Measure (ℕ → Ω)) ∧
      (∫ ξ, noise ξ ∂(P : Measure (ℕ → Ω))) ≤ p.κ * p.σ ^ 2 / B := by
  have hp : CollectionParameters (compiled p).trace := by
    simpa only [compiled, compile_trace] using collectionParameters_run p.workers p.events he
  have hc : CompletedLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hh : Histories (compiled p).trace := by
    simpa only [compiled, compile_trace] using histories_run p.workers p.events he
  have hr := instruction_raw_properties p he K hs.1
  have hrow := structural_row_bounds _ _ _ K B hp hc hh hs
  have hsub : range (n + 1) ⊆ range p.ordering.labels.length := range_mono (by omega)
  exact collection_noise (native p) (program p) lmo hlmo μ P hiid f g ho regular hR hR0
    (range (n + 1)) (instructionRaw p.ordering (compiled p).trace (compiled p).registers)
    (row (compiled p).trace p.ordering hs.1.2.2.2.2.2.2.2.2 n)
    (p.ordering.refresh (compiled p).trace) B (Nat.cast_pos.mpr hB)
    (fun i hi j hj hij => hr.1 (hsub hi) (hsub hj) hij) (fun j hj => (hr.2 j (mem_range.mp (hsub hj))).1)
    (fun j hj => (hr.2 j (mem_range.mp (hsub hj))).2.1)
    (fun j _ => hrow.1 n j)
    (fun j hj => hrow.2.1 n hn j (by have := mem_range.mp hj; omega))
    (fun j hj => by
      rw [(hr.2 j (mem_range.mp (hsub hj))).2.2]
      exact hs.2.2.2.2.2.2.1 j (mem_range.mp (hsub hj)))
    (hrow.2.2.1 n)

end LongTails.Proofs.BirchCollectionNoise
