import LongTails.Proofs.BirchCollectionTrajectory

namespace LongTails.Proofs.BirchCollectionMoments

open Finset
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionSampling
open LongTails.Proofs.BirchCollectionReplay
open LongTails.Proofs.BirchCollectionWeights
open LongTails.Proofs.BirchCollectionEvaluation
open LongTails.Proofs.BirchCollectionNoise
open LongTails.Proofs.BirchCollectionBlocks
open LongTails.Proofs.BirchCollectionTrajectory
open LongTails.Proofs.BirchRetainedSampling
open LongTails.Proofs.BirchNonEuclideanRecords
open LongTails.Proofs.BirchNonEuclideanExecution (queryCount)
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open MeasureTheory

lemma instruction_query_point {Ω : Type} (p : Params) (lmo : Point p.d → Point p.d)
    (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K)
    (n : ℕ) (hn : n < p.ordering.labels.length)
    (q : ℕ) (hq : q ∈ instructionRaw p.ordering (compiled p).trace (compiled p).registers n) :
    sampledQueryPoint (native p) (program p) lmo g q ξ =
      sourcePoint p lmo (fun k x => g x (ξ k)) n := by
  have hqmem := (instruction_raw_properties p he K ho).2 n hn |>.1 hq
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
  have hl : RawLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using rawLedger_run p.workers p.events he
  have hc : CompletedLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hlabel := ho.2.2.2.2.2.2.1 n hn
  have haraw := (completed_raw _ hl hc _ hlabel).2 a (List.mem_toFinset.mp ha)
  have hv := rawValues_compile (1 / (20 * p.L)) p.workers p.events he
  have hr := executed_represents p lmo (fun k x => g x (ξ k))
  have hpoint := sampledQueryPoint_identity (native p) (program p) lmo g _ hqmem ξ
  erw [hv.query a haraw.1, ← hr.2.1] at hpoint
  have hheader := (hc.records _ hlabel).2.2.2
  have hsource := congrArg (fun z : ℕ × ℕ × ℕ × ℝ × ℝ => z.2.1) hheader
  change ((compiled p).trace.collections ((compiled p).trace.directions
    (p.ordering.label n)).collection).source =
      ((compiled p).trace.directions (p.ordering.label n)).source at hsource
  erw [haraw.2, hsource] at hpoint
  exact hpoint

lemma instruction_mean_error {Ω : Type} (p : Params) (lmo : Point p.d → Point p.d)
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω)
    (he : ValidFrom p.workers {} p.events) (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    let raw := instructionRaw p.ordering (compiled p).trace (compiled p).registers n
    meanVector p lmo (fun k x => g x (ξ k)) n -
        gradient f (sourcePoint p lmo (fun k x => g x (ξ k)) n) =
      (1 / (raw.card : ℝ)) • ∑ q ∈ raw,
        (g (sampledQueryPoint (native p) (program p) lmo g q ξ)
          (ξ (queryCount ((program p).instructions.take (q - 1)))) -
          gradient f (sampledQueryPoint (native p) (program p) lmo g q ξ)) := by
  let raw := instructionRaw p.ordering (compiled p).trace (compiled p).registers n
  have hr := (instruction_raw_properties p he K ho).2 n hn
  have hcard : (raw.card : ℝ) ≠ 0 := (Nat.cast_pos.mpr (card_pos.mpr hr.2.1)).ne'
  have hq (q : ℕ) (hq : q ∈ raw) :
      g (sampledQueryPoint (native p) (program p) lmo g q ξ)
          (ξ (queryCount ((program p).instructions.take (q - 1)))) -
          gradient f (sampledQueryPoint (native p) (program p) lmo g q ξ) =
        (executed p lmo (fun k x => g x (ξ k))).vectors q -
          gradient f (sourcePoint p lmo (fun k x => g x (ξ k)) n) := by
    rw [← sampled_query_identity (native p) (program p) lmo g q (hr.1 hq) ξ,
      instruction_query_point p lmo g ξ he K ho n hn q hq]
    rfl
  dsimp only
  change _ = (1 / (raw.card : ℝ)) • _
  rw [sum_congr rfl hq, sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_sub, smul_smul, one_div_mul_cancel hcard, one_smul]
  rw [executed_instruction_mean p lmo (fun k x => g x (ξ k)) he K ho n hn]

noncomputable def noise {Ω : Type} (p : Params)
    (hpast : ∀ n, p.ordering.history (compiled p).trace n ⊆ range n)
    (lmo : Point p.d → Point p.d) (f : Point p.d → ℝ)
    (g : Point p.d → Ω → Point p.d) (n : ℕ) (ξ : ℕ → Ω) : ℝ :=
  dualNorm p.N (∑ q ∈ range (n + 1), row (compiled p).trace p.ordering hpast n q •
    (meanVector p lmo (fun k x => g x (ξ k)) q -
      gradient f (sourcePoint p lmo (fun k x => g x (ξ k)) q))) ^ 2

lemma noise_identity {Ω : Type} (p : Params) (lmo : Point p.d → Point p.d)
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω)
    (he : ValidFrom p.workers {} p.events) (K B : ℕ)
    (hs : Structural (compiled p).trace p.ordering p.controls K B)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    noise p hs.1.2.2.2.2.2.2.2.2 lmo f g n ξ =
      dualNorm p.N (∑ q ∈ (program p).symbolic.queries,
        coefficients p hs.1.2.2.2.2.2.2.2.2 n q •
          (g (sampledQueryPoint (native p) (program p) lmo g q ξ)
            (ξ (queryCount ((program p).instructions.take (q - 1)))) -
            gradient f (sampledQueryPoint (native p) (program p) lmo g q ξ))) ^ 2 := by
  have hr := instruction_raw_properties p he K hs.1
  have hsub : range (n + 1) ⊆ range p.ordering.labels.length := range_mono (by omega)
  rw [noise, coefficients, rawRow_smul _ _ _ _ _
    (fun i hi j hj hij => hr.1 (hsub hi) (hsub hj) hij)
    (fun j hj => (hr.2 j (mem_range.mp (hsub hj))).1)]
  congr 2
  apply sum_congr rfl
  intro q hq
  rw [instruction_mean_error p lmo f g ξ he K hs.1 q (mem_range.mp (hsub hq))]

lemma noise_bound {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (he : ValidFrom p.workers {} p.events) (K B : ℕ)
    (hs : Structural (compiled p).trace p.ordering p.controls K B) (hB : 0 < B)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (hg : LongTails.Setups.BirchNonEuclidean.StochasticGradient (native p) (μ : Measure Ω) f g)
    (regular : LongTails.Setups.BirchNonEuclidean.DualRegularityWitness p.N p.κ)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    Integrable (noise p hs.1.2.2.2.2.2.2.2.2 lmo f g n) (P : Measure (ℕ → Ω)) ∧
      (∫ ξ, noise p hs.1.2.2.2.2.2.2.2.2 lmo f g n ξ ∂(P : Measure (ℕ → Ω))) ≤
        p.κ * p.σ ^ 2 / B := by
  have h := BirchCollectionNoise.coefficient_noise p he K B hs hB lmo hlmo μ P hiid
    f g hg regular hR hR0 n hn
  have heq := funext (fun ξ => noise_identity p lmo f g ξ he K B hs n hn)
  rw [heq]
  exact h

lemma expected_energy {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (he : ValidFrom p.workers {} p.events) (K B : ℕ)
    (hs : Structural (compiled p).trace p.ordering p.controls K B) (hB : 0 < B)
    (lmo : Point p.d → Point p.d) (hlmo : IsBallLMO p.N 1 lmo)
    (I : Instance p.d) (hf : LongTails.Setups.BirchNonEuclidean.Objective (native p) I)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Point p.d → Ω → Point p.d)
    (hg : LongTails.Setups.BirchNonEuclidean.StochasticGradient (native p) (μ : Measure Ω) I.f g)
    (regular : LongTails.Setups.BirchNonEuclidean.DualRegularityWitness p.N p.κ)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (hdef : ∀ x, p.N x = 0 → x = 0) (hL : 0 < p.L) :
    let G := fun ξ : ℕ → Ω => ∑ k ∈ range K,
      dualNorm p.N (gradient I.f (mainPoint p lmo (fun j x => g x (ξ j)) k)) ^ 2
    Integrable G (P : Measure (ℕ → Ω)) ∧
      (∫ ξ, G ξ ∂(P : Measure (ℕ → Ω))) ≤
        (6 * p.Δ / (1 / (20 * p.L))) / p.controls.lowerMass +
          (16 / p.controls.lowerMass) *
            (p.κ * p.σ ^ 2 / B * ((K : ℝ) * p.controls.upperMass)) := by
  let G := fun ξ : ℕ → Ω => ∑ k ∈ range K,
    dualNorm p.N (gradient I.f (mainPoint p lmo (fun j x => g x (ξ j)) k)) ^ 2
  let T := noise p hs.1.2.2.2.2.2.2.2.2 lmo I.f g
  let V := fun ξ => ∑ n ∈ range p.ordering.labels.length,
    p.ordering.movement (compiled p).trace n * T n ξ
  have hp : CollectionParameters (compiled p).trace := by
    simpa only [compiled, compile_trace] using collectionParameters_run p.workers p.events he
  have hc : CompletedLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hw := ordering_parameters _ _ K hp hc hs.1
  have hlower := hs.2.1.1
  have hκ : 0 ≤ p.κ := (by norm_num : (0 : ℝ) ≤ 1).trans
    (regular.smoothness_lower.trans regular.smoothness_upper)
  have hnoise (n : ℕ) (hn : n < p.ordering.labels.length) :
      Integrable (T n) (P : Measure (ℕ → Ω)) ∧
        (∫ ξ, T n ξ ∂(P : Measure (ℕ → Ω))) ≤ p.κ * p.σ ^ 2 / B :=
    noise_bound p he K B hs hB lmo hlmo.measurable μ P hiid I.f g hg regular hR hR0 n hn
  have hVI : Integrable V (P : Measure (ℕ → Ω)) :=
    integrable_finsetSum _ (fun n hn => (hnoise n (mem_range.mp hn)).1.const_mul _)
  have hVB : (∫ ξ, V ξ ∂(P : Measure (ℕ → Ω))) ≤
      p.κ * p.σ ^ 2 / B * ((K : ℝ) * p.controls.upperMass) := by
    rw [show V = fun ξ => ∑ n ∈ range p.ordering.labels.length,
      p.ordering.movement (compiled p).trace n * T n ξ from rfl,
      integral_finsetSum _ (fun n hn => (hnoise n (mem_range.mp hn)).1.const_mul _)]
    simp only [integral_const_mul]
    calc
      _ ≤ ∑ n ∈ range p.ordering.labels.length,
          p.ordering.movement (compiled p).trace n * (p.κ * p.σ ^ 2 / B) :=
        sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left
          (hnoise n (mem_range.mp hn)).2 (hw n).1)
      _ = (p.κ * p.σ ^ 2 / B) * ∑ n ∈ range p.ordering.labels.length,
          p.ordering.movement (compiled p).trace n := by rw [← sum_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (total_mass_bound _ _ _ K B hs) (by positivity)
  have hpoint (ξ : ℕ → Ω) : G ξ ≤
      (6 * p.Δ / (1 / (20 * p.L))) / p.controls.lowerMass +
        (16 / p.controls.lowerMass) * V ξ := by
    have henergy := logical_energy p lmo (fun k x => g x (ξ k)) he K B hs I hf hR hdef hL hlmo
    have hlow : p.controls.lowerMass * G ξ ≤
        ∑ k ∈ range K, mass (compiled p).trace p.ordering k *
          dualNorm p.N (gradient I.f (mainPoint p lmo (fun j x => g x (ξ j)) k)) ^ 2 := by
      rw [show G ξ = ∑ k ∈ range K,
        dualNorm p.N (gradient I.f (mainPoint p lmo (fun j x => g x (ξ j)) k)) ^ 2 from rfl,
        mul_sum]
      exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right
        (hs.2.2.2.2.1 k (mem_range.mp hk)) (sq_nonneg _))
    have hh : p.controls.lowerMass * G ξ ≤ 6 * p.Δ / (1 / (20 * p.L)) + 16 * V ξ :=
      hlow.trans henergy
    calc
      _ ≤ (6 * p.Δ / (1 / (20 * p.L)) + 16 * V ξ) / p.controls.lowerMass :=
        (le_div_iff₀ hlower).mpr (by nlinarith)
      _ = _ := by ring
  have hm := LongTails.Proofs.BirchNonEuclideanCausality.interpret_prefix_measurable
    (native p) lmo hlmo.measurable hR hR0 g hg.measurable (program p).instructions
  have hGM : Measurable G := by
    apply Finset.measurable_sum
    intro k _
    exact ((OracleTemplate.NormBallLMO.continuous_dualNorm hR hR0).measurable.comp
      ((OracleTemplate.NormBallLMO.measurable_gradient_space I.f).comp (hm.1 _))).pow_const 2
  have hGI : Integrable G (P : Measure (ℕ → Ω)) := by
    apply ((integrable_const ((6 * p.Δ / (1 / (20 * p.L))) / p.controls.lowerMass)).add
      (hVI.const_mul (16 / p.controls.lowerMass))).mono' hGM.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun k _ => sq_nonneg _))]
    exact hpoint ξ
  refine ⟨hGI, ?_⟩
  have hh := integral_mono hGI
    ((integrable_const ((6 * p.Δ / (1 / (20 * p.L))) / p.controls.lowerMass)).add
      (hVI.const_mul (16 / p.controls.lowerMass))) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) (hVI.const_mul _), integral_const_mul] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  have hscale : 0 ≤ (16 : ℝ) / p.controls.lowerMass := div_nonneg (by norm_num) hlower.le
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hVB hscale))

end LongTails.Proofs.BirchCollectionMoments
