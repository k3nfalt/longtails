import LongTails.Algorithms.QueryLayers
import LongTails.Algorithms.TemporalAccelerated
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.InnerProductSpace.Basic
import LongTails.Algorithms.RobustGradientEstimator
import LongTails.Proofs.Clipping
import LongTails.Algorithms.Batched
import LongTails.Algorithms.StochasticEnvelopeProgram

open MeasureTheory
open scoped ENNReal

namespace LongTails.Algorithms.HeavyTailSaddleEstimator

noncomputable def fastSteps {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] (h : ℕ) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) : OracleTemplate.Algorithm (E × F) (E × F) F where
  State := ℕ × E × F
  initial _ := (0, start, 0)
  query s := (0, (s.2.1, dual))
  update s v :=
    let g := v + correction (s.2.1, dual)
    if s.1 < h then (s.1 + 1, s.2.1 - η • g.1, s.2.2)
    else (s.1 + 1, s.2.1, -g.2)
  output s := s.2.2

noncomputable def fastLevel {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (h n : ℕ) (hn : 0 < n) (η : ℝ)
    (start : E) (dual : F) (correction : E × F → E × F) :
    OracleTemplate.Algorithm (E × F) (E × F) F :=
  OracleTemplate.batched hn (fastSteps h η start dual correction)
    (fun s _ => (s.2.1, dual)) (fun _ replies => (n : ℝ)⁻¹ • ∑ i, replies i) 0

def levelCalls (h level : ℕ) : ℕ := (h + 1) * 2 ^ level

def replyCalls (h : ℕ) {J : ℕ} (j : Fin (J + 1)) : ℕ :=
  levelCalls h 0 + levelCalls h (j.val + 1) + levelCalls h j.val

noncomputable def levelPMF (J : ℕ) : PMF (Fin (J + 1)) :=
  PMF.normalize (fun j => (2⁻¹ : ℝ≥0∞) ^ j.val)
    (by
      rw [tsum_fintype]
      have h : 1 ≤ ∑ j : Fin (J + 1), (2⁻¹ : ℝ≥0∞) ^ j.val := by
        simpa using Finset.single_le_sum (f := fun j : Fin (J + 1) =>
          (2⁻¹ : ℝ≥0∞) ^ j.val) (fun i hi => bot_le) (Finset.mem_univ 0)
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one h))
    (by
      rw [tsum_fintype]
      apply ENNReal.sum_ne_top.mpr
      intro i hi
      finiteness)

noncomputable def levelLaw (J : ℕ) : ProbabilityMeasure (Fin (J + 1)) :=
  ⟨(levelPMF J).toMeasure, inferInstance⟩

noncomputable def levelWeight (J : ℕ) (j : Fin (J + 1)) : ℝ :=
  ((levelPMF J) j).toReal

noncomputable def reply {E : Type*} [AddCommGroup E] [Module ℝ E]
    {J : ℕ} (base : E) (fine coarse : Fin (J + 1) → E) (j : Fin (J + 1)) : E :=
  base + (levelWeight J j)⁻¹ • (fine j - coarse j)

def algorithmPlan {Q R U : Type} (A : OracleTemplate.Algorithm Q R U) :
    (k : ℕ) → A.State → OracleTemplate.QueryPlan Q R U k
  | 0, s => .done (A.output s)
  | k + 1, s => .ask (A.query s).2 (fun v => algorithmPlan A k (A.update s v))

noncomputable def fastPlan {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (h level : ℕ) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) F (levelCalls h level) :=
  let A := fastLevel h (2 ^ level) (by positivity) η start dual correction
  algorithmPlan A (levelCalls h level) (A.initial ())

noncomputable def estimatorPlan {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (h : ℕ) {J : ℕ} (j : Fin (J + 1))
    (η : ℝ) (start : E) (dual : F) (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) F (replyCalls h j) :=
  StochasticEnvelopeProgram.castPlan (by simp [replyCalls]; omega)
    ((fastPlan h 0 η start dual correction).bind fun base =>
      (fastPlan h (j.val + 1) η start dual correction).bind fun fine =>
        (fastPlan h j.val η start dual correction).map fun coarse =>
          base + (levelWeight J j)⁻¹ • (fine - coarse))

def batchCalls (h : ℕ) {J : ℕ} (levels : ℕ → Fin (J + 1)) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, replyCalls h (levels i)

noncomputable def sumEstimatorPlan {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (h : ℕ) {J : ℕ} (levels : ℕ → Fin (J + 1))
    (η : ℝ) (start : E) (dual : F) (correction : E × F → E × F) :
    (n : ℕ) → OracleTemplate.QueryPlan (E × F) (E × F) F (batchCalls h levels n)
  | 0 => .done 0
  | n + 1 => StochasticEnvelopeProgram.castPlan (by simp [batchCalls, Finset.sum_range_succ]; omega)
      ((sumEstimatorPlan h levels η start dual correction n).bind fun total =>
        (estimatorPlan h (levels n) η start dual correction).map fun value => total + value)

noncomputable def clippedBatchPlan {E F : Type} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h n : ℕ) {J : ℕ}
    (levels : ℕ → Fin (J + 1)) (η C : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) F (batchCalls h levels n) :=
  (sumEstimatorPlan h levels η start dual correction n).map fun total =>
    OracleTemplate.clip C ((n : ℝ)⁻¹ • total)

noncomputable def primalSteps {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) : OracleTemplate.Algorithm (E × F) (E × F) E where
  State := E
  initial _ := start
  query x := (0, (x, dual))
  update x v := x - η • (v + correction (x, dual)).1
  output x := x

noncomputable def primalLevel {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (n : ℕ) (hn : 0 < n) (η : ℝ)
    (start : E) (dual : F) (correction : E × F → E × F) :
    OracleTemplate.Algorithm (E × F) (E × F) E :=
  OracleTemplate.batched hn (primalSteps η start dual correction)
    (fun x _ => (x, dual)) (fun _ replies => (n : ℝ)⁻¹ • ∑ i, replies i) 0

noncomputable def primalPlan {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (h n : ℕ) (hn : 0 < n) (η : ℝ)
    (start : E) (dual : F) (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) E (h * n) :=
  let A := primalLevel n hn η start dual correction
  algorithmPlan A (h * n) (A.initial ())

noncomputable def primalReplicasPlan {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (h n : ℕ) (hn : 0 < n) (η : ℝ)
    (start : E) (dual : F) (correction : E × F → E × F) (M : ℕ) :
    OracleTemplate.QueryPlan (E × F) (E × F) (Fin M → E) (h * n * M) :=
  StochasticEnvelopeProgram.collectPlans M (fun _ => primalPlan h n hn η start dual correction)

noncomputable def refreshPlan {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] (h n M : ℕ) (hn : 0 < n) (η R : ℝ)
    (start : E) (dual : F) (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) E (h * n * M) :=
  (primalReplicasPlan h n hn η start dual correction M).map fun values =>
    OracleTemplate.RobustGradient.pilotCenter (R / 8) values

noncomputable def refreshBatch (p σ L R : ℝ) : ℕ :=
  1 + ⌈((2 : ℝ) ^ 24 * (σ / (L * R)) ^ p) ^ (1 / (p - 1))⌉₊

noncomputable def refreshRepetitions (δ : ℝ) : ℕ := 1 + ⌈4 * Real.log (1 / δ)⌉₊

noncomputable def tunedRefreshPlan {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] (p σ L R δ : ℝ)
    (start : E) (dual : F) (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) E
      (256 * refreshBatch p σ L R * refreshRepetitions δ) :=
  refreshPlan 256 (refreshBatch p σ L R) (refreshRepetitions δ)
    (by unfold refreshBatch; omega) (1 / (4 * L)) R start dual correction

noncomputable def levelProfileLaw (batch depth : ℕ → ℕ) :
    ProbabilityMeasure ((j : ℕ) → Fin (batch j) → Fin (depth j + 1)) :=
  ⟨Measure.infinitePi (fun j => Measure.pi (fun _ : Fin (batch j) =>
      (levelLaw (depth j) : Measure (Fin (depth j + 1))))), inferInstance⟩

def extendLevels {n J : ℕ} (v : Fin n → Fin (J + 1)) (j : ℕ) : Fin (J + 1) :=
  if hj : j < n then v ⟨j, hj⟩ else 0

noncomputable def kernelHorizon (Lfast m : ℝ) : ℕ :=
  ⌈Real.logb (32 / 31) (max 1 ((2 : ℝ) ^ 18 * Lfast / m))⌉₊

noncomputable def kernelDepth (p σ m B : ℝ) : ℕ :=
  ⌈Real.logb 2 (max 1 (((2 : ℝ) ^ 24 * σ / Real.sqrt (m * B)) ^ (p / (p - 1))))⌉₊

noncomputable def kernelBatch (p σ m H B : ℝ) (J : ℕ) : ℕ :=
  1 + ⌈((2 : ℝ) ^ 36 * ((J + 1) * σ ^ p) /
    (Real.sqrt (m * B) * (Real.sqrt (H * B)) ^ (p - 1))) ^ (1 / (p - 1))⌉₊

noncomputable def tunedKernelPlan {E F : Type} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p σ Lfast m H B : ℝ)
    (levels : ℕ → Fin (kernelDepth p σ m B + 1)) (start : E) (dual : F)
    (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) F
      (batchCalls (kernelHorizon Lfast m) levels (kernelBatch p σ m H B (kernelDepth p σ m B))) :=
  clippedBatchPlan (kernelHorizon Lfast m) (kernelBatch p σ m H B (kernelDepth p σ m B))
    levels (1 / (4 * Lfast)) (32 * Real.sqrt (H * B)) start dual correction

open LongTails.Algorithms.StochasticEnvelopeProgram

noncomputable def epochPlan {E F : Type} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p σ Lfast m H B a : ℝ)
    (seeds : ℕ → Fin (kernelBatch p σ m H B (kernelDepth p σ m B)) → Fin (kernelDepth p σ m B + 1))
    (ref : E) (correction : E × F → E × F) (N : ℕ) (state : F × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) (F × F)
      (slotCalls (fun j => batchCalls (kernelHorizon Lfast m) (extendLevels (seeds j))
        (kernelBatch p σ m H B (kernelDepth p σ m B))) N 0) :=
  substitutePlan
    (fun j => batchCalls (kernelHorizon Lfast m) (extendLevels (seeds j))
      (kernelBatch p σ m H B (kernelDepth p σ m B)))
    (fun j v => tunedKernelPlan p σ Lfast m H B (extendLevels (seeds j)) ref v correction)
    (statePlan (fun _ => OracleTemplate.TemporalDiscrepancy.acceleratedQuery a)
      (fun _ => OracleTemplate.TemporalDiscrepancy.acceleratedUpdate a m) N 0 state) 0

noncomputable def epochLog (m H δ : ℝ) : ℝ :=
  100000 * (1 + Real.log (100000 * Real.sqrt H / (Real.sqrt m * δ)))
noncomputable def epochMomentum (m H δ : ℝ) : ℝ :=
  Real.sqrt m / (Real.sqrt H * epochLog m H δ)
noncomputable def epochSteps (m H δ : ℝ) : ℕ :=
  ⌈4 * Real.sqrt H * epochLog m H δ / Real.sqrt m⌉₊

noncomputable def halvingCalls (p σ L m H B δ : ℝ)
    (seeds : ℕ → Fin (kernelBatch p σ m H B (kernelDepth p σ m B)) → Fin (kernelDepth p σ m B + 1)) : ℕ :=
  256 * refreshBatch p σ L (Real.sqrt (B / m)) * refreshRepetitions (δ / 2) +
    slotCalls (fun j => batchCalls (kernelHorizon L m) (extendLevels (seeds j))
      (kernelBatch p σ m H B (kernelDepth p σ m B))) (epochSteps m H (δ / 2)) 0

noncomputable def halvingPlan {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p σ L m H B δ : ℝ)
    (seeds : ℕ → Fin (kernelBatch p σ m H B (kernelDepth p σ m B)) → Fin (kernelDepth p σ m B + 1))
    (ref : E) (state : F × F) (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) (E × F) (halvingCalls p σ L m H B δ seeds) :=
  (epochPlan p σ L m H B (epochMomentum m H (δ / 2)) seeds ref correction
    (epochSteps m H (δ / 2)) state).bind fun v =>
      (tunedRefreshPlan p σ L (Real.sqrt (B / m)) (δ / 2) ref v.1 correction).map fun r => (r, v.1)

abbrev HalvingProfile (batch depth : ℕ → ℕ) :=
  (j : ℕ) → ℕ → Fin (batch j) → Fin (depth j + 1)
noncomputable def halvingProfileLaw (batch depth : ℕ → ℕ) : ProbabilityMeasure (HalvingProfile batch depth) :=
  ⟨Measure.infinitePi (fun j => Measure.infinitePi (fun _ : ℕ =>
    Measure.pi (fun _ : Fin (batch j) => (levelLaw (depth j) : Measure (Fin (depth j + 1)))))), inferInstance⟩

noncomputable def refinementEnvelope (B : ℝ) (j : ℕ) : ℝ := B / (2 : ℝ) ^ j
noncomputable def refinementDepth (p σ m B : ℝ) (j : ℕ) : ℕ :=
  kernelDepth p σ m (refinementEnvelope B j)
noncomputable def refinementBatch (p σ m H B : ℝ) (j : ℕ) : ℕ :=
  kernelBatch p σ m H (refinementEnvelope B j) (refinementDepth p σ m B j)
noncomputable def refinementCalls (p σ L m H B δ : ℝ) (K : ℕ)
    (seeds : ℕ → HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)) : ℕ :=
  slotCalls (fun j => halvingCalls p σ L m H (refinementEnvelope B j) (δ / (K + 1)) ((seeds j) j)) K 0
noncomputable def refinementPlan {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p σ L m H B δ : ℝ) (K : ℕ)
    (seeds : ℕ → HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B))
    (state : E × F) (correction : E × F → E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) (E × F) (refinementCalls p σ L m H B δ K seeds) :=
  substitutePlan
    (fun j => halvingCalls p σ L m H (refinementEnvelope B j) (δ / (K + 1)) ((seeds j) j))
    (fun j z => halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K + 1)) ((seeds j) j) z.1 (z.2, z.2) correction)
    (statePlan (fun _ z => z) (fun _ _ z => z) K 0 state) 0

noncomputable def refinementSteps (B target : ℝ) : ℕ := 1 + ⌈Real.logb 2 (max 1 (B / target))⌉₊

open OracleTemplate LongTails.Algorithms.QueryLayers
def cappedPlan {Q R U : Type} (q0 : Q) (u0 : U) (cap : ℕ) {k : ℕ}
    (plan : QueryPlan Q R U k) : QueryPlan Q R U cap :=
  if h : k ≤ cap then
    cast (congrArg (QueryPlan Q R U) (Nat.sub_add_cancel h)) (paddedPlan q0 plan (cap-k))
  else paddingPlan q0 u0 cap

noncomputable def refinementMaxReply (p σ L m B : ℝ) (K : ℕ) : ℕ :=
  1 + (Finset.range K).sup (fun j => (kernelHorizon L m+1)*(1+3*2^(refinementDepth p σ m B j)))
noncomputable def refinementFixedCalls (p σ L m B δ : ℝ) (K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range K, 256 * refreshBatch p σ L (Real.sqrt (refinementEnvelope B j/m)) * refreshRepetitions (δ/(K+1)/2)
noncomputable def refinementMeanCalls (p σ L m H B δ : ℝ) (K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range K, epochSteps m H (δ/(K+1)/2) * refinementBatch p σ m H B j *
    ((kernelHorizon L m+1)*(1+3*(refinementDepth p σ m B j+1)))
noncomputable def refinementCap (p σ L m H B δ η : ℝ) (K : ℕ) : ℕ :=
  refinementFixedCalls p σ L m B δ K + 2*refinementMeanCalls p σ L m H B δ K +
    ⌈(refinementMaxReply p σ L m B K : ℝ)*Real.log (1/η)⌉₊
noncomputable def cappedRefinementPlan {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p σ L m H B δ η : ℝ) (K : ℕ)
    (seeds : ℕ → HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B))
    (initial : E × F) (correction : E × F → E × F) :
    QueryPlan (E × F) (E × F) (E × F) (refinementCap p σ L m H B δ η K) :=
  cappedPlan initial initial (refinementCap p σ L m H B δ η K)
    (refinementPlan p σ L m H B δ K seeds initial correction)

noncomputable def proximalCorrection {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L lam : ℝ) (center : E) (shift : F) (z : E × F) : E × F :=
  ((2*L) • (z.1-center), -(lam • z.2)+shift)

noncomputable def recoveryStages (L μ : ℝ) : ℕ := 1 + ⌈Real.logb 2 (max 1 (15*L/μ))⌉₊
noncomputable def recoveryMass (μ : ℝ) (j : ℕ) : ℝ := (2:ℝ)^j*μ
noncomputable def recoveryScale (L μ ζ : ℝ) : ℝ := Real.sqrt (μ*ζ)/(1000*recoveryStages L μ)
noncomputable def recoveryTarget (L μ ζ : ℝ) (j : ℕ) : ℝ := (recoveryScale L μ ζ)^2/recoveryMass μ j
noncomputable def recoveryEnvelope (L μ ζ initialBound : ℝ) (j : ℕ) : ℝ :=
  if j=0 then max initialBound (recoveryTarget L μ ζ 0) else 8*recoveryTarget L μ ζ (j-1)
noncomputable def recoveryHalvings (L μ ζ initialBound : ℝ) (j : ℕ) : ℕ :=
  if j=0 then refinementSteps (recoveryEnvelope L μ ζ initialBound 0) (recoveryTarget L μ ζ 0) else 4
noncomputable def recoverySmoothness (L μ : ℝ) (j : ℕ) : ℝ := 15*L+recoveryMass μ j-μ
noncomputable def recoveryConfidence (L μ δ : ℝ) : ℝ := δ/(2*(recoveryStages L μ+1))
noncomputable def recoveryStageBatch (p σ L μ ζ initialBound : ℝ) (j : ℕ) : ℕ → ℕ :=
  refinementBatch p σ (recoveryMass μ j) (recoverySmoothness L μ j) (recoveryEnvelope L μ ζ initialBound j)
noncomputable def recoveryStageDepth (p σ L μ ζ initialBound : ℝ) (j : ℕ) : ℕ → ℕ :=
  refinementDepth p σ (recoveryMass μ j) (recoveryEnvelope L μ ζ initialBound j)
abbrev RecoveryProfile (p σ L μ ζ initialBound : ℝ) :=
  (j : ℕ) → ℕ → HalvingProfile (recoveryStageBatch p σ L μ ζ initialBound j)
    (recoveryStageDepth p σ L μ ζ initialBound j)
noncomputable def recoveryStageCap (p σ L μ ζ initialBound δ : ℝ) (j : ℕ) : ℕ :=
  refinementCap p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
    (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
    (recoveryHalvings L μ ζ initialBound j)
noncomputable def recoveryCalls (p σ L μ ζ initialBound δ : ℝ) : ℕ :=
  slotCalls (recoveryStageCap p σ L μ ζ initialBound δ) (recoveryStages L μ) 0
noncomputable def recoveryPlan {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p σ L μ ζ initialBound δ : ℝ) (seeds : ℕ → RecoveryProfile p σ L μ ζ initialBound)
    (center : E) (initial : E × F) : QueryPlan (E × F) (E × F) (E × F)
      (recoveryCalls p σ L μ ζ initialBound δ) :=
  (substitutePlan (recoveryStageCap p σ L μ ζ initialBound δ)
    (fun j (state : (E × F) × F) =>
      cappedRefinementPlan p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
        (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
        (recoveryHalvings L μ ζ initialBound j) (seeds j j) state.1
        (proximalCorrection L (recoveryMass μ j-μ) center state.2))
    (statePlan (fun _ state => state)
      (fun j (state : (E × F) × F) (reply : E × F) => (reply,state.2+recoveryMass μ j • reply.2))
      (recoveryStages L μ) 0 (initial,0)) 0).map Prod.fst

noncomputable def recoveryProfileLaw (p σ L μ ζ initialBound : ℝ) :
    ProbabilityMeasure (RecoveryProfile p σ L μ ζ initialBound) :=
  ⟨Measure.infinitePi (fun j => Measure.infinitePi (fun _ : ℕ =>
    (halvingProfileLaw (recoveryStageBatch p σ L μ ζ initialBound j)
      (recoveryStageDepth p σ L μ ζ initialBound j) : Measure _))), inferInstance⟩

noncomputable def movementScore {E F : Type} [NormedAddCommGroup E] (record : E × (E × F)) : ℝ :=
  ‖record.2.1-record.1‖^2
noncomputable def coarseUpdate {E F : Type} [NormedAddCommGroup E] (j : ℕ)
    (state : (E × (E × F)) × (E × (E × F))) (reply : E × F) : (E × (E × F)) × (E × (E × F)) :=
  ((state.1.2.1,reply), if j=0 ∨ movementScore (state.1.2.1,reply) ≤ movementScore state.2
    then (state.1.2.1,reply) else state.2)
noncomputable def coarseInitialBound (L μ Δ G ζ : ℝ) (T j : ℕ) : ℝ :=
  if j=0 then 3*(L/μ)^2*(Δ+G^2/μ) else 12*(L/μ)*(Δ+(T+1)*ζ)
abbrev CoarseProfile (p σ L μ Δ G ζ : ℝ) (T : ℕ) :=
  (j : ℕ) → ℕ → RecoveryProfile p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j)
noncomputable def coarseCalls (p σ L μ Δ G ζ δ : ℝ) (T : ℕ) : ℕ :=
  slotCalls (fun j => recoveryCalls p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ) T 0
noncomputable def coarsePlan {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p σ L μ Δ G ζ δ : ℝ) (T : ℕ)
    (seeds : ℕ → CoarseProfile p σ L μ Δ G ζ T) (initial : E × F) :
    OracleTemplate.QueryPlan (E × F) (E × F) (E × (E × F))
      (coarseCalls p σ L μ Δ G ζ δ T) :=
  (substitutePlan
    (fun j => recoveryCalls p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ)
    (fun j (state : (E × (E × F)) × (E × (E × F))) =>
      recoveryPlan p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ (seeds j j) state.1.2.1 state.1.2)
    (statePlan (fun _ state => state) coarseUpdate T 0 ((initial.1,initial),(initial.1,initial))) 0).map Prod.snd

noncomputable def coarseProfileLaw (p σ L μ Δ G ζ : ℝ) (T : ℕ) :
    ProbabilityMeasure (CoarseProfile p σ L μ Δ G ζ T) :=
  ⟨Measure.infinitePi (fun j => Measure.infinitePi (fun _ : ℕ =>
    (recoveryProfileLaw p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) : Measure _))), inferInstance⟩

noncomputable def outerSteps (L Δ ε : ℝ) : ℕ := 1+⌈4096*L*Δ/ε^2⌉₊
noncomputable def coarseAccuracy (L ε : ℝ) : ℝ := ε^2/(1048576*L)
noncomputable def fineAccuracy (L μ ε : ℝ) : ℝ := μ*ε^2/(1048576*L^2)
noncomputable def outerConfidence (L Δ ε δ : ℝ) : ℝ := δ/(outerSteps L Δ ε+2)
noncomputable def fineInitialBound (L μ ε : ℝ) : ℝ := 3*(L/μ)*coarseAccuracy L ε
abbrev SaddleSeed (p σ L μ Δ G ε : ℝ) :=
  (ℕ → CoarseProfile p σ L μ Δ G (coarseAccuracy L ε) (outerSteps L Δ ε)) ×
  (ℕ → RecoveryProfile p σ L μ (fineAccuracy L μ ε) (fineInitialBound L μ ε))
noncomputable def saddleSeedLaw (p σ L μ Δ G ε : ℝ) : ProbabilityMeasure (SaddleSeed p σ L μ Δ G ε) :=
  ⟨(Measure.infinitePi (fun _ : ℕ =>
      (coarseProfileLaw p σ L μ Δ G (coarseAccuracy L ε) (outerSteps L Δ ε) : Measure _))).prod
    (Measure.infinitePi (fun _ : ℕ =>
      (recoveryProfileLaw p σ L μ (fineAccuracy L μ ε) (fineInitialBound L μ ε) : Measure _))), inferInstance⟩
noncomputable def saddleCalls (p σ L μ Δ G ε δ : ℝ) : ℕ :=
  recoveryCalls p σ L μ (fineAccuracy L μ ε) (fineInitialBound L μ ε) (outerConfidence L Δ ε δ)+
    coarseCalls p σ L μ Δ G (coarseAccuracy L ε) (outerConfidence L Δ ε δ) (outerSteps L Δ ε)
noncomputable def saddlePlan {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p σ L μ Δ G ε δ : ℝ) (seed : SaddleSeed p σ L μ Δ G ε) (initial : E × F) :
    QueryPlan (E × F) (E × F) E (saddleCalls p σ L μ Δ G ε δ) :=
  (coarsePlan p σ L μ Δ G (coarseAccuracy L ε) (outerConfidence L Δ ε δ)
    (outerSteps L Δ ε) seed.1 initial).bind (fun selected =>
      (recoveryPlan p σ L μ (fineAccuracy L μ ε) (fineInitialBound L μ ε)
        (outerConfidence L Δ ε δ) seed.2 selected.1 selected.2).map Prod.fst)
noncomputable def saddleAlgorithm {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p σ L μ Δ G ε δ : ℝ) (initial : E × F) : Algorithm (E × F) (E × F) E :=
  QueryPlan.algorithm (saddleSeedLaw p σ L μ Δ G ε) initial initial.1
    (saddleCalls p σ L μ Δ G ε δ) (fun seed => saddlePlan p σ L μ Δ G ε δ seed initial)

end LongTails.Algorithms.HeavyTailSaddleEstimator
