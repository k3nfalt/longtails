import LongTails.Algorithms.ClippedExtragradientSamples
import LongTails.Algorithms.EnergyHessianReuse
import LongTails.Algorithms.ClippedExtragradient
import LongTails.Algorithms.ContinuizedQuasar
import LongTails.Algorithms.RobustGradientEstimator
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators

namespace OracleTemplate.ProjectedClippedExtragradient

structure Tuning where
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  G : ℝ
  σ : ℝ
  ε : ℝ
  δ : ℝ

noncomputable def curvature (t : Tuning) : ℝ :=
  (t.L0 + t.L1 * t.G + t.L1 * t.ε) * (1 + t.L1 * t.R)

noncomputable def rootBound (t : Tuning) : ℝ :=
  t.G + 16 * (t.L0 + t.L1 * t.G) * t.R + t.ε * (1 + 8 * t.L1 * t.R)

noncomputable def stageCount (t : Tuning) : ℕ :=
  ⌈Real.log (2 + 2 ^ 20 * curvature t * t.R / t.ε) / Real.log 2⌉₊ + 1

noncomputable def repetitions (t : Tuning) : ℕ :=
  ⌈Real.log (2 * stageCount t / t.δ) / Real.log 2⌉₊ + 1

noncomputable def regularization (t : Tuning) (s : ℕ) : ℝ :=
  2 ^ s * t.ε / (2 ^ 20 * stageCount t * t.R)

noncomputable def radius (t : Tuning) (s : ℕ) : ℝ := t.R / 2 ^ s

noncomputable def localScale (t : Tuning) (s : ℕ) : ℝ :=
  2 ^ 20 * (curvature t * (1 + t.L1 * radius t s) + regularization t s * (1 + t.L1 * radius t s) ^ 4)

noncomputable def batchSize (t : Tuning) (s : ℕ) : ℕ :=
  max 1 ⌈2 ^ 23 * t.σ ^ 2 / (regularization t s * localScale t s * radius t s ^ 2)⌉₊

noncomputable def innerSteps (t : Tuning) (s : ℕ) : ℕ :=
  ⌈2 ^ 16 * localScale t s / regularization t s⌉₊

noncomputable def finalBatchSize (t : Tuning) : ℕ := max 1 ⌈2 ^ 20 * t.σ ^ 2 / t.ε ^ 2⌉₊

noncomputable def finalStepSize (t : Tuning) : ℝ :=
  1 / (64 * (t.L0 + t.L1 * rootBound t + t.L1 * t.ε + regularization t (stageCount t - 1)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def halfStep (P : E → E) (b S : ℝ) (x g : E) : E :=
  P (x - ClippedExtragradient.stepSize b S g • g)

noncomputable def finishStep (P : E → E) (d γ : ℝ) (c x g : E) : E :=
  c + clip (2 * d) (P (x - γ • g) - c)

noncomputable def batchStep {Ω : Type*} (P : E → E) (n : ℕ) (b S d r : ℝ)
    (anchor center : E) (g : E → Ω → E) (x : E)
    (samples : (Fin n → Ω) × (Fin n → Ω)) : E :=
  let first := ClippedExtragradient.regularizedReply r anchor x
    ((1 / (n : ℝ)) • ∑ i, g x (samples.1 i))
  let γ := ClippedExtragradient.stepSize b S first
  let y := halfStep P b S x first
  finishStep P d γ center x (ClippedExtragradient.regularizedReply r anchor y
    ((1 / (n : ℝ)) • ∑ i, g y (samples.2 i)))

noncomputable def aggregate {k : ℕ} (d : ℝ) (c : E) (v : Fin k → E) : E :=
  c + clip (2 * d) (RobustGradient.pilotCenter d (fun i => v i - c))

noncomputable def trialOutput {Ω : Type*} (P : E → E) (n m : ℕ) (b S d r : ℝ)
    (anchor center : E) (g : E → Ω → E)
    (samples : Fin n → (Fin m → Ω) × (Fin m → Ω)) : E :=
  ContinuizedSimilarQuasar.iterateSamples (batchStep P m b S d r anchor center g) n center samples

noncomputable def confidenceOutput {Ω : Type*} (P : E → E) (n m k : ℕ) (b S d r : ℝ)
    (anchor center : E) (g : E → Ω → E)
    (samples : Fin k → Fin n → (Fin m → Ω) × (Fin m → Ω)) : E :=
  aggregate d center (fun i => trialOutput P n m b S d r anchor center g (samples i))

noncomputable def residualOutput (P : E → E) (t : Tuning) (anchor x g : E) : E :=
  P (x - finalStepSize t • ClippedExtragradient.regularizedReply
    (regularization t (stageCount t - 1)) anchor x g)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def sumPlan (x : E) : (n : ℕ) → QueryPlan (Fin 2 × E) E E n
  | 0 => .done 0
  | n + 1 => .ask (0, x) fun g => QueryPlan.map (g + ·) (sumPlan x n)

noncomputable def meanPlan (n : ℕ) (x : E) : QueryPlan (Fin 2 × E) E E n :=
  QueryPlan.map ((1 / (n : ℝ)) • ·) (sumPlan x n)

noncomputable def stepPlan (t : Tuning) (s : ℕ) (anchor center x : E) :
    QueryPlan (Fin 2 × E) E E ((1 + batchSize t s + 1) + batchSize t s) :=
  QueryPlan.bind (meanPlan (batchSize t s) x) fun raw =>
    let first := ClippedExtragradient.regularizedReply (regularization t s) anchor x raw
    let γ := ClippedExtragradient.stepSize t.L1 (localScale t s) first
    .ask (1, x - γ • first) fun y =>
      QueryPlan.bind (meanPlan (batchSize t s) y) fun rawSecond =>
        .ask (1, x - γ • ClippedExtragradient.regularizedReply (regularization t s) anchor y rawSecond)
          fun z => .done (center + clip (2 * radius t s) (z - center))

noncomputable def repeatPlan {c : ℕ} (step : E → QueryPlan (Fin 2 × E) E E c) :
    (n : ℕ) → E → QueryPlan (Fin 2 × E) E E (c * n)
  | 0, x => .done x
  | n + 1, x => QueryPlan.bind (step x) (repeatPlan step n)

noncomputable def stageCalls (t : Tuning) (s : ℕ) : ℕ :=
  ((1 + batchSize t s + 1) + batchSize t s) * innerSteps t s * repetitions t

noncomputable def stagePlan (t : Tuning) (s : ℕ) (anchor center : E) :
    QueryPlan (Fin 2 × E) E E (stageCalls t s) :=
  QueryPlan.map (fun values : List E => aggregate (radius t s) center
    (fun i : Fin (repetitions t) => values[i.val]?.getD center))
    (QueryPlan.traverse (repetitions t) fun _ =>
      repeatPlan (stepPlan t s anchor center) (innerSteps t s) center)

noncomputable def finalPlan (t : Tuning) (anchor x : E) :
    QueryPlan (Fin 2 × E) E E (1 + finalBatchSize t * repetitions t) :=
  QueryPlan.bind (QueryPlan.traverse (repetitions t) fun _ => meanPlan (finalBatchSize t) x)
    fun values =>
      let estimate := RobustGradient.pilotCenter (t.ε / 16)
        (fun i : Fin (repetitions t) => values[i.val]?.getD 0)
      .ask (1, x - finalStepSize t • ClippedExtragradient.regularizedReply
        (regularization t (stageCount t - 1)) anchor x estimate) fun y => .done y

noncomputable def runCalls (t : Tuning) : ℕ → ℕ → ℕ
  | _, 0 => 1 + finalBatchSize t * repetitions t
  | s, n + 1 => runCalls t (s + 1) n + stageCalls t s

noncomputable def runPlan (t : Tuning) : (s n : ℕ) → E → E →
    QueryPlan (Fin 2 × E) E E (runCalls t s n)
  | _, 0, anchor, center => finalPlan t anchor center
  | s, n + 1, anchor, center => QueryPlan.bind (stagePlan t s anchor center) fun w =>
      runPlan t (s + 1) n (if n = 0 then anchor else (1 / 2 : ℝ) • (anchor + w)) w

noncomputable def algorithm (t : Tuning) (x0 : E) : Algorithm E E E 2 :=
  LongTails.Algorithms.EnergyHessianReuse.channelAlgorithm (0, x0) x0
    (runPlan t 0 (stageCount t) x0 x0)

noncomputable def output (t : Tuning) (x0 : E) (O : Oracle E E 2)
    (budget : Fin 2 → ℕ) (ξ : (k : ℕ) → O.Seed k) : E :=
  execute O (algorithm t x0) budget () ξ

def sampleIndex (m : ℕ) (i : Fin (m + m)) : Fin ((1 + m + 1) + m) :=
  ⟨if i.val < m then i.val else i.val + 1, by split_ifs <;> have hi := i.isLt <;> omega⟩

def stepSamples {Ω : Type*} (m : ℕ) (ξ : Fin ((1 + m + 1) + m) → Ω) :
    (Fin m → Ω) × (Fin m → Ω) :=
  ClippedExtragradient.splitBatches m (fun i => ξ (sampleIndex m i))

def trialSamples {Ω : Type*} (m n : ℕ) (ξ : Fin (((1 + m + 1) + m) * n) → Ω) :
    Fin n → (Fin m → Ω) × (Fin m → Ω) :=
  fun j => stepSamples m (ClippedExtragradient.groupSamples ((1 + m + 1) + m) n ξ j)

noncomputable def stageSamples {Ω : Type*} (t : Tuning) (s : ℕ)
    (ξ : Fin (stageCalls t s) → Ω) :
    Fin (repetitions t) → Fin (innerSteps t s) →
      (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω) :=
  fun j => trialSamples (batchSize t s) (innerSteps t s)
    (ClippedExtragradient.groupSamples (((1 + batchSize t s + 1) + batchSize t s) * innerSteps t s)
      (repetitions t) ξ j)

noncomputable def blockOutput {Ω : Type*} (P : E → E) (t : Tuning) (s : ℕ)
    (anchor center : E) (g : E → Ω → E) (ξ : Fin (stageCalls t s) → Ω) : E :=
  confidenceOutput P (innerSteps t s) (batchSize t s) (repetitions t) t.L1 (localScale t s)
    (radius t s) (regularization t s) anchor center g (stageSamples t s ξ)

abbrev ProcessState (E : Type*) := ℕ × E × E

noncomputable def finalCalls (t : Tuning) : ℕ := 1 + finalBatchSize t * repetitions t

noncomputable def finalSamples {Ω : Type*} (t : Tuning) (ξ : Fin (finalCalls t) → Ω)
    (j : Fin (repetitions t)) (i : Fin (finalBatchSize t)) : Ω :=
  ξ ⟨finalBatchSize t * j.val + i.val, by
    have hj := Nat.mul_le_mul_left (finalBatchSize t) (Nat.succ_le_of_lt j.isLt)
    have hi := i.isLt
    simp only [Nat.mul_succ] at hj
    unfold finalCalls
    omega⟩

noncomputable def finalEstimate {Ω : Type*} (t : Tuning) (x : E)
    (g : E → Ω → E) (ξ : Fin (finalCalls t) → Ω) : E :=
  RobustGradient.pilotCenter (t.ε / 16)
    (fun j : Fin (repetitions t) => (1 / (finalBatchSize t : ℝ)) •
      ∑ i : Fin (finalBatchSize t), g x (finalSamples t ξ j i))

noncomputable def finalBlock {Ω : Type*} (P : E → E) (t : Tuning) (anchor x : E)
    (g : E → Ω → E) (ξ : Fin (finalCalls t) → Ω) : E :=
  residualOutput P t anchor x (finalEstimate t x g ξ)

noncomputable def phaseCost (t : Tuning) (state : ProcessState E) : ℕ :=
  if state.1 < stageCount t then stageCalls t state.1 else finalCalls t

noncomputable def phaseReply {Ω : Type*} (P : E → E) (t : Tuning) (g : E → Ω → E)
    (n : ℕ) (state : ProcessState E) (ξ : Fin n → Ω) : E :=
  if state.1 < stageCount t then
    if hn : n = stageCalls t state.1 then
      blockOutput P t state.1 state.2.1 state.2.2 g (fun i => ξ (Fin.cast hn.symm i))
    else state.2.2
  else
    if hn : n = finalCalls t then
      finalBlock P t state.2.1 state.2.2 g (fun i => ξ (Fin.cast hn.symm i))
    else state.2.2

noncomputable def phaseNext {Ω : Type*} (P : E → E) (t : Tuning) (g : E → Ω → E)
    (n : ℕ) (state : ProcessState E) (ξ : Fin n → Ω) : ProcessState E :=
  let w := phaseReply P t g n state ξ
  (state.1 + 1, (if state.1 + 1 < stageCount t then (1 / 2 : ℝ) • (state.2.1 + w) else state.2.1), w)

end OracleTemplate.ProjectedClippedExtragradient
