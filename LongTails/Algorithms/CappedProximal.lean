import LongTails.Setups.CappedHessianSimilarConvex
import LongTails.Algorithms.ComponentEnvelope
import Mathlib.Data.Finset.Option

namespace LongTails.Algorithms.CappedProximal

universe u

open LongTails.Setups.CappedHessianSimilarConvex
open OracleTemplate.ComponentEnvelope

noncomputable def contacts (p : Params) (indices : Fin p.s → Option (Fin p.m)) :
    Finset (Fin p.m) := Finset.univ.biUnion (fun j => (indices j).toFinset)

noncomputable def roundQuery (p : Params) (indices : Fin p.s → Option (Fin p.m))
    (request : Fin p.m → Operation × p.E) : Query p where
  clients := contacts p indices
  cap := by
    classical
    calc
      (contacts p indices).card ≤ ∑ j : Fin p.s, (indices j).toFinset.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin p.s, 1 := by
        apply Finset.sum_le_sum
        intro j _
        cases indices j <;> simp
      _ = p.s := by simp
  request := request

noncomputable def gradientQuery (p : Params) (indices : Fin p.s → Option (Fin p.m))
    (x : p.E) : Query p := roundQuery p indices (fun _ => (.gradient, x))

noncomputable def proximalQuery (p : Params) (indices : Fin p.s → Option (Fin p.m))
    (coefficient : {a : ℝ // 0 < a}) (centers : Fin p.m → p.E) : Query p :=
  roundQuery p indices (fun i => (.prox coefficient, centers i))

def blockIndices (p : Params) (block : ℕ) (j : Fin p.s) : Option (Fin p.m) :=
  if h : block * p.s + j.val < p.m then some ⟨block * p.s + j.val, h⟩ else none

noncomputable def snapshotPlan (p : Params) (x : p.E) :
    ℕ → ℕ → (Fin p.m → p.E) → Program (Query p) (Fin p.m → p.E) (Fin p.m → p.E)
  | 0, _, cache => .done cache
  | k + 1, block, cache =>
      let query := gradientQuery p (blockIndices p block) x
      .ask query fun reply => snapshotPlan p x k (block + 1)
        (fun i => if i ∈ query.clients then reply i else cache i)

noncomputable def correctedProxPlan (p : Params) (indices : Fin p.s → Fin p.m)
    (coefficient : {a : ℝ // 0 < a}) (x g : p.E) :
    Program (Query p) (Fin p.m → p.E) p.E :=
  .ask (gradientQuery p (fun j => some (indices j)) x) fun gradients =>
    .ask (proximalQuery p (fun j => some (indices j)) coefficient
      (fun i => x + coefficient.val⁻¹ • (gradients i - g))) fun points =>
        .done ((p.s : ℝ)⁻¹ • ∑ j, points (indices j))

noncomputable def outerRegularization (p : Params) : ℝ := p.μ + p.δ / Real.sqrt p.m

noncomputable def subproblemConvexity (p : Params) : ℝ := p.μ + outerRegularization p

noncomputable def epochLength (p : Params) : ℕ :=
  ⌈1 + 64 * Real.sqrt (p.δ * (1 + Real.sqrt p.m / p.s) / subproblemConvexity p) +
    2 ^ 20 * p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2)⌉₊

noncomputable def innerRegularization (p : Params) : ℝ :=
  subproblemConvexity p * (epochLength p : ℝ) ^ 2 / 64

noncomputable def outerLength (p : Params) : ℕ :=
  ⌈8 * Real.sqrt (outerRegularization p / p.μ)⌉₊

noncomputable def solveLength (p : Params) : ℕ :=
  1 + ⌈Real.log (2 ^ 20 * subproblemConvexity p * (outerLength p : ℝ) ^ 4 /
    outerRegularization p) / Real.log 8⌉₊

noncomputable def restartCount (p : Params) : ℕ :=
  1 + ⌈Real.log (2 + p.Δ / p.ε) / Real.log 8⌉₊

def snapshotLength (p : Params) : ℕ := (p.m + p.s - 1) / p.s

noncomputable def positiveCoefficient (a : ℝ) : {a : ℝ // 0 < a} :=
  if h : 0 < a then ⟨a, h⟩ else ⟨1, by norm_num⟩

structure State (E : Type*) where
  weight : ℝ
  primal : E
  dual : E

noncomputable def nextWeight (lam A : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * lam * A)) / (2 * lam)

noncomputable def predictor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : ℝ) (state : State E) : E :=
  let a := nextWeight lam state.weight
  (state.weight / (state.weight + a)) • state.primal +
    (a / (state.weight + a)) • state.dual

noncomputable def advance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : ℝ) (state : State E) (z : E) : State E :=
  let a := nextWeight lam state.weight
  ⟨state.weight + a, z, state.dual - (a * lam) • (predictor lam state - z)⟩

abbrev Cohorts (p : Params) := (Fin p.s → Fin p.m) × (Fin p.s → Fin p.m)

noncomputable def epochSteps (p : Params) (center : p.E) (cache : Fin p.m → p.E) :
    (k : ℕ) → (Fin k → Cohorts p) → State p.E →
      Program (Query p) (Fin p.m → p.E) (State p.E)
  | 0, _, state => .done state
  | k + 1, samples, state =>
      let x := predictor (innerRegularization p) state
      .ask (gradientQuery p (fun j => some ((samples 0).1 j)) x) fun gradients =>
        let g := (p.m : ℝ)⁻¹ • (∑ i, cache i) +
          (p.s : ℝ)⁻¹ • (∑ j, (gradients ((samples 0).1 j) - cache ((samples 0).1 j))) +
          outerRegularization p • (x - center)
        (correctedProxPlan p (samples 0).2
          (positiveCoefficient (innerRegularization p + outerRegularization p)) x g).bind fun z =>
            epochSteps p center cache k (fun j => samples j.succ)
              (advance (innerRegularization p) state z)

noncomputable def epochPlan (p : Params) (center start : p.E)
    (samples : Fin (epochLength p) → Cohorts p) : Program (Query p) (Fin p.m → p.E) p.E :=
  (snapshotPlan p start (snapshotLength p) 0 (fun _ => 0)).bind fun cache =>
    (epochSteps p center cache (epochLength p) samples ⟨0, start, start⟩).map State.primal

noncomputable def solvePlan (p : Params) (center : p.E) :
    (k : ℕ) → (Fin k → Fin (epochLength p) → Cohorts p) → p.E →
      Program (Query p) (Fin p.m → p.E) p.E
  | 0, _, start => .done start
  | k + 1, samples, start =>
      (epochPlan p center start (samples 0)).bind fun z =>
        solvePlan p center k (fun j => samples j.succ) z

noncomputable def outerSteps (p : Params) :
    (k : ℕ) → (Fin k → Fin (solveLength p) → Fin (epochLength p) → Cohorts p) →
      State p.E → Program (Query p) (Fin p.m → p.E) (State p.E)
  | 0, _, state => .done state
  | k + 1, samples, state =>
      (solvePlan p (predictor (outerRegularization p) state) (solveLength p)
        (samples 0) state.primal).bind fun z =>
          outerSteps p k (fun j => samples j.succ) (advance (outerRegularization p) state z)

noncomputable def restartsPlan (p : Params) :
    (k : ℕ) → (Fin k → Fin (outerLength p) → Fin (solveLength p) →
      Fin (epochLength p) → Cohorts p) → p.E → Program (Query p) (Fin p.m → p.E) p.E
  | 0, _, start => .done start
  | k + 1, samples, start =>
      (outerSteps p (outerLength p) (samples 0) ⟨0, start, start⟩).bind fun state =>
        restartsPlan p k (fun j => samples j.succ) state.primal

def Seeds (p : Params) := Fin (restartCount p) → Fin (outerLength p) →
  Fin (solveLength p) → Fin (epochLength p) → Cohorts p

noncomputable instance (p : Params) : Fintype (Seeds p) :=
  inferInstanceAs (Fintype (Fin (restartCount p) → Fin (outerLength p) →
    Fin (solveLength p) → Fin (epochLength p) → Cohorts p))

instance (p : Params) : Nonempty (Seeds p) := ⟨fun _ _ _ _ => (fun _ => 0, fun _ => 0)⟩
instance (p : Params) : MeasurableSpace (Seeds p) := ⊤
instance (p : Params) : MeasurableSingletonClass (Seeds p) := ⟨fun _ => trivial⟩

noncomputable def plan (p : Params) (seed : Seeds p) : Program (Query p) (Fin p.m → p.E) p.E :=
  restartsPlan p (restartCount p) seed p.x0

noncomputable def algorithm (p : Params.{u}) : OracleTemplate.Algorithm (Query p) (Fin p.m → p.E) p.E where
  Seed := Seeds p
  seedSpace := inferInstance
  law := ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure, inferInstance⟩
  State := Program (Query p) (Fin p.m → p.E) p.E
  initial := plan p
  query state := (0, state.query (gradientQuery p (fun _ => none) p.x0))
  update := Program.update
  output := Program.output p.x0

noncomputable def output (p : Params.{u}) (oracle : OracleTemplate.Oracle (Query p) (Fin p.m → p.E))
    (budget : ℕ) (seed : Seeds p) (oracleSeed : (k : ℕ) → oracle.Seed k) : p.E :=
  OracleTemplate.execute oracle (algorithm p) (fun _ => budget) seed oracleSeed

end LongTails.Algorithms.CappedProximal
