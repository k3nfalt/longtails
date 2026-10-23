import LongTails.Algorithms.QueryPlan
import LongTails.Setups.FiniteSumWeakMintyInclusion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.VarianceReducedWeakMinty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

abbrev Query (n : ℕ) (E : Type*) := (Fin n × E) ⊕ (ℝ × E)

noncomputable def batchValue (F : Fin n → E → E) (w y : E) {b : ℕ}
    (ξ : Fin b → Fin n) : E :=
  LongTails.Setups.FiniteSumWeakMintyInclusion.operator F w +
    (b : ℝ)⁻¹ • ∑ i, (F (ξ i) y - F (ξ i) w)

noncomputable def estimatorValue (exact : Bool) (F : Fin n → E → E) (w y : E)
    {b : ℕ} (ξ : Fin b → Fin n) : E :=
  if exact then LongTails.Setups.FiniteSumWeakMintyInclusion.operator F y
  else batchValue F w y ξ

def answer (F : Fin n → E → E) (J : ℝ → E → E) : Query n E → E
  | .inl (i, x) => F i x
  | .inr (η, z) => J η z

def fullSumPlan (x : E) : QueryPlan (Query n E) E E n :=
  Eq.rec (motive := fun k _ => QueryPlan (Query n E) E E k)
    ((QueryPlan.traverse (Q := Query n E) (R := E) (c := 1) n
      (fun i => .ask (Sum.inl (i, x)) .done)).map List.sum) (Nat.one_mul n)

noncomputable def fullPlan (x : E) : QueryPlan (Query n E) E E n :=
  (fullSumPlan x).map ((n : ℝ)⁻¹ • ·)

def differencePlan (w y : E) (i : Fin n) : QueryPlan (Query n E) E E 2 :=
  .ask (.inl (i, y)) fun gy => .ask (.inl (i, w)) fun gw => .done (gy - gw)

noncomputable def batchPlan (w fw y : E) {b : ℕ} (ξ : Fin b → Fin n) :
    QueryPlan (Query n E) E E (2 * b) :=
  (QueryPlan.traverse b (fun i => differencePlan w y (ξ i))).map
    (fun values => fw + (b : ℝ)⁻¹ • values.sum)

def estimatorCost (exact : Bool) (n b : ℕ) : ℕ := if exact then n else 2 * b

noncomputable def estimatorPlan (exact : Bool) (w fw y : E) {b : ℕ}
    (ξ : Fin b → Fin n) : QueryPlan (Query n E) E E (estimatorCost exact n b) :=
  match exact with
  | true => fullPlan y
  | false => batchPlan w fw y ξ

noncomputable def picardStepPlan (exact : Bool) (η : ℝ) (z w fw y : E) {b : ℕ}
    (ξ : Fin b → Fin n) :
    QueryPlan (Query n E) E (E × E) (1 + estimatorCost exact n b) :=
  (estimatorPlan exact w fw y ξ).bind fun g =>
    .ask (.inr (η, z - η • g)) fun ynext =>
      .done (ynext, η⁻¹ • (z - ynext) - g)

noncomputable def picardPlan (exact : Bool) (η : ℝ) (z w fw : E) {b : ℕ} :
    (J : ℕ) → (Fin J → Fin b → Fin n) → E × E →
      QueryPlan (Query n E) E (E × E) ((1 + estimatorCost exact n b) * J)
  | 0, _, state => .done state
  | J + 1, ξ, state =>
    (picardStepPlan exact η z w fw state.1 (ξ 0)).bind fun next =>
      picardPlan exact η z w fw J (fun j => ξ j.succ) next

noncomputable def stepPlan (exact : Bool) (η s p : ℝ) (x w fw : E) {b J : ℕ}
    (ξ : (Fin J → Fin b → Fin n) × (Fin b → Fin n)) :
    QueryPlan (Query n E) E (E × (E × E))
      (estimatorCost exact n b + (1 + estimatorCost exact n b) * J) :=
  let z := (1 - p) • x + p • w
  (picardPlan exact η z w fw J ξ.1 (z, 0)).bind fun yv =>
    (estimatorPlan exact w fw yv.1 ξ.2).map fun g =>
      (z - (s * η) • (g + yv.2), yv)

abbrev StepSeed (n b J : ℕ) := (Fin J → Fin b → Fin n) × (Fin b → Fin n)

def stepCost (exact : Bool) (n b J : ℕ) : ℕ :=
  estimatorCost exact n b + (1 + estimatorCost exact n b) * J

noncomputable def stepsPlan (exact : Bool) (η s p : ℝ) (w fw : E) {b J : ℕ} :
    (q : ℕ) → (Fin q → StepSeed n b J) → E →
      QueryPlan (Query n E) E (E × List (E × (E × E))) (stepCost exact n b J * q)
  | 0, _, x => .done (x, [])
  | q + 1, ξ, x =>
    (stepPlan exact η s p x w fw (ξ 0)).bind fun next =>
      (stepsPlan exact η s p w fw q (fun i => ξ i.succ) next.1).map
        (fun rest => (rest.1, next :: rest.2))

abbrev EpochSeed (n b J q : ℕ) := (Fin q → StepSeed n b J) × Fin q

noncomputable def epochPlan (exact : Bool) (η s p : ℝ) (x w : E) {b J q : ℕ}
    (ξ : EpochSeed n b J q) :
    QueryPlan (Query n E) E ((E × E) × List (E × E))
      (stepCost exact n b J * q + n) :=
  (fullPlan w).bind fun fw =>
    (stepsPlan exact η s p w fw q ξ.1 x).map fun states =>
      ((states.1, (states.2.getD ξ.2.val (w, (w, 0))).1), states.2.map Prod.snd)

noncomputable def epochsPlan (exact : Bool) (η s p : ℝ) {b J q : ℕ} :
    (M : ℕ) → (Fin M → EpochSeed n b J q) → E × E →
      QueryPlan (Query n E) E ((E × E) × List (E × E))
        ((stepCost exact n b J * q + n) * M)
  | 0, _, state => .done (state, [])
  | M + 1, ξ, state =>
    (epochPlan exact η s p state.1 state.2 (ξ 0)).bind fun next =>
      (epochsPlan exact η s p M (fun i => ξ i.succ) next.1).map
        (fun rest => (rest.1, next.2 ++ rest.2))

noncomputable def outputPlan (exact : Bool) (η s p : ℝ) (x0 : E) {b J q M : ℕ}
    (ξ : (Fin M → EpochSeed n b J q) × Fin (q * M)) :
    QueryPlan (Query n E) E (E × E) ((stepCost exact n b J * q + n) * M) :=
  (epochsPlan exact η s p M ξ.1 (x0, x0)).map
    (fun states => states.2.getD ξ.2.val (x0, 0))

structure Seeds (n b J q M : ℕ) where
  epochs : Fin M → EpochSeed n b J q
  selection : Fin (q * M)
  deriving Fintype

instance {n b J q M : ℕ} [NeZero n] [NeZero q] [NeZero M] :
    Nonempty (Seeds n b J q M) := by
  have : NeZero (q * M) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M)⟩
  exact ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩

instance (n b J q M : ℕ) : MeasurableSpace (Seeds n b J q M) := ⊤

instance (n b J q M : ℕ) : MeasurableSingletonClass (Seeds n b J q M) :=
  ⟨fun _ => trivial⟩

noncomputable def algorithm (exact : Bool) (η s p : ℝ) (x0 : E) (b J q M : ℕ)
    [NeZero n] [NeZero q] [NeZero M] : Algorithm (Query n E) E (E × E) :=
  QueryPlan.algorithm (S := Seeds n b J q M)
    ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩
    (.inr (η, x0)) (x0, 0) ((stepCost exact n b J * q + n) * M)
    (fun ξ => outputPlan exact η s p x0 (ξ.epochs, ξ.selection))

open LongTails.Setups.FiniteSumWeakMintyInclusion

noncomputable def margin (p : Params) : ℝ := 1 - p.ρ * p.L

noncomputable def exactWork (p : Params) : ℝ :=
  p.n * (1 + p.L ^ 2 * p.R ^ 2 / (margin p ^ 2 * p.ε ^ 2))

noncomputable def batchWork (p : Params) : ℝ :=
  (p.n + p.Λ ^ 2 / p.L ^ 2 +
    (Real.sqrt p.n * p.Λ * p.L + p.Λ ^ 2) * p.R ^ 2 / (margin p ^ 2 * p.ε ^ 2)) /
      margin p ^ 3

noncomputable def useExact (p : Params) : Bool := decide (exactWork p ≤ batchWork p)

noncomputable def epochLength (p : Params) : ℕ :=
  if useExact p then 2 else max 2 ⌈Real.sqrt p.n * p.L / p.Λ⌉₊

noncomputable def batchSize (p : Params) : ℕ :=
  if useExact p then 1 else ⌈524288 * epochLength p * p.Λ ^ 2 / (p.L ^ 2 * margin p ^ 3)⌉₊

noncomputable def innerLength (p : Params) : ℕ :=
  ⌈32 / margin p * Real.log (65536 / margin p ^ 2)⌉₊ + 1

noncomputable def epochCount (p : Params) : ℕ :=
  max 1 ⌈128 * p.L ^ 2 * p.R ^ 2 / (margin p ^ 2 * epochLength p * p.ε ^ 2)⌉₊

instance (p : Params) : NeZero (epochLength p) := by
  constructor
  unfold epochLength
  split <;> omega

instance (p : Params) : NeZero (epochCount p) := by
  constructor
  unfold epochCount
  omega

noncomputable def tunedAlgorithm (p : Params) : Algorithm (Query p.n p.E) p.E (p.E × p.E) := by
  classical
  exact if hn : 0 < p.n then
    letI : NeZero p.n := ⟨Nat.ne_of_gt hn⟩
    algorithm (useExact p) ((2 - margin p) / (2 * p.L)) (margin p / (2 - margin p))
      (epochLength p : ℝ)⁻¹ p.x0 (batchSize p) (innerLength p) (epochLength p) (epochCount p)
  else
    { State := p.E
      initial := fun _ => p.x0
      query := fun x => (0, .inr (0, x))
      update := fun x _ => x
      output := fun x => (x, 0) }

end OracleTemplate.VarianceReducedWeakMinty
