import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

namespace OracleTemplate

universe uP uD uI uQ uR uO

structure Algorithm (Query : Type uQ) (Reply : Type uR) (Output : Type uO) (numOracles : ℕ := 1) where
  Seed : Type := Unit
  [seedSpace : MeasurableSpace Seed]
  law : ProbabilityMeasure Seed := by exact ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  State : Type (max uQ uR uO)
  initial : Seed → State
  query : State → Fin numOracles × Query
  update : State → Reply → State
  output : State → Output

attribute [instance] Algorithm.seedSpace

structure Oracle (Query : Type uQ) (Reply : Type uR) (numOracles : ℕ := 1) where
  Seed : ℕ → Type := fun _ => Unit
  [seedSpace : ∀ k, MeasurableSpace (Seed k)]
  law : ProbabilityMeasure ((k : ℕ) → Seed k) := by
    exact ⟨MeasureTheory.Measure.dirac (fun _ => ()), inferInstance⟩
  answer : (history : List ((Fin numOracles × Query) × Reply)) →
    (Fin numOracles × Query) → Seed history.length → Reply

attribute [instance] Oracle.seedSpace

private def _run
    {Query : Type uQ} {Reply : Type uR} {Output : Type uO}
    {numOracles : ℕ}
    (oracle : List ((Fin numOracles × Query) × Reply) → (Fin numOracles × Query) → Reply)
    (A : Algorithm Query Reply Output numOracles) :
    Nat → List ((Fin numOracles × Query) × Reply) → (Fin numOracles → ℕ) → A.State →
      Output × List ((Fin numOracles × Query) × Reply)
  | 0, history, _, state => (A.output state, history)
  | k + 1, history, remaining, state =>
      let query := A.query state
      if remaining query.1 = 0 then (A.output state, history)
      else
        let reply := oracle history query
        let remaining := Function.update remaining query.1 (remaining query.1 - 1)
        _run oracle A k (history ++ [(query, reply)]) remaining (A.update state reply)

def executeWithTrace
    {Query : Type uQ} {Reply : Type uR} {Output : Type uO}
    {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles) (A : Algorithm Query Reply Output numOracles)
    (budget : Fin numOracles → ℕ) (seed : A.Seed := by exact ())
    (oracleSeed : (k : ℕ) → oracle.Seed k := by exact fun _ => ()) :
    Output × List ((Fin numOracles × Query) × Reply) :=
  _run (fun history query => oracle.answer history query (oracleSeed history.length))
    A (∑ i, budget i) [] budget (A.initial seed)

def execute
    {Query : Type uQ} {Reply : Type uR} {Output : Type uO}
    {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles) (A : Algorithm Query Reply Output numOracles)
    (budget : Fin numOracles → ℕ) (seed : A.Seed := by exact ())
    (oracleSeed : (k : ℕ) → oracle.Seed k := by exact fun _ => ()) : Output :=
  (executeWithTrace oracle A budget seed oracleSeed).1

structure Setup where
  numOracles : ℕ := 1
  Params : Type uP
  Public : Type uD
  Instance : Public → Type uI
  Query : Public → Type uQ
  Reply : Public → Type uR
  Output : Public → Type uO
  publicInput : Params → Public
  valid : Params → Prop
  admissible : (p : Params) → Instance (publicInput p) →
    Oracle (Query (publicInput p)) (Reply (publicInput p)) numOracles → Prop
  successful : {Ω : Type} → [MeasurableSpace Ω] →
    (p : Params) → Instance (publicInput p) →
    (Ω → Output (publicInput p)) → ProbabilityMeasure Ω → Prop :=
    fun _ _ _ _ => False
  allowedAlgorithm : (p : Public) → Algorithm (Query p) (Reply p) (Output p) numOracles → Prop :=
    fun _ _ => True

def Convergence (S : Setup)
    (budget : S.Params → Fin S.numOracles → ℕ) : Prop :=
  ∃ makeAlgorithm : (p : S.Public) → Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles,
    (∀ p, S.valid p →
      ∀ (I : S.Instance (S.publicInput p))
        (oracle : Oracle (S.Query (S.publicInput p)) (S.Reply (S.publicInput p)) S.numOracles),
        S.admissible p I oracle →
          let A := makeAlgorithm (S.publicInput p)
          let result := fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
            execute oracle A (budget p) seed.1 seed.2
          S.successful p I result
            ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩) ∧
    ∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (makeAlgorithm (S.publicInput p))

end OracleTemplate
