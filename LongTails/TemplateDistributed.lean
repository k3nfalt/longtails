import LongTails.Template
import Mathlib.Basic.NNReal.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.PNat.Defs

open MeasureTheory

namespace DistributedTemplate

universe uP uD uI

abbrev Time := NNReal

def clockBits : ℕ := 64

abbrev ClockReading := Fin (2 ^ clockBits)

inductive Action (ComputeQuery : Type) (numWorkers : ℕ := 1)
  | compute (query : ComputeQuery)
  | communicate (query : Fin numWorkers × List Bool)
  | advance (targetTime : ClockReading)

inductive Event (ComputeReply CommReply : Type)
  | computed (reply : ComputeReply)
  | received (reply : CommReply)
  | wake

structure Algorithm (ComputeQuery ComputeReply CommReply Output : Type)
    (numWorkers : ℕ := 1) where
  clock : Time → ClockReading
  timer : ClockReading → Time
  Seed : Type := Unit
  [seedSpace : MeasurableSpace Seed]
  law : ProbabilityMeasure Seed := by exact ⟨Measure.dirac (), inferInstance⟩
  State : Type
  root : Fin numWorkers
  initial : Fin numWorkers → Seed → State
  query : Fin numWorkers → State → ClockReading → Action ComputeQuery numWorkers × State
  update : Fin numWorkers → State → ClockReading → Event ComputeReply CommReply → State
  output : State → Output

attribute [instance] Algorithm.seedSpace

structure ComputationOracle (Query Reply Seed : Type) (numWorkers : ℕ) where
  State : Type
  initial : Fin numWorkers → Seed → State
  submit : Fin numWorkers → State → Time → Query → State
  answer : Fin numWorkers → State → Time → Option (Reply × State)

structure CommunicationOracle (Reply Seed : Type) (numWorkers : ℕ) where
  State : Type
  initial : Seed → State
  submit : State → Time → Fin numWorkers → (Fin numWorkers × List Bool) → State
  answer : State → Time → Option ((Fin numWorkers × Reply) × State)

structure Oracle (ComputeQuery ComputeReply CommReply : Type) (numWorkers : ℕ := 1) where
  Seed : Type := Unit
  [seedSpace : MeasurableSpace Seed]
  law : ProbabilityMeasure Seed := by exact ⟨Measure.dirac (), inferInstance⟩
  computation : ComputationOracle ComputeQuery ComputeReply Seed numWorkers
  communication : CommunicationOracle CommReply Seed numWorkers

attribute [instance] Oracle.seedSpace

structure OracleState {n : ℕ} {ComputeQuery ComputeReply CommReply : Type}
    (O : Oracle ComputeQuery ComputeReply CommReply n) where
  computation : Fin n → O.computation.State
  communication : O.communication.State

namespace Oracle

variable {n : ℕ} {ComputeQuery ComputeReply CommReply : Type}
  (O : Oracle ComputeQuery ComputeReply CommReply n)

def initial (seed : O.Seed) : OracleState O :=
  ⟨fun v => O.computation.initial v seed, O.communication.initial seed⟩

noncomputable def answer (s : OracleState O) (time : Time) :
    Option ((Fin n × Event ComputeReply CommReply) × OracleState O) :=
  match (List.finRange n).findSome? (fun v =>
    (O.computation.answer v (s.computation v) time).map fun (reply, state) =>
      ((v, Event.computed (CommReply := CommReply) reply),
        { s with computation := Function.update s.computation v state })) with
  | some result => some result
  | none => (O.communication.answer s.communication time).map fun ((v, reply), state) =>
      ((v, .received reply), { s with communication := state })

end Oracle

noncomputable def nextTime {α : Type} (event : Time → Option α)
    (time deadline : Time) : Time := by
  classical
  exact if h : ∃ t, IsLeast {t | time ≤ t ∧ t ≤ deadline ∧
      (t = deadline ∨ (event t).isSome)} t then Classical.choose h else time

structure ExecutionState {n : ℕ} {ComputeQuery ComputeReply CommReply Output : Type}
    (O : Oracle ComputeQuery ComputeReply CommReply n)
    (A : Algorithm ComputeQuery ComputeReply CommReply Output n) where
  time : Time
  deadline : Time
  workers : Fin n → A.State
  wakeTime : Fin n → Time
  turn : ℕ := 0
  oracle : OracleState O

section Execution

variable {n : ℕ} {ComputeQuery ComputeReply CommReply Output : Type}
  (O : Oracle ComputeQuery ComputeReply CommReply n)
  (A : Algorithm ComputeQuery ComputeReply CommReply Output n)

def initial (T : Time) (seed : A.Seed × O.Seed) : ExecutionState O A :=
  { time := 0
    deadline := T
    workers := fun v => A.initial v seed.1
    wakeTime := fun _ => 0
    oracle := O.initial seed.2 }

noncomputable def event (c : ExecutionState O A) (time : Time) :
    Option ((Fin n × Event ComputeReply CommReply) × OracleState O) :=
  match O.answer c.oracle time with
  | some result => some result
  | none =>
      (((List.finRange n).rotate c.turn).find? fun v => c.wakeTime v ≤ time).map fun v =>
        ((v, .wake), c.oracle)

noncomputable def step (c : ExecutionState O A) : Option (ExecutionState O A) :=
  if c.deadline < c.time then none
  else
    match event O A c c.time with
    | some ((v, notification), oracle) =>
        let state := A.update v (c.workers v) (A.clock c.time) notification
        let (action, state) := A.query v state (A.clock c.time)
        let c := { c with
          workers := Function.update c.workers v state
          wakeTime := Function.update c.wakeTime v c.time
          turn := v.val + 1
          oracle := oracle }
        match action with
        | .compute query =>
            some { c with
              oracle := { c.oracle with
                computation := Function.update c.oracle.computation v
                  (O.computation.submit v (c.oracle.computation v) c.time query) } }
        | .communicate (target, bits) =>
            some { c with
              oracle := { c.oracle with
                communication := O.communication.submit c.oracle.communication c.time v
                  (target, bits ++ List.replicate clockBits false) } }
        | .advance targetTime =>
            some { c with wakeTime := Function.update c.wakeTime v (max c.time (A.timer targetTime)) }
    | none =>
        if c.time = c.deadline then none
        else some { c with time := nextTime (event O A c) c.time c.deadline }

noncomputable def run : ℕ → ExecutionState O A → ExecutionState O A
  | 0, c => c
  | k + 1, c =>
      match step O A c with
      | none => c
      | some next => run k next

def FiniteEvents (time : Time) (seed : A.Seed × O.Seed) : Prop :=
  ∀ T ≤ time, ∃ k : ℕ, step O A (run O A k (initial O A T seed)) = none

noncomputable def execute (T : Time) (seed : A.Seed := by exact ())
    (oracleSeed : O.Seed := by exact ()) : Output := by
  classical
  let c := initial O A T (seed, oracleSeed)
  let final := if h : ∃ k : ℕ, step O A (run O A k c) = none then
    run O A (Nat.find h) c else c
  exact A.output (final.workers A.root)

noncomputable def law : ProbabilityMeasure (A.Seed × O.Seed) :=
  ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩

end Execution

structure Setup where
  Params : Type uP
  Public : Type uD
  numWorkers : Public → ℕ+
  Instance : Public → Type uI
  ComputeQuery : Public → Type
  ComputeReply : Public → Type
  CommReply : Public → Type
  Output : Public → Type
  publicInput : Params → Public
  valid : Params → Prop
  admissible : (p : Params) → Instance (publicInput p) →
    Oracle (ComputeQuery (publicInput p))
      (ComputeReply (publicInput p)) (CommReply (publicInput p)) (numWorkers (publicInput p)) → Prop
  successful : {Ω : Type} → [MeasurableSpace Ω] →
    (p : Params) → Instance (publicInput p) →
    (Ω → Output (publicInput p)) → ProbabilityMeasure Ω → Prop
  allowedAlgorithm : (q : Public) →
    Algorithm (ComputeQuery q) (ComputeReply q) (CommReply q)
      (Output q) (numWorkers q) → Prop :=
    fun _ _ => True

def TimedConvergence (S : Setup) (time : S.Params → Time) : Prop :=
  ∃ makeAlgorithm : (q : S.Public) →
      Algorithm (S.ComputeQuery q) (S.ComputeReply q) (S.CommReply q)
        (S.Output q) (S.numWorkers q),
    ∀ p, S.valid p →
      let A := makeAlgorithm (S.publicInput p)
      S.allowedAlgorithm (S.publicInput p) A ∧
      ∀ (I : S.Instance (S.publicInput p))
        (O : Oracle (S.ComputeQuery (S.publicInput p))
          (S.ComputeReply (S.publicInput p)) (S.CommReply (S.publicInput p))
          (S.numWorkers (S.publicInput p))),
        S.admissible p I O →
          (∀ᵐ seed ∂(law O A : Measure _), FiniteEvents O A (time p) seed) ∧
          S.successful p I (fun seed => execute O A (time p) seed.1 seed.2) (law O A)

end DistributedTemplate
