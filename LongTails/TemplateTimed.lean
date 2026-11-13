import LongTails.Template
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory

namespace OracleTemplate

universe uP uD uI

inductive TimedEvent (n : ℕ) (Query Reply : Type)
  | start
  | replied (query : Query) (reply : Reply)
  | received (source : Fin n) (payload : List ℝ)

inductive TimedAction (n : ℕ) (Query : Type)
  | call (query : Query)
  | send (targets : Finset (Fin n)) (payload : List ℝ)
  | abort

inductive Header (n : ℕ)
  | call (node : Fin n) (id : ℕ)
  | send (source : Fin n) (targets : Finset (Fin n)) (size : ℕ) (id : ℕ)
  | abort (node : Fin n)

inductive Completion (n : ℕ)
  | done (id : ℕ)
  | delivered (id : ℕ) (target : Fin n)
  deriving DecidableEq

structure TimedAlgorithm (n : ℕ) (Query Reply Output : Type) where
  Seed : Type := Unit
  [seedSpace : MeasurableSpace Seed]
  law : ProbabilityMeasure Seed := by exact ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  State : Type
  root : Fin n
  initial : Fin n → Seed → State
  react : Fin n → ℝ → State → TimedEvent n Query Reply → State × List (TimedAction n Query)
  output : State → Output

attribute [instance] TimedAlgorithm.seedSpace

structure Environment (n : ℕ) where
  Seed : Type := Unit
  [seedSpace : MeasurableSpace Seed]
  law : ProbabilityMeasure Seed := by exact ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  State : Type
  initial : Seed → State
  submit : State → ℝ → Header n → State
  next : State → Option (ℝ × Completion n × State)

attribute [instance] Environment.seedSpace

structure TimedConfig (n : ℕ) (Query Reply State EnvState : Type) where
  now : ℝ
  states : Fin n → State
  env : EnvState
  nextId : ℕ
  calls : List (ℕ × Fin n × Query)
  sends : List (ℕ × Fin n × Finset (Fin n) × List ℝ)
  histories : Fin n → List ((Fin 1 × Query) × Reply)

section Execution

variable {n : ℕ} {Query Reply Output : Type}
  (oracles : Fin n → Oracle Query Reply) (E : Environment n)
  (A : TimedAlgorithm n Query Reply Output)

abbrev TimedSeed := A.Seed × E.Seed × ((v : Fin n) → (k : ℕ) → (oracles v).Seed k)

abbrev TimedConfigOf := TimedConfig n Query Reply A.State E.State

def issueAction (v : Fin n) (c : TimedConfigOf E A) :
    TimedAction n Query → TimedConfigOf E A
  | .call query =>
      { c with
        env := E.submit c.env c.now (.call v c.nextId)
        nextId := c.nextId + 1
        calls := c.calls ++ [(c.nextId, v, query)] }
  | .send targets payload =>
      { c with
        env := E.submit c.env c.now (.send v targets payload.length c.nextId)
        nextId := c.nextId + 1
        sends := c.sends ++ [(c.nextId, v, targets, payload)] }
  | .abort =>
      { c with
        env := E.submit c.env c.now (.abort v)
        calls := c.calls.filter fun entry => entry.2.1 ≠ v }

def deliverEvent (v : Fin n) (event : TimedEvent n Query Reply) (c : TimedConfigOf E A) :
    TimedConfigOf E A :=
  let reaction := A.react v c.now (c.states v) event
  reaction.2.foldl (issueAction E A v) { c with states := Function.update c.states v reaction.1 }

def handleCompletion (oracleSeed : (v : Fin n) → (k : ℕ) → (oracles v).Seed k)
    (c : TimedConfigOf E A) : Completion n → TimedConfigOf E A
  | .done id =>
      match c.calls.find? (fun entry => entry.1 = id) with
      | none => c
      | some (_, v, query) =>
          let history := c.histories v
          let reply := (oracles v).answer history (0, query) (oracleSeed v history.length)
          deliverEvent E A v (.replied query reply)
            { c with
              calls := c.calls.filter fun entry => entry.1 ≠ id
              histories := Function.update c.histories v (history ++ [((0, query), reply)]) }
  | .delivered id target =>
      match c.sends.find? (fun entry => entry.1 = id ∧ target ∈ entry.2.2.1) with
      | none => c
      | some (_, source, _, payload) =>
          deliverEvent E A target (.received source payload)
            { c with
              sends := c.sends.map fun entry =>
                if entry.1 = id then (entry.1, entry.2.1, entry.2.2.1.erase target, entry.2.2.2)
                else entry }

noncomputable def runTimed (oracleSeed : (v : Fin n) → (k : ℕ) → (oracles v).Seed k)
    (T : ℝ) : ℕ → TimedConfigOf E A → TimedConfigOf E A
  | 0, c => c
  | fuel + 1, c =>
      match E.next c.env with
      | none => c
      | some (t, completion, env) =>
          let now := max t c.now
          if T < now then c
          else runTimed oracleSeed T fuel
            (handleCompletion oracles E A oracleSeed { c with now := now, env := env } completion)

def initialTimedConfig (seed : A.Seed) (envSeed : E.Seed) : TimedConfigOf E A :=
  (List.finRange n).foldl (fun c v => deliverEvent E A v .start c)
    { now := 0
      states := fun v => A.initial v seed
      env := E.initial envSeed
      nextId := 0
      calls := []
      sends := []
      histories := fun _ => [] }

noncomputable def executeTimed (T : ℝ) (fuel : ℕ) (seed : TimedSeed oracles E A) : Output :=
  A.output ((runTimed oracles E A seed.2.2 T fuel
    (initialTimedConfig E A seed.1 seed.2.1)).states A.root)

noncomputable def timedLaw : ProbabilityMeasure (TimedSeed oracles E A) :=
  ⟨(A.law : Measure A.Seed).prod ((E.law : Measure E.Seed).prod
    (Measure.pi fun v => ((oracles v).law : Measure _))), inferInstance⟩

end Execution

structure TimedSetup where
  Params : Type uP
  Public : Type uD
  numNodes : Public → ℕ
  Instance : Public → Type uI
  Query : Public → Type
  Reply : Public → Type
  Output : Public → Type
  publicInput : Params → Public
  valid : Params → Prop
  admissible : (p : Params) → Instance (publicInput p) →
    (Fin (numNodes (publicInput p)) → Oracle (Query (publicInput p)) (Reply (publicInput p))) →
    Environment (numNodes (publicInput p)) → Prop
  successful : {Ω : Type} → [MeasurableSpace Ω] →
    (p : Params) → Instance (publicInput p) →
    (Ω → Output (publicInput p)) → ProbabilityMeasure Ω → Prop
  allowedAlgorithm : (q : Public) →
    TimedAlgorithm (numNodes q) (Query q) (Reply q) (Output q) → Prop :=
    fun _ _ => True

def TimedConvergence (S : TimedSetup) (time : S.Params → ℝ) : Prop :=
  ∃ makeAlgorithm : (q : S.Public) →
      TimedAlgorithm (S.numNodes q) (S.Query q) (S.Reply q) (S.Output q),
    (∀ p, S.valid p →
      ∀ (I : S.Instance (S.publicInput p))
        (oracles : Fin (S.numNodes (S.publicInput p)) →
          Oracle (S.Query (S.publicInput p)) (S.Reply (S.publicInput p)))
        (environment : Environment (S.numNodes (S.publicInput p))),
        S.admissible p I oracles environment →
          let A := makeAlgorithm (S.publicInput p)
          ∃ minFuel : ℕ, ∀ fuel, minFuel ≤ fuel →
            S.successful p I (executeTimed oracles environment A (time p) fuel)
              (timedLaw oracles environment A)) ∧
    ∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (makeAlgorithm (S.publicInput p))

end OracleTemplate
