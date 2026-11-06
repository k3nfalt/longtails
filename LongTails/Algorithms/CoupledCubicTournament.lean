import LongTails.Setups.StrongGrowthFiniteSumSecondOrder
import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.PLMinimaxCubic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log

namespace LongTails.Algorithms.CoupledCubicTournament

open OracleTemplate
open LongTails.Setups.StrongGrowthFiniteSumSecondOrder

noncomputable section

abbrev Model (p : Params) := p.E × (p.E →L[ℝ] p.E)

noncomputable def modelStep (p : Params) (m : Model p) : p.E :=
  OracleTemplate.PLMinimax.envelopeCubicStep m.1 m.2 (p.ρ / 2)

noncomputable def graphNorm (p : Params) (m : Model p) (v : p.E) : ℝ :=
  ‖m.2 v‖ + p.ρ * ‖modelStep p m‖ * ‖v‖

noncomputable def anchoredCompatible (p : Params) (a b : Model p) : Prop :=
  (∀ v, ‖(a.2 - b.2) v‖ ≤ (1 / 1000000 : ℝ) * graphNorm p a v) ∧
  ‖a.1 - b.1 + (a.2 - b.2) (modelStep p a)‖ ≤
    (1 / 1000000 : ℝ) * p.ρ * ‖modelStep p a‖ ^ 2

noncomputable def compatible (p : Params) (a b : Model p) : Prop :=
  anchoredCompatible p a b ∧ anchoredCompatible p b a

noncomputable def modelAt (p : Params) (models : List (Model p)) (j : ℕ) : Model p :=
  models[j]?.getD 0

noncomputable def qualifies (p : Params) (models : List (Model p)) (j : ℕ) : Prop := by
  classical
  exact models.length < 2 * ((Finset.range models.length).filter
    (fun k => compatible p (modelAt p models j) (modelAt p models k))).card

noncomputable def selectedIndex (p : Params) (models : List (Model p)) : ℕ := by
  classical
  exact if h : ∃ j, j < models.length ∧ qualifies p models j then Nat.find h else 0

noncomputable def selectedStep (p : Params) (models : List (Model p)) : p.E :=
  modelStep p (modelAt p models (selectedIndex p models))

noncomputable def nextState (p : Params) (state : p.E × Bool) (models : List (Model p)) :
    p.E × Bool :=
  if state.2 then state else
    let u := selectedStep p models
    (state.1 + u, decide (‖u‖ ≤ Real.sqrt (p.ε / p.ρ) / 5))

noncomputable def batchPlan (p : Params) (b : ℕ) (x : p.E) (ξ : Fin b → Fin p.n) :
    QueryPlan (Fin p.n × p.E) (Model p) (Model p) (1 * b) :=
  QueryPlan.map (fun replies => (b : ℝ)⁻¹ • replies.sum)
    (QueryPlan.traverse b (fun i => .ask (ξ i, x) (fun reply => .done reply)))

noncomputable def roundPlan (p : Params) (b K : ℕ) (x : p.E)
    (ξ : Fin K → Fin b → Fin p.n) :
    QueryPlan (Fin p.n × p.E) (Model p) (List (Model p)) ((1 * b) * K) :=
  QueryPlan.traverse K (fun j => batchPlan p b x (ξ j))

def Seeds (p : Params) (b K T : ℕ) := Fin T → Fin K → Fin b → Fin p.n

noncomputable instance (p : Params) (b K T : ℕ) : Fintype (Seeds p b K T) := by
  unfold Seeds
  infer_instance

instance (p : Params) (b K T : ℕ) : Nonempty (Seeds p b K T) := by
  unfold Seeds
  infer_instance

instance (p : Params) (b K T : ℕ) : MeasurableSpace (Seeds p b K T) := by
  unfold Seeds
  infer_instance

instance (p : Params) (b K T : ℕ) : MeasurableSingletonClass (Seeds p b K T) := by
  unfold Seeds
  infer_instance


noncomputable def sampledModel (p : Params) (b : ℕ) (g : Fin p.n × p.E → Model p)
    (x : p.E) (ξ : Fin b → Fin p.n) : Model p := (b : ℝ)⁻¹ • ∑ i, g (ξ i, x)

noncomputable def sampledModels (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (x : p.E) (ξ : Fin K → Fin b → Fin p.n) : List (Model p) :=
  List.ofFn (fun j => sampledModel p b g x (ξ j))

noncomputable def runState (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p) :
    (T : ℕ) → p.E × Bool → Seeds p b K T → p.E × Bool
  | 0, state, _ => state
  | T + 1, state, ξ => runState p b K g T
      (nextState p state (sampledModels p b K g state.1 (ξ 0))) (fun i => ξ i.succ)

noncomputable def allPlan (p : Params) (b K : ℕ) : (T : ℕ) → p.E × Bool →
    Seeds p b K T → QueryPlan (Fin p.n × p.E) (Model p) p.E (((1 * b) * K) * T)
  | 0, state, _ => .done state.1
  | T + 1, state, ξ => QueryPlan.bind (roundPlan p b K state.1 (ξ 0))
      (fun models => allPlan p b K T (nextState p state models) (fun i => ξ i.succ))

noncomputable def output (p : Params) (b K T : ℕ) (g : Fin p.n × p.E → Model p)
    (ξ : Seeds p b K T) : p.E :=
  QueryPlan.eval g (allPlan p b K T (p.x0, false) ξ)

noncomputable def method (p : Params) (b K T : ℕ) :
    Algorithm (Fin p.n × p.E) (Model p) p.E :=
  QueryPlan.algorithm ⟨(PMF.uniformOfFintype (Seeds p b K T)).toMeasure, inferInstance⟩
    (0, p.x0) p.x0 (((1 * b) * K) * T) (allPlan p b K T (p.x0, false))

def batchSize (p : Params) : ℕ := ⌈10 ^ 20 * p.κ * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ)⌉₊

def roundCount (p : Params) : ℕ := ⌈16000 * Real.sqrt p.ρ * p.Δ / (p.ε * Real.sqrt p.ε)⌉₊ + 1

def modelsPerRound (p : Params) : ℕ := Nat.log 2 (3 * roundCount p) + 1

end

end LongTails.Algorithms.CoupledCubicTournament
