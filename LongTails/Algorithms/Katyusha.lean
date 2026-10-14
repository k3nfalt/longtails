import LongTails.Setups.CompositeFiniteSumStronglyConvex
import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.Svrg
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Distributions.Uniform

open scoped BigOperators

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

noncomputable def tuning (p : Params) : ℕ :=
  max 1 ⌈Real.sqrt (p.L / ((2 * p.n : ℕ) * p.μ))⌉₊

noncomputable def tau (p : Params) : ℝ := 1 / (2 * (tuning p : ℝ))

noncomputable def alpha (p : Params) : ℝ :=
  1 / (12 * ((2 * p.n : ℕ) : ℝ) * (tuning p : ℝ) * p.μ)

noncomputable def theta (p : Params) : ℝ := 1 + alpha p * p.μ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def mix (τ : ℝ) (snapshot : E) (s : E × E) : E :=
  τ • s.2 + (1 / 2 : ℝ) • snapshot + (1 / 2 - τ) • s.1

noncomputable def advance (τ α L : ℝ) (prox : ℝ → E → E → E)
    (snapshot : E) (s : E × E) (v : E) : E × E :=
  (prox (1 / (3 * L)) (mix τ snapshot s) v, prox α s.2 v)

noncomputable def innerRun {n : ℕ} (τ α L θ : ℝ)
    (g : Fin n × E → E) (prox : ℝ → E → E → E) (snapshot full : E) :
    (k : ℕ) → (E × E) → (Fin k → Fin n) → (E × E) × E
  | 0, s, _ => (s, 0)
  | k + 1, s, samples =>
    let x := mix τ snapshot s
    let next := advance τ α L prox snapshot s (g (samples 0, x) - g (samples 0, snapshot) + full)
    let rest := innerRun τ α L θ g prox snapshot full k next (fun i => samples i.succ)
    (rest.1, next.1 + θ • rest.2)

noncomputable def weightSum (θ : ℝ) (m : ℕ) : ℝ := ∑ j ∈ Finset.range m, θ ^ j

structure State (E : Type*) where
  snapshot : E
  y : E
  z : E

noncomputable def epoch {n : ℕ} (τ α L θ : ℝ) (m : ℕ)
    (g : Fin n × E → E) (prox : ℝ → E → E → E)
    (s : State E) (samples : Fin m → Fin n) : State E :=
  let result := innerRun τ α L θ g prox s.snapshot (FiniteSum.fullGradient g s.snapshot)
    m (s.y, s.z) samples
  ⟨(weightSum θ m)⁻¹ • result.2, result.1.1, result.1.2⟩

noncomputable def run {n : ℕ} (τ α L θ : ℝ) (m : ℕ)
    (g : Fin n × E → E) (prox : ℝ → E → E → E) :
    (S : ℕ) → State E → (Fin S → Fin m → Fin n) → State E
  | 0, s, _ => s
  | S + 1, s, samples =>
    run τ α L θ m g prox S (epoch τ α L θ m g prox s (samples 0))
      (fun i => samples i.succ)

noncomputable def fullPlan (p : Params) (snapshot : p.E) :
    QueryPlan (Query p) p.E p.E (1 * p.n) :=
  QueryPlan.map (fun values => (p.n : ℝ)⁻¹ • values.sum)
    (QueryPlan.traverse p.n (fun i => .ask (.gradient i snapshot) (fun v => .done v)))

noncomputable def stepPlan (p : Params) (snapshot : p.E) (s : p.E × p.E)
    (full : p.E) (i : Fin p.n) : QueryPlan (Query p) p.E (p.E × p.E) 4 :=
  let x := mix (tau p) snapshot s
  .ask (.gradient i x) (fun gx =>
    .ask (.gradient i snapshot) (fun gs =>
      let v := gx - gs + full
      .ask (.prox (alpha p) s.2 v) (fun z =>
        .ask (.prox (1 / (3 * p.L)) x v) (fun y => .done (y, z)))))

noncomputable def innerPlan (p : Params) (snapshot full : p.E) :
    (k : ℕ) → (p.E × p.E) → (Fin k → Fin p.n) →
      QueryPlan (Query p) p.E ((p.E × p.E) × p.E) (4 * k)
  | 0, s, _ => .done (s, 0)
  | k + 1, s, samples =>
    QueryPlan.bind (stepPlan p snapshot s full (samples 0)) (fun next =>
      QueryPlan.map (fun rest => (rest.1, next.1 + theta p • rest.2))
        (innerPlan p snapshot full k next (fun i => samples i.succ)))

noncomputable def epochPlan (p : Params) (s : State p.E)
    (samples : Fin (2 * p.n) → Fin p.n) :
    QueryPlan (Query p) p.E (State p.E) (4 * (2 * p.n) + 1 * p.n) :=
  QueryPlan.bind (fullPlan p s.snapshot) (fun full =>
    QueryPlan.map (fun result =>
      ⟨(weightSum (theta p) (2 * p.n))⁻¹ • result.2, result.1.1, result.1.2⟩)
      (innerPlan p s.snapshot full (2 * p.n) (s.y, s.z) samples))

noncomputable def allPlan (p : Params) : (S : ℕ) → State p.E →
    (Fin S → Fin (2 * p.n) → Fin p.n) →
      QueryPlan (Query p) p.E (State p.E) ((4 * (2 * p.n) + 1 * p.n) * S)
  | 0, s, _ => .done s
  | S + 1, s, samples =>
    QueryPlan.bind (epochPlan p s (samples 0))
      (fun next => allPlan p S next (fun i => samples i.succ))

def Seeds (p : Params) (S : ℕ) := Fin S → Fin (2 * p.n) → Fin p.n

instance (p : Params) (S : ℕ) : Fintype (Seeds p S) :=
  inferInstanceAs (Fintype (Fin S → Fin (2 * p.n) → Fin p.n))

instance (p : Params) (S : ℕ) : Nonempty (Seeds p S) :=
  inferInstanceAs (Nonempty (Fin S → Fin (2 * p.n) → Fin p.n))

instance (p : Params) (S : ℕ) : MeasurableSpace (Seeds p S) := ⊤
instance (p : Params) (S : ℕ) : MeasurableSingletonClass (Seeds p S) := ⟨fun _ => trivial⟩

noncomputable def katyusha (p : Params) (S : ℕ) : Algorithm (Query p) p.E p.E :=
  QueryPlan.algorithm ⟨(PMF.uniformOfFintype (Seeds p S)).toMeasure, inferInstance⟩
    (.gradient 0 p.x0) p.x0 ((4 * (2 * p.n) + 1 * p.n) * S)
    (fun samples => QueryPlan.map State.snapshot (allPlan p S ⟨p.x0, p.x0, p.x0⟩ samples))

end OracleTemplate.Katyusha
