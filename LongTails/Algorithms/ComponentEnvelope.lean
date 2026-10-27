import LongTails.Setups.InterpolatedGeneralizedFiniteSum
import LongTails.Algorithms.Extragradient
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.ComponentEnvelope

universe u

open LongTails.Setups.InterpolatedGeneralizedFiniteSum

inductive Program (Q R U : Type*) where
  | done : U → Program Q R U
  | ask : Q → (R → Program Q R U) → Program Q R U

namespace Program

variable {Q R U V : Type*}

def bind : Program Q R U → (U → Program Q R V) → Program Q R V
  | .done u, next => next u
  | .ask q rest, next => .ask q (fun r => bind (rest r) next)

def map (f : U → V) (p : Program Q R U) : Program Q R V := p.bind (fun u => .done (f u))

def query (fallback : Q) : Program Q R U → Q
  | .done _ => fallback
  | .ask q _ => q

def update : Program Q R U → R → Program Q R U
  | .done u, _ => .done u
  | .ask _ next, r => next r

def output (fallback : U) : Program Q R U → U
  | .done u => u
  | .ask _ _ => fallback

end Program

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def innerStep (L0 L1 μ : ℝ) (c z reply : E) : E :=
  let r := reply + μ • (z - c)
  z - (1 / (16 * (L0 + μ + L1 * ‖reply‖ + L1 * ‖r‖))) • r

noncomputable def innerPath (g : E → E) (L0 L1 μ : ℝ) (c : E) (k : ℕ) : E :=
  (fun z => innerStep L0 L1 μ c z (g z))^[k] c

noncomputable def innerPlan {n : ℕ} (L0 L1 μ ζ : ℝ) (i : Fin n) (c : E) :
    ℕ → E → Program (Fin n × E) E E
  | 0, z => .done (μ • (c - z))
  | k + 1, z => .ask (i, z) fun reply =>
      if ‖reply + μ • (z - c)‖ ≤ ζ then .done (μ • (c - z))
      else innerPlan L0 L1 μ ζ i c k (innerStep L0 L1 μ c z reply)

noncomputable def smoothing (p : Params.{u}) : ℝ := p.L0 + 8 * p.n * p.L1 ^ 2 * p.ε

noncomputable def epochCount (p : Params.{u}) : ℕ :=
  ⌈Real.sqrt (7200 * smoothing p * p.R ^ 2 / (p.n * p.ε))⌉₊

noncomputable def tolerance (p : Params.{u}) : ℝ :=
  smoothing p * p.R / (1048576 * p.n * ((epochCount p : ℝ) + 4) ^ 3)

noncomputable def innerFuel (p : Params.{u}) : ℕ :=
  ⌈4096 * Real.log (4 + p.L1 * p.R + smoothing p * p.R * (1 + p.L1 * p.R) /
    tolerance p) * (1 + 4 * p.L1 ^ 2 * p.R ^ 2)⌉₊

noncomputable def componentPlan (p : Params.{u}) (i : Fin p.n) (c : p.E) :
    Program (Fin p.n × p.E) p.E p.E :=
  innerPlan p.L0 p.L1 (smoothing p) (tolerance p) i c (innerFuel p) c

noncomputable def projectBall (p : Params.{u}) (x : p.E) : p.E :=
  SaddlePoint.project (Metric.closedBall p.x0 p.R) x

noncomputable def snapshotPlan (p : Params.{u}) (x : p.E) :
    (k : ℕ) → (Fin k → Fin p.n) → Program (Fin p.n × p.E) p.E (Fin k → p.E)
  | 0, _ => .done Fin.elim0
  | k + 1, indices => (componentPlan p (indices 0) x).bind fun first =>
      (snapshotPlan p x k (fun j => indices j.succ)).map (Fin.cons first)

noncomputable def warmupPlan (p : Params.{u}) : (k : ℕ) → (Fin k → Fin p.n) →
    p.E → p.E → Program (Fin p.n × p.E) p.E (p.E × p.E)
  | 0, _, x, total => .done (x, total)
  | k + 1, samples, x, total => (componentPlan p (samples 0) x).bind fun v =>
      warmupPlan p k (fun j => samples j.succ)
        (projectBall p (x - (1 / (2 * smoothing p)) • v)) (total + x)

structure EpochState (E : Type*) where
  y : E
  z : E
  total : E

noncomputable def queryMix (s : ℕ) (snapshot : E) (state : EpochState E) : E :=
  let τ : ℝ := 2 / (s + 4)
  τ • state.z + (1 / 2 : ℝ) • snapshot + (1 / 2 - τ) • state.y

noncomputable def epochUpdate (p : Params.{u}) (s : ℕ) (snapshot v : p.E)
    (state : EpochState p.E) : EpochState p.E :=
  let τ : ℝ := 2 / (s + 4)
  let y := projectBall p (queryMix s snapshot state - (1 / (6 * smoothing p)) • v)
  ⟨y, projectBall p (state.z - (1 / (6 * smoothing p * τ)) • v), state.total + y⟩

noncomputable def epochPlan (p : Params.{u}) (s : ℕ) (snapshot : p.E)
    (cache : Fin p.n → p.E) : (k : ℕ) → (Fin k → Fin p.n) → EpochState p.E →
      Program (Fin p.n × p.E) p.E (EpochState p.E)
  | 0, _, state => .done state
  | k + 1, samples, state =>
      (componentPlan p (samples 0) (queryMix s snapshot state)).bind fun v =>
        let estimator := v - cache (samples 0) + (p.n : ℝ)⁻¹ • ∑ i, cache i
        epochPlan p s snapshot cache k (fun j => samples j.succ)
          (epochUpdate p s snapshot estimator state)

noncomputable def epochsPlan (p : Params.{u}) : (k : ℕ) →
    (Fin k → Fin p.n → Fin p.n) → ℕ → p.E → p.E → p.E →
      Program (Fin p.n × p.E) p.E p.E
  | 0, _, _, snapshot, _, _ => .done snapshot
  | k + 1, samples, s, snapshot, y, z =>
      (snapshotPlan p snapshot p.n id).bind fun cache =>
        (epochPlan p s snapshot cache p.n (samples 0) ⟨y, z, 0⟩).bind fun state =>
          epochsPlan p k (fun j => samples j.succ) (s + 1)
            ((p.n : ℝ)⁻¹ • state.total) state.y state.z

def Seeds (p : Params.{u}) :=
  (Fin (4 * p.n) → Fin p.n) × (Fin (epochCount p) → Fin p.n → Fin p.n)

noncomputable instance (p : Params.{u}) : Fintype (Seeds p) := inferInstanceAs (Fintype (_ × _))
instance (p : Params.{u}) : Nonempty (Seeds p) := ⟨(fun _ => 0, fun _ _ => 0)⟩
instance (p : Params.{u}) : MeasurableSpace (Seeds p) := ⊤
instance (p : Params.{u}) : MeasurableSingletonClass (Seeds p) := ⟨fun _ => trivial⟩

noncomputable def plan (p : Params.{u}) (seed : Seeds p) : Program (Fin p.n × p.E) p.E p.E :=
  (warmupPlan p (4 * p.n) seed.1 p.x0 0).bind fun state =>
    let x := ((4 * p.n : ℕ) : ℝ)⁻¹ • state.2
    epochsPlan p (epochCount p) seed.2 0 x x x

noncomputable def algorithm (p : Params.{u}) : Algorithm (Fin p.n × p.E) p.E p.E where
  Seed := Seeds p
  seedSpace := inferInstance
  law := ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure, inferInstance⟩
  State := Program (Fin p.n × p.E) p.E p.E
  initial := plan p
  query state := (0, state.query (0, p.x0))
  update := Program.update
  output := Program.output p.x0

noncomputable def output (p : Params.{u}) (oracle : Oracle (Fin p.n × p.E) p.E) (K : ℕ)
    (seed : Seeds p) (oracleSeed : (k : ℕ) → oracle.Seed k) : p.E :=
  execute oracle (algorithm p) (fun _ => K) seed oracleSeed

end OracleTemplate.ComponentEnvelope
