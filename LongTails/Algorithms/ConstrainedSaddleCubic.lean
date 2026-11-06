import LongTails.Setups.ConstrainedMinimaxSecondOrder
import LongTails.Algorithms.Extragradient
import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.AuxiliaryPlan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.ConstrainedSaddleCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def quadraticModel (w : E) (c : ℝ) (g : E) (A : E →L[ℝ] E) (v : E) : ℝ :=
  c + ⟪g, v - w⟫ + ⟪v - w, A (v - w)⟫ / 2

open LongTails.Setups.ConstrainedMinimaxSecondOrder

def feasible (p : Params) : Set (Space p) := {w | w.snd ∈ p.Y}

noncomputable def operatorReply {p : Params} (z : p.E) (w g : Space p) : Space p :=
  WithLp.toLp 2 (g.fst + (2 * p.L) • (w.fst - z), -g.snd)

noncomputable def projectedStep {p : Params} (η : ℝ) (z : p.E) (w query g : Space p) : Space p :=
  OracleTemplate.SaddlePoint.project (feasible p) (w - η • operatorReply z query g)

noncomputable def startupSteps (p : Params) : ℕ :=
  ⌈16 * p.L / p.μ * Real.log (1 + 32 * p.ρ * p.B / p.μ ^ 2)⌉₊

noncomputable def refinementSteps (p : Params) : ℕ :=
  1 + ⌈2 * Real.log (33 + 512 * p.L * p.μ / (p.ρ * p.ε))⌉₊

noncomputable def residualTolerance (p : Params) : ℝ :=
  min (p.μ ^ 2 / (32 * p.ρ)) (p.ε / (128 * (p.L / p.μ + 2 * Real.sqrt (p.L / p.μ) + 1)))

noncomputable def segmentLength (p : Params) : ℝ :=
  p.μ / (16 * p.ρ * Real.sqrt (4 + p.L / p.μ))

noncomputable def extraPlan {p : Params} (z : p.E) (w : Space p) :
    OracleTemplate.QueryPlan (Space p) (spec.Reply p) (Space p) 2 :=
  .ask w fun first =>
    let u := projectedStep (1 / (6 * p.L)) z w w first.2.1
    .ask u fun second => .done (projectedStep (1 / (6 * p.L)) z w u second.2.1)

noncomputable def initialPlan {p : Params} (z : p.E) :
    (n : ℕ) → Space p → OracleTemplate.QueryPlan (Space p) (spec.Reply p) (Space p) (2 * n)
  | 0, w => .done w
  | n + 1, w => OracleTemplate.QueryPlan.bind (extraPlan z w) (initialPlan z n)

def AffineSaddle {p : Params} (z : p.E) (w g : Space p)
    (A : Space p →L[ℝ] Space p) (v : Space p) : Prop :=
  v.snd ∈ p.Y ∧ (g + A (v - w)).fst + (2 * p.L) • (v.fst - z) = 0 ∧
    ∀ y ∈ p.Y, ⟪(g + A (v - w)).snd, y - v.snd⟫ ≤ 0

noncomputable def affineStep {p : Params} (z : p.E) (w g : Space p)
    (A : Space p →L[ℝ] Space p) : Space p := by
  classical
  exact if h : ∃ v, AffineSaddle z w g A v then h.choose else w

def correction {p : Params} (w g : Space p) (A : Space p →L[ℝ] Space p)
    (v gv : Space p) : Space p := gv - (g + A (v - w))

noncomputable def newtonPlan {p : Params} (z : p.E) (w : Space p) :
    OracleTemplate.QueryPlan (Space p) (spec.Reply p) (Space p × Space p) 2 :=
  .ask w fun first =>
    let v := affineStep z w first.2.1 first.2.2
    .ask v fun second => .done (v, correction w first.2.1 first.2.2 v second.2.1)

noncomputable def refinePlan {p : Params} (z : p.E) :
    (n : ℕ) → Space p × Space p →
      OracleTemplate.QueryPlan (Space p) (spec.Reply p) (Space p × Space p) (2 * n)
  | 0, state => .done state
  | n + 1, state => OracleTemplate.QueryPlan.bind (newtonPlan z state.1) (refinePlan z n)

noncomputable def segmentCount {p : Params} (z z' : p.E) : ℕ :=
  max 1 ⌈‖z' - z‖ / segmentLength p⌉₊

noncomputable def pathCenter {p : Params} (z z' : p.E) (m i : ℕ) : p.E :=
  z + ((i : ℝ) / m) • (z' - z)

noncomputable def trackPlan {p : Params} (z z' : p.E) (m : ℕ) :
    (i n : ℕ) → Space p × Space p →
      OracleTemplate.QueryPlan (Space p) (spec.Reply p) (Space p × Space p) (2 * refinementSteps p * n)
  | _, 0, state => .done state
  | i, n + 1, state => OracleTemplate.QueryPlan.bind
      (refinePlan (pathCenter z z' m (i + 1)) (refinementSteps p) state)
      (trackPlan z z' m (i + 1) n)

noncomputable def modelScale (p : Params) : ℝ := p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3

noncomputable def modelEnvelope {p : Params} (w : Space p) (c : ℝ) (g : Space p)
    (A : Space p →L[ℝ] Space p) (z : p.E) : ℝ :=
  ⨅ u, value (quadraticModel w c g A) u + p.L * ‖u - z‖ ^ 2

noncomputable def modelObjective {p : Params} (w : Space p) (c : ℝ) (g : Space p)
    (A : Space p →L[ℝ] Space p) (z0 z : p.E) : ℝ :=
  modelEnvelope w c g A z + modelScale p * ‖z - z0‖ ^ 3 / 3

noncomputable def cubicCenter {p : Params} (w : Space p) (c : ℝ) (g : Space p)
    (A : Space p →L[ℝ] Space p) (z0 : p.E) : p.E := by
  classical
  exact if h : ∃ z, ∀ u, modelObjective w c g A z0 z ≤ modelObjective w c g A z0 u
    then h.choose else z0

noncomputable def outerPlan {p : Params} (z : p.E) (state : Space p × Space p) :
    OracleTemplate.QueryPlan (Space p) (spec.Reply p) p.E 1 :=
  .ask state.1 fun reply => .done (cubicCenter state.1 reply.1 (reply.2.1 - state.2) reply.2.2 z)

open LongTails.Algorithms.AuxiliaryPlan

noncomputable def outerSteps (p : Params) : ℕ :=
  1 + ⌈96 * p.Δ * Real.sqrt (modelScale p) / (p.ε * Real.sqrt p.ε)⌉₊

def liftPlan {Q R U : Type} : {k : ℕ} → OracleTemplate.QueryPlan Q R U k → TwoPlan Q R U
  | _, .done value => .done value
  | _, .ask q next => .ask 0 q (fun r => liftPlan (next r))

noncomputable def runOuter {p : Params} : ℕ → p.E → Space p × Space p →
    TwoPlan (Space p) (spec.Reply p) p.E
  | 0, _, state => .done state.1.fst
  | n + 1, z, state =>
    (liftPlan (outerPlan z state)).andThen fun z' =>
      (liftPlan (trackPlan z z' (segmentCount z z') 0 (segmentCount z z') state)).andThen fun next =>
        if ‖z' - z‖ ^ 2 ≤ p.ε / (4 * modelScale p) then .done next.1.fst
        else runOuter n z' next

noncomputable def fullPlan (p : Params) : TwoPlan (Space p) (spec.Reply p) p.E :=
  (liftPlan (initialPlan p.x0 (startupSteps p) (WithLp.toLp 2 (p.x0, p.y0)))).andThen fun w =>
    (liftPlan (refinePlan p.x0 (refinementSteps p) (w, 0))).andThen fun state =>
      runOuter (outerSteps p) p.x0 state

noncomputable def method (p : Params) : OracleTemplate.Algorithm (Space p) (spec.Reply p) p.E where
  State := TwoPlan (Space p) (spec.Reply p) p.E
  initial _ := fullPlan p
  query state := (0, (TwoPlan.index (WithLp.toLp 2 (p.x0, p.y0)) state).2)
  update := TwoPlan.advance
  output := TwoPlan.result p.x0

noncomputable def output (p : Params) (O : OracleTemplate.Oracle (Space p) (spec.Reply p))
    (K : ℕ) (ω : (k : ℕ) → O.Seed k) : p.E :=
  OracleTemplate.execute O (method p) (fun _ => K) () ω

end LongTails.Algorithms.ConstrainedSaddleCubic
