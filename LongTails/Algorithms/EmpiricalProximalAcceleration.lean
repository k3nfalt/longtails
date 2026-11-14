import LongTails.Setups.FiniteSumStrongGrowthConvex
import LongTails.Algorithms.Katyusha
import LongTails.Algorithms.ProximalStorm

namespace LongTails.Algorithms.EmpiricalProximalAcceleration

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthConvex

noncomputable def batchSize (p : Params) : ℕ := max 1 (min p.n ⌈1024 * p.ρ⌉₊)

instance (p : Params) : NeZero (batchSize p) :=
  ⟨by unfold batchSize; omega⟩

noncomputable def regularization (p : Params) : ℝ := 1024 * p.L / batchSize p

noncomputable def innerParams (p : Params) (c : p.E) :
    LongTails.Setups.CompositeFiniteSumStronglyConvex.Params where
  E := p.E
  n := batchSize p
  L := p.L
  μ := regularization p
  Δ := 1
  ε := 1 / (2 ^ 20 * p.ρ * (1 + p.L / regularization p) ^ 4)
  x0 := c

noncomputable def innerEpochs (p : Params) : ℕ :=
  12 * Katyusha.tuning (innerParams p p.x0) *
    Nat.clog 2 ⌈14 * (2 ^ 20 * p.ρ * (1 + p.L / regularization p) ^ 4)⌉₊

noncomputable def innerCost (p : Params) : ℕ :=
  (4 * (2 * batchSize p) + 1 * batchSize p) * innerEpochs p

abbrev BatchIndices (p : Params) := Fin (batchSize p) → Fin p.n

abbrev InnerSeeds (p : Params) :=
  Fin (innerEpochs p) → Fin (2 * batchSize p) → Fin (batchSize p)

noncomputable def indices (p : Params) (ξ : BatchIndices p) : BatchIndices p :=
  if h : batchSize p = p.n then fun i => Fin.cast h i else ξ

noncomputable def quadraticProx (p : Params) (c : p.E) (a : ℝ) (z v : p.E) : p.E :=
  (1 + a * regularization p)⁻¹ • (z - a • v + (a * regularization p) • c)

noncomputable def translatePlan (p : Params) (c : p.E) (ι : BatchIndices p)
    {U : Type*} : {K : ℕ} →
    QueryPlan (LongTails.Setups.CompositeFiniteSumStronglyConvex.Query (innerParams p c))
      p.E U K → QueryPlan (Fin p.n × p.E) p.E U K
  | _, .done u => .done u
  | _, .ask (.gradient i x) next =>
    .ask (ι i, x) (fun v => translatePlan p c ι (next v))
  | _, .ask (.prox a z v) next =>
    .ask (0, c) (fun _ => translatePlan p c ι (next (quadraticProx p c a z v)))

noncomputable def innerPlan (p : Params) (c : p.E) (ι : BatchIndices p)
    (ξ : InnerSeeds p) : QueryPlan (Fin p.n × p.E) p.E p.E (innerCost p) :=
  translatePlan p c ι (QueryPlan.map Katyusha.State.snapshot
    (Katyusha.allPlan (innerParams p c) (innerEpochs p) ⟨c, c, c⟩ ξ))

noncomputable def innerOutput (p : Params) (g : Fin p.n × p.E → p.E)
    (c : p.E) (ι : BatchIndices p) (ξ : InnerSeeds p) : p.E :=
  (Katyusha.run (Katyusha.tau (innerParams p c)) (Katyusha.alpha (innerParams p c))
    p.L (Katyusha.theta (innerParams p c)) (2 * batchSize p)
    (fun q => g (ι q.1, q.2)) (quadraticProx p c) (innerEpochs p)
    ⟨c, c, c⟩ ξ).snapshot

noncomputable def gradientPlan (p : Params) (ι : BatchIndices p) (w : p.E) :
    QueryPlan (Fin p.n × p.E) p.E p.E (1 * batchSize p) :=
  (QueryPlan.traverse (batchSize p)
    (fun i => .ask (ι i, w) (fun v => .done v))).map
      (fun values => (batchSize p : ℝ)⁻¹ • values.sum)

abbrev State (p : Params) := ℝ × p.E × p.E

noncomputable def predictor (p : Params) (s : State p) : p.E :=
  ProximalStorm.mixPt (regularization p)⁻¹ s.1 s.2.1 s.2.2

noncomputable def advance (p : Params) (s : State p) (w h : p.E) : State p :=
  let a := ProximalStorm.aNext (regularization p)⁻¹ s.1
  (s.1 + a, w, s.2.2 - a • h)

noncomputable def stepCost (p : Params) : ℕ := 1 * batchSize p + innerCost p

noncomputable def stepPlan (p : Params) (s : State p) (ξ : BatchIndices p × InnerSeeds p) :
    QueryPlan (Fin p.n × p.E) p.E (State p) (stepCost p) :=
  (innerPlan p (predictor p s) (indices p ξ.1) ξ.2).bind fun w =>
    (gradientPlan p (indices p ξ.1) w).map fun h => advance p s w h

noncomputable def step (p : Params) (g : Fin p.n × p.E → p.E)
    (s : State p) (ξ : BatchIndices p × InnerSeeds p) : State p :=
  let w := innerOutput p g (predictor p s) (indices p ξ.1) ξ.2
  advance p s w (FiniteSum.fullGradient (fun q => g (indices p ξ.1 q.1, q.2)) w)

def Seeds (p : Params) (T : ℕ) := Fin T → BatchIndices p × InnerSeeds p

noncomputable instance (p : Params) (T : ℕ) : Fintype (Seeds p T) := by
  unfold Seeds BatchIndices InnerSeeds
  infer_instance

instance (p : Params) (T : ℕ) : Nonempty (Seeds p T) := by
  unfold Seeds BatchIndices InnerSeeds
  infer_instance

instance (p : Params) (T : ℕ) : MeasurableSpace (Seeds p T) := ⊤

instance (p : Params) (T : ℕ) : MeasurableSingletonClass (Seeds p T) :=
  ⟨fun _ => trivial⟩

noncomputable def outerPlan (p : Params) : (T : ℕ) → State p → Seeds p T →
    QueryPlan (Fin p.n × p.E) p.E (State p) (stepCost p * T)
  | 0, s, _ => .done s
  | T + 1, s, ξ => (stepPlan p s (ξ 0)).bind
      (fun next => outerPlan p T next (fun i => ξ i.succ))

noncomputable def run (p : Params) (g : Fin p.n × p.E → p.E) :
    (T : ℕ) → State p → Seeds p T → State p
  | 0, s, _ => s
  | T + 1, s, ξ => run p g T (step p g s (ξ 0)) (fun i => ξ i.succ)

noncomputable def output (p : Params) (g : Fin p.n × p.E → p.E)
    (T : ℕ) (ξ : Seeds p T) : p.E := (run p g T (0, p.x0, p.x0) ξ).2.1

noncomputable def method (p : Params) (T : ℕ) :
    Algorithm (Fin p.n × p.E) p.E p.E :=
  QueryPlan.algorithm ⟨(PMF.uniformOfFintype (Seeds p T)).toMeasure, inferInstance⟩
    (0, p.x0) p.x0 (stepCost p * T)
    (fun ξ => (outerPlan p T (0, p.x0, p.x0) ξ).map fun s => s.2.1)

end LongTails.Algorithms.EmpiricalProximalAcceleration
