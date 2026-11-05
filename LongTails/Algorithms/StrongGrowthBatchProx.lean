import LongTails.Setups.FiniteSumStrongGrowthStronglyConvex
import LongTails.Algorithms.Katyusha

namespace LongTails.Algorithms.StrongGrowthBatchProx

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthStronglyConvex

noncomputable def batchSize (p : Params) : ℕ := max 1 (min p.n ⌈128 * p.ρ⌉₊)

instance (p : Params) : NeZero (batchSize p) :=
  ⟨by unfold batchSize; omega⟩

noncomputable def innerParams (p : Params) (c : p.E) :
    LongTails.Setups.CompositeFiniteSumStronglyConvex.Params where
  E := p.E
  n := batchSize p
  L := p.L
  μ := p.μ
  Δ := (p.L + p.μ) / 2
  ε := p.μ / 1024
  x0 := c

noncomputable def innerEpochs (p : Params) : ℕ :=
  12 * Katyusha.tuning (innerParams p p.x0) *
    Nat.clog 2 ⌈7168 * (p.L + p.μ) / p.μ⌉₊

noncomputable def innerCost (p : Params) : ℕ :=
  (4 * (2 * batchSize p) + 1 * batchSize p) * innerEpochs p

abbrev BatchIndices (p : Params) := Fin (batchSize p) → Fin p.n

abbrev InnerSeeds (p : Params) :=
  Fin (innerEpochs p) → Fin (2 * batchSize p) → Fin (batchSize p)

noncomputable def indices (p : Params) (ξ : BatchIndices p) : BatchIndices p :=
  if h : batchSize p = p.n then fun i => Fin.cast h i else ξ

noncomputable def quadraticProx (p : Params) (c : p.E) (a : ℝ) (z v : p.E) : p.E :=
  (1 + a * p.μ)⁻¹ • (z - a • v + (a * p.μ) • c)

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

noncomputable def outerPlan (p : Params) : (T : ℕ) → p.E → Seeds p T →
    QueryPlan (Fin p.n × p.E) p.E p.E (innerCost p * T)
  | 0, c, _ => .done c
  | T + 1, c, ξ => QueryPlan.bind
    (innerPlan p c (indices p (ξ 0).1) (ξ 0).2)
    (fun next => outerPlan p T next (fun i => ξ i.succ))

noncomputable def output (p : Params) (g : Fin p.n × p.E → p.E) :
    (T : ℕ) → p.E → Seeds p T → p.E
  | 0, c, _ => c
  | T + 1, c, ξ => output p g T
    (innerOutput p g c (indices p (ξ 0).1) (ξ 0).2) (fun i => ξ i.succ)

noncomputable def method (p : Params) (T : ℕ) :
    Algorithm (Fin p.n × p.E) p.E p.E :=
  QueryPlan.algorithm ⟨(PMF.uniformOfFintype (Seeds p T)).toMeasure, inferInstance⟩
    (0, p.x0) p.x0 (innerCost p * T) (outerPlan p T p.x0)

end LongTails.Algorithms.StrongGrowthBatchProx
