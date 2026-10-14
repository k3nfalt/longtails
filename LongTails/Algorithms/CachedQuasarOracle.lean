import LongTails.Algorithms.CachedQuasar
import LongTails.Algorithms.QueryPlan
import LongTails.Setups.SimilarFiniteSumQuasar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section

namespace OracleTemplate.SimilarQuasar

open LongTails.Setups.SimilarFiniteSumQuasar

def fullPlan (p : Params) (w : p.E) :
    QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) (1 * p.n) :=
  QueryPlan.map (fun values => ((p.n : ℝ)⁻¹ • values.sum, values.headD 0))
    (QueryPlan.traverse p.n (fun i => .ask (i, w) (fun v => .done v)))

def innerPlan (p : Params) (θ : ℝ) (full reference : p.E) :
    (k : ℕ) → (p.E × p.E) → QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) k
  | 0, s => .done s
  | k + 1, s => .ask (0, query θ s) (fun v =>
      innerPlan p θ full reference k (update p.γ θ p.μ s (v - reference + full)))

def epochPlan (p : Params) (θ : ℝ) (m : ℕ) (s : p.E × p.E) :
    QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) (m + 1 * p.n) :=
  QueryPlan.bind (fullPlan p s.1) (fun cache => innerPlan p θ cache.1 cache.2 m s)

def allPlan (p : Params) (θ : ℝ) (m : ℕ) :
    (S : ℕ) → (p.E × p.E) →
      QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) ((m + 1 * p.n) * S)
  | 0, s => .done s
  | S + 1, s => QueryPlan.bind (epochPlan p θ m s) (fun next => allPlan p θ m S next)

def cachedQuasar (p : Params) (θ : ℝ) (m S : ℕ) :
    Algorithm (Fin p.n × p.E) p.E p.E :=
  QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    (0, p.x0) p.x0 ((m + 1 * p.n) * S)
    (fun _ => QueryPlan.map Prod.fst (allPlan p θ m S (p.x0, p.x0)))

end OracleTemplate.SimilarQuasar
