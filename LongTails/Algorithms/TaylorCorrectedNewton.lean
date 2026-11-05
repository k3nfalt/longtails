import LongTails.Algorithms.QueryPlan
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.List.OfFn

namespace LongTails.Algorithms.TaylorCorrectedNewton

open OracleTemplate OracleTemplate.QueryPlan
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Reply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  E × (E →L[ℝ] E)

noncomputable def model (η : ℝ) (z w g : E) (H : E →L[ℝ] E) (v : E) : ℝ :=
  η * (⟪g, v - w⟫ + ⟪v - w, H (v - w)⟫) + ‖v - z‖ ^ 2 / 2

noncomputable def modelPoint (η ρ : ℝ) (c z w g : E) (H : E →L[ℝ] E) : E := by
  classical
  exact if h : ∃ v ∈ Metric.closedBall c ρ, IsMinOn (model η z w g H) (Metric.closedBall c ρ) v
  then Classical.choose h else c

noncomputable def residual (w v : E) (cached fresh : Reply E) : E :=
  fresh.1 - cached.1 - cached.2 (v - w)

noncomputable def corrected (η : ℝ) (w v : E) (cached fresh : Reply E) : E :=
  v - (2 * η) • residual w v cached fresh

noncomputable def collect {n : ℕ} (w : E) : (k : ℕ) → (Fin k → Fin n) →
    QueryPlan (Fin n × E) (Reply E) (Fin k → Reply E) k
  | 0, _ => .done Fin.elim0
  | k + 1, indices => .ask (indices 0, w) (fun reply =>
      QueryPlan.map (Fin.cons reply) (collect w k (fun i => indices i.succ)))

noncomputable def snapshot {n : ℕ} (w : E) :
    QueryPlan (Fin n × E) (Reply E) (Fin n → Reply E) n := collect w n id

noncomputable def meanGradient {n : ℕ} (cache : Fin n → Reply E) : E :=
  (n : ℝ)⁻¹ • ∑ i, (cache i).1

noncomputable def meanHessian {n : ℕ} (cache : Fin n → Reply E) : E →L[ℝ] E :=
  (n : ℝ)⁻¹ • ∑ i, (cache i).2

noncomputable def step {n : ℕ} (η ρ : ℝ) (c z w : E) (cache : Fin n → Reply E)
    (i : Fin n) : QueryPlan (Fin n × E) (Reply E) (E × E) 1 :=
  let v := modelPoint η ρ c z w (meanGradient cache) (meanHessian cache)
  .ask (i, v) (fun fresh => .done (corrected η w v (cache i) fresh, v))

noncomputable def inner {n : ℕ} (η ρ : ℝ) (c w : E) (cache : Fin n → Reply E) :
    (k : ℕ) → E → (Fin k → Fin n) →
      QueryPlan (Fin n × E) (Reply E) (E × (Fin k → E)) k
  | 0, z, _ => .done (z, Fin.elim0)
  | k + 1, z, indices => QueryPlan.bind (step η ρ c z w cache (indices 0))
      (fun zv => QueryPlan.map (fun rest => (rest.1, Fin.cons zv.2 rest.2))
        (inner η ρ c w cache k zv.1 (fun i => indices i.succ)))

noncomputable def epoch {n : ℕ} (η ρ : ℝ) (c z w : E)
    (indices : Fin n → Fin n) (selection : Fin n) :
    QueryPlan (Fin n × E) (Reply E) (E × E × (Fin n → E)) (n + n) :=
  QueryPlan.bind (snapshot w) (fun cache =>
    QueryPlan.map (fun result => (result.1, result.2 selection, result.2))
      (inner η ρ c w cache n z indices))

abbrev EpochSeed (n : ℕ) := (Fin n → Fin n) × Fin n

noncomputable def epochs {n : ℕ} (η ρ : ℝ) (c : E) :
    (m : ℕ) → E → E → (Fin m → EpochSeed n) →
      QueryPlan (Fin n × E) (Reply E) (E × E × List E) ((n + n) * m)
  | 0, z, w, _ => .done (z, w, [])
  | m + 1, z, w, seeds => QueryPlan.bind (epoch η ρ c z w (seeds 0).1 (seeds 0).2)
      (fun result => QueryPlan.map
        (fun rest => (rest.1, rest.2.1, List.ofFn result.2.2 ++ rest.2.2))
        (epochs η ρ c m result.1 result.2.1 (fun i => seeds i.succ)))

noncomputable def restart {n : ℕ} (η ρ : ℝ) (c y : E) (m : ℕ)
    (seeds : Fin m → EpochSeed n) (selection : Fin (n * m)) :
    QueryPlan (Fin n × E) (Reply E) E ((n + n) * m) :=
  QueryPlan.map (fun result => result.2.2.getD selection.val y) (epochs η ρ c m y y seeds)

abbrev RestartSeed (n m : ℕ) := (Fin m → EpochSeed n) × Fin (n * m)

noncomputable def restarts {n : ℕ} (η ρ : ℝ) (c : E) (m : ℕ) :
    (J : ℕ) → E → (Fin J → RestartSeed n m) →
      QueryPlan (Fin n × E) (Reply E) E (((n + n) * m) * J)
  | 0, y, _ => .done y
  | J + 1, y, seeds => QueryPlan.bind (restart η ρ c y m (seeds 0).1 (seeds 0).2)
      (fun next => restarts η ρ c m J next (fun i => seeds i.succ))

noncomputable def augmentPlan {n : ℕ} {U : Type*} (augment : E → Reply E → Reply E) :
    {k : ℕ} → QueryPlan (Fin n × E) (Reply E) U k →
      QueryPlan (Fin n × E) (Reply E) U k
  | _, .done value => .done value
  | _, .ask query next => .ask query (fun reply => augmentPlan augment (next (augment query.2 reply)))

end LongTails.Algorithms.TaylorCorrectedNewton
