import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.RecursiveGradient
import LongTails.Setups.FiniteSumSmoothNonconvex
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

namespace OracleTemplate.NonconvexFiniteSum

open LongTails.Setups.FiniteSumSmoothNonconvex

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def fullGradientPlan (x : E) : QueryPlan (Fin n × E) E E (1 * n) :=
  QueryPlan.map (fun values => (n : ℝ)⁻¹ • values.sum)
    (QueryPlan.traverse n (fun i => .ask (i, x) (fun reply => .done reply)))

noncomputable def differencePlan {b : ℕ} (x y : E) (samples : Fin b → Fin n) :
    QueryPlan (Fin n × E) E E (2 * b) :=
  QueryPlan.map (fun values => (b : ℝ)⁻¹ • values.sum)
    (QueryPlan.traverse b (fun j => .ask (samples j, x)
      (fun gx => .ask (samples j, y) (fun gy => .done (gx - gy)))))

noncomputable def recursivePlan (η : ℝ) (b : ℕ) :
    (k : ℕ) → E → E → (Fin k → Fin b → Fin n) →
      QueryPlan (Fin n × E) E (E × List E) (2 * b * k)
  | 0, x, v, _ => .done (x - η • v, [x])
  | k + 1, x, v, samples =>
    let y := x - η • v
    QueryPlan.bind (differencePlan y x (samples 0)) (fun diff =>
      QueryPlan.map (fun result => (result.1, x :: result.2))
        (recursivePlan η b k y (v + diff) (fun i => samples i.succ)))

noncomputable def epochPlan (η : ℝ) (b k : ℕ) (x : E)
    (samples : Fin k → Fin b → Fin n) :
    QueryPlan (Fin n × E) E (E × List E) (2 * b * k + 1 * n) :=
  QueryPlan.bind (fullGradientPlan x) (fun v => recursivePlan η b k x v samples)

noncomputable def allEpochsPlan (η : ℝ) (b k : ℕ) :
    (S : ℕ) → E → (Fin S → Fin k → Fin b → Fin n) →
      QueryPlan (Fin n × E) E (E × List E) ((2 * b * k + 1 * n) * S)
  | 0, x, _ => .done (x, [])
  | S + 1, x, samples =>
    QueryPlan.bind (epochPlan η b k x (samples 0)) (fun epoch =>
      QueryPlan.map (fun rest => (rest.1, epoch.2 ++ rest.2))
        (allEpochsPlan η b k S epoch.1 (fun i => samples i.succ)))

def RecursiveSeeds (n b k S : ℕ) :=
  (Fin S → Fin k → Fin b → Fin n) × Fin ((k + 1) * S)

instance (n b k S : ℕ) : Fintype (RecursiveSeeds n b k S) :=
  inferInstanceAs (Fintype ((Fin S → Fin k → Fin b → Fin n) × Fin ((k + 1) * S)))

instance (n b k S : ℕ) [NeZero n] [NeZero S] : Nonempty (RecursiveSeeds n b k S) :=
  inferInstanceAs (Nonempty ((Fin S → Fin k → Fin b → Fin n) × Fin ((k + 1) * S)))

instance (n b k S : ℕ) : MeasurableSpace (RecursiveSeeds n b k S) := ⊤

instance (n b k S : ℕ) : MeasurableSingletonClass (RecursiveSeeds n b k S) :=
  ⟨fun _ => trivial⟩

noncomputable def recursiveGradient [NeZero n] (η : ℝ) (b k S : ℕ) [NeZero S]
    (x0 : E) : Algorithm (Fin n × E) E E :=
  QueryPlan.algorithm
    ⟨(PMF.uniformOfFintype (RecursiveSeeds n b k S)).toMeasure, inferInstance⟩
    (0, x0) x0 ((2 * b * k + 1 * n) * S) (fun seed =>
      QueryPlan.map (fun result => result.2.getD seed.2.val x0)
        (allEpochsPlan η b k S x0 seed.1))

noncomputable def tunedRecursiveGradient (p : Params) : Algorithm (Fin p.n × p.E) p.E p.E :=
  let b := Nat.sqrt p.n + 1
  let S := max 1 ⌈4 * p.L * p.Δ / ((b : ℝ) * p.ε ^ 2)⌉₊
  haveI : NeZero S := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))⟩
  recursiveGradient (1 / (2 * p.L)) b (b - 1) S p.x0

end OracleTemplate.NonconvexFiniteSum
