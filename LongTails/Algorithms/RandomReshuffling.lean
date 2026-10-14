import LongTails.Algorithms.QueryPlan
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import Mathlib.GroupTheory.Perm.Finite

namespace OracleTemplate.RandomReshuffling

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

def pass (g : I → E → E) (η : ℝ) : List I → E → E
  | [], x => x
  | i :: is, x => pass g η is (x - η • g i x)

def epochs (g : I → E → E) (η : ℝ) : List (List I) → E → E
  | [], x => x
  | order :: orders, x => epochs g η orders (pass g η order x)

def passPlan (η : ℝ) : (order : List I) → E → QueryPlan (I × E) E E order.length
  | [], x => .done x
  | i :: is, x => .ask (i, x) (fun reply => passPlan η is (x - η • reply))

def epochPlan {n : ℕ} (η : ℝ) (order : Equiv.Perm (Fin n)) (x : E) :
    QueryPlan (Fin n × E) E E n :=
  Eq.ndrec (motive := fun k => QueryPlan (Fin n × E) E E k)
    (passPlan η (List.ofFn order) x) List.length_ofFn

def epochsPlan {n : ℕ} (η : ℝ) : (K : ℕ) → E → (Fin K → Equiv.Perm (Fin n)) →
    QueryPlan (Fin n × E) E E (n * K)
  | 0, x, _ => .done x
  | K + 1, x, orders =>
    QueryPlan.bind (epochPlan η (orders 0) x) (fun y =>
      epochsPlan η K y (fun k => orders k.succ))

def Seeds (n K : ℕ) := Fin K → Equiv.Perm (Fin n)

instance (n K : ℕ) : Fintype (Seeds n K) := inferInstanceAs (Fintype (Fin K → Equiv.Perm (Fin n)))
instance (n K : ℕ) : Nonempty (Seeds n K) := ⟨fun _ => Equiv.refl _⟩
instance (n K : ℕ) : MeasurableSpace (Seeds n K) := ⊤
instance (n K : ℕ) : MeasurableSingletonClass (Seeds n K) := ⟨fun _ => trivial⟩

noncomputable def algorithm {n : ℕ} [NeZero n] (η : ℝ) (K : ℕ) (x0 : E) :
    Algorithm (Fin n × E) E E :=
  QueryPlan.algorithm (S := Seeds n K) ⟨(PMF.uniformOfFintype (Seeds n K)).toMeasure, inferInstance⟩
    (0, x0) x0 (n * K) (fun seed => epochsPlan η K x0 seed)

end OracleTemplate.RandomReshuffling
