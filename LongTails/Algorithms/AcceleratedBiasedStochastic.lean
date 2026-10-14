import LongTails.Algorithms.Accelerated
import LongTails.Algorithms.Clipping

namespace OracleTemplate.BiasedStochasticGradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def projectedUpdate (D R : ℝ) (x0 : E) (k : ℕ) (s : E × E) (g : E) : E × E :=
  let next := x0 + clip R (s.2 - (((k : ℝ) + 1) / (2 * D)) • g - x0)
  (Gradient.acceleratedQuery (k, s.1, next), next)

noncomputable def projectedRun (g : E → Ω → E) (D R : ℝ) (x0 : E) :
    (K : ℕ) → ℕ → E → E → (Fin K → Ω) → E × E
  | 0, _, x, z, _ => (x, z)
  | K + 1, k, x, z, ξ =>
      let next := projectedUpdate D R x0 k (x, z) (g (Gradient.acceleratedQuery (k, x, z)) (ξ 0))
      projectedRun g D R x0 K (k + 1) next.1 next.2 (fun i => ξ i.succ)

noncomputable def projectedAccelerated (D R : ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E × E
  initial _ := (0, x0, x0)
  query := fun s => (0, (Gradient.acceleratedQuery) s)
  update s g := (s.1 + 1, projectedUpdate D R x0 s.1 s.2 g)
  output s := s.2.1

end OracleTemplate.BiasedStochasticGradient
