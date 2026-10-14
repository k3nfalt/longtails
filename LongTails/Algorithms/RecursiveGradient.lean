import LongTails.Algorithms.Svrg

namespace OracleTemplate.NonconvexFiniteSum

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def differenceBatch (g : Fin n × E → E) (b : ℕ)
    (x y : E) (samples : List (Fin n)) : E :=
  (b : ℝ)⁻¹ • (samples.map (fun i => g (i, x) - g (i, y))).sum

noncomputable def recursiveRun (g : Fin n × E → E) (η : ℝ) (b : ℕ) :
    E → E → List (List (Fin n)) → E × List E
  | x, v, [] => (x - η • v, [x])
  | x, v, samples :: tail =>
    let y := x - η • v
    let w := v + differenceBatch g b y x samples
    let result := recursiveRun g η b y w tail
    (result.1, x :: result.2)

noncomputable def recursiveEpochs (g : Fin n × E → E) (η : ℝ) (b : ℕ) :
    E → List (List (List (Fin n))) → E × List E
  | x, [] => (x, [])
  | x, samples :: tail =>
    let epoch := recursiveRun g η b x (FiniteSum.fullGradient g x) samples
    let rest := recursiveEpochs g η b epoch.1 tail
    (rest.1, epoch.2 ++ rest.2)

end OracleTemplate.NonconvexFiniteSum
