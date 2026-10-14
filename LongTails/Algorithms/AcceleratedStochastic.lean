import LongTails.Algorithms.Accelerated

namespace OracleTemplate.StochasticGradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def acceleratedRun (g : E → Ω → E) (D : ℝ) :
    (K : ℕ) → ℕ → E → E → (Fin K → Ω) → E × E
  | 0, _, x, z, _ => (x, z)
  | K + 1, k, x, z, ξ =>
      let y := Gradient.acceleratedQuery (k, x, z)
      let reply := g y (ξ 0)
      acceleratedRun g D K (k + 1) (y - (1 / D) • reply)
        (z - (((k : ℝ) + 1) / (2 * D)) • reply) (fun i => ξ i.succ)

end OracleTemplate.StochasticGradient
