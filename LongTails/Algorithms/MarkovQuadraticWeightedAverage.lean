import LongTails.Algorithms.MarkovQuadraticSgd

namespace OracleTemplate.MarkovQuadraticWeightedAverage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def average (α : ℝ) (x0 : E) : ℕ → E → E → E
  | 0, _, _ => x0
  | n + 1, x, s => (1 + α * n)⁻¹ • (α • s + x)

noncomputable def algorithm (L α : ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E × E
  initial _ := (0, x0, 0)
  query z := (0, z.2.1)
  update z g := (z.1 + 1, z.2.1 - L⁻¹ • g, if z.1 = 0 then z.2.2 else z.2.2 + z.2.1)
  output z := average α x0 z.1 z.2.1 z.2.2

noncomputable def output (α : ℝ) (x0 : E) (x : ℕ → E) (K : ℕ) : E :=
  average α x0 K (x K) (∑ j ∈ Finset.range (K - 1), x (j + 1))

end OracleTemplate.MarkovQuadraticWeightedAverage
