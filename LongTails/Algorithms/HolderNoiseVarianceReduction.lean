import LongTails.Algorithms.DyadicVarianceReduction

namespace OracleTemplate.HolderNoise

open DyadicHolder

noncomputable def anchorConfig (L σ Δ ε : ℝ) : DyadicConfig :=
  ⟨ε / (4 * L), ⌈16 * L * Δ / ε ^ 2⌉₊, 0, ⌈32 * σ ^ 2 / ε ^ 2⌉₊ + 1, fun _ => 1⟩

def calls (cfg : DyadicConfig) : ℕ := ∑ k ∈ Finset.range (cfg.K + 1), cfg.batch k

noncomputable def selectConfig (a b : DyadicConfig) : DyadicConfig :=
  if calls a ≤ calls b then a else b

noncomputable def outputAlgorithm {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : DyadicConfig) (x0 : E) : Algorithm (E × E) (E × E) E :=
  dyadicVR (selectConfig a b) x0

end OracleTemplate.HolderNoise
