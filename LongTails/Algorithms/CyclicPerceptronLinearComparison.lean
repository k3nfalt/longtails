import LongTails.Setups.CyclicFullWidthPerceptron

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.CyclicPerceptronLinearComparison

open LongTails.Setups.CyclicFullWidthPerceptron

noncomputable def linearMargin {d : ℕ} (q z : Input d) : ℝ := q.1 * z.1 + ⟪q.2, z.2⟫

noncomputable def linearIterate (p : Params) (D : Data p.dimension p.count)
    (η : ℝ) (index : ℕ → Fin (p.count + 1)) : ℕ → Input p.dimension
  | 0 => 0
  | k + 1 =>
      let z := linearIterate p D η index k
      let q := sample p D (index k)
      if linearMargin q z ≤ 0 then z + η • q else z

end LongTails.Algorithms.CyclicPerceptronLinearComparison
