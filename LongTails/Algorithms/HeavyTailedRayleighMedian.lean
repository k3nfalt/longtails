import LongTails.Setups.HeavyTailedHessianVector
import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.HeavyTailedRayleighMedian

open LongTails.Setups.HeavyTailedHessianVector

noncomputable def groupMean (n : ℕ) (values : List ℝ) (j : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, values.getD (j * n + k) 0

noncomputable def output (n m : ℕ) (values : List ℝ) : ℝ :=
  let means := List.ofFn (fun j : Fin m => groupMean n values j.val)
  (means.mergeSort (· ≤ ·)).getD (m / 2) 0

noncomputable def algorithm (p : Params) (x v : Space p) (n m : ℕ) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) ℝ where
  State := List ℝ
  initial _ := []
  query _ := (0, x, some v)
  update values reply := ⟪v, reply⟫ :: values
  output values := output n m values.reverse

end LongTails.Algorithms.HeavyTailedRayleighMedian
