import LongTails.Setups.DerivativeConvolutionalPerceptron
import LongTails.Algorithms.ClusteredConvolutionalPerceptron

open OracleTemplate

namespace LongTails.Algorithms.DerivativeConvolutionalPerceptron

open LongTails.Setups.DerivativeConvolutionalPerceptron
open ClusteredConvolutionalPerceptron (ScanState scanUpdate)

noncomputable def stepSize (p : Params) : ℝ :=
  p.derivativeMargin ^ 2 * p.lower ^ 2 / (2 ^ 40 * p.upper ^ 3)

noncomputable def algorithm (p : Params) :
    Algorithm (Query p.dimension p.samples) (Reply p.dimension) (Space p.dimension) where
  State := ScanState p.dimension p.samples
  initial _ := ⟨((Real.sqrt 2, 0), 0), 0⟩
  query state := (0, state.cursor, state.point)
  update := scanUpdate (stepSize p)
  output state := state.point

noncomputable def output (p : Params)
    (O : Oracle (Query p.dimension p.samples) (Reply p.dimension)) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) : Space p.dimension :=
  execute O (algorithm p) (fun _ => K) seed ξ

noncomputable def frozenFeature {d : ℕ} (b : Features d) : Features d := Real.sqrt 2 • b

noncomputable def frozenStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (sample point : E) : E :=
  if inner ℝ sample point ≤ 0 then point + η • sample else point

noncomputable def frozenPairedIterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (η : ℝ) (positive negative : Fin (n + 1) → E) : ℕ → E
  | 0 => 0
  | k + 1 =>
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    frozenStep η (-negative j) (frozenStep η (positive j) (frozenPairedIterate η positive negative k))

noncomputable def frozenPairedMiddle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (η : ℝ) (positive negative : Fin (n + 1) → E) (k : ℕ) : E :=
  frozenStep η (positive ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩)
    (frozenPairedIterate η positive negative k)

end LongTails.Algorithms.DerivativeConvolutionalPerceptron
