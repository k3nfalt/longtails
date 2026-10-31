import LongTails.Setups.ClusteredConvolutionalPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Algorithms.ClusteredConvolutionalPerceptron

open LongTails.Setups.ClusteredConvolutionalPerceptron

structure ScanState (d n : ℕ) where
  point : Space d
  cursor : Fin (n + 1)

def advance {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩

noncomputable def scanUpdate {d n : ℕ} (η : ℝ) (state : ScanState d n)
    (reply : Reply d) : ScanState d n :=
  ⟨if reply.margin ≤ 0 then state.point + η • reply.direction else state.point,
    advance state.cursor⟩

noncomputable def algorithm (p : Params) :
    Algorithm (Query p.dimension p.samples) (Reply p.dimension) (Space p.dimension) where
  State := ScanState p.dimension p.samples
  initial _ := ⟨(((p.derivativeMargin / 8 + 1) / Real.sqrt 2,
    (p.derivativeMargin / 8 - 1) / Real.sqrt 2), 0), 0⟩
  query state := (0, state.cursor, state.point)
  update := scanUpdate (1 / (4 * p.upper))
  output state := state.point

noncomputable def output (p : Params)
    (O : Oracle (Query p.dimension p.samples) (Reply p.dimension)) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) : Space p.dimension :=
  execute O (algorithm p) (fun _ => K) seed ξ

noncomputable def frozenFeature {d : ℕ} (κ : ℝ) (b : Features d) : Features d :=
  ((κ / 8 + 1) / Real.sqrt 2) • b +
    ((κ / 8 - 1) / Real.sqrt 2) • LongTails.Setups.TwoSampleQuadraticPerceptron.shift b

noncomputable def linearStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (sample point : E) : E := if ⟪sample, point⟫ ≤ 0 then point + sample else point

noncomputable def pairedLinearIterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (positive negative : Fin (n + 1) → E) : ℕ → E
  | 0 => 0
  | k + 1 =>
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    linearStep (-negative j) (linearStep (positive j) (pairedLinearIterate positive negative k))

noncomputable def pairedLinearMiddle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (positive negative : Fin (n + 1) → E) (k : ℕ) : E :=
  linearStep (positive ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩)
    (pairedLinearIterate positive negative k)

end LongTails.Algorithms.ClusteredConvolutionalPerceptron
