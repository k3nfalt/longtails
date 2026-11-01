import LongTails.Setups.TwoSidedConvolutionalPerceptron

open OracleTemplate

namespace LongTails.Algorithms.TwoSidedConvolutionalPerceptron

open LongTails.Setups.TwoSidedConvolutionalPerceptron

structure ScanState (d n : ℕ) where
  point : Space d
  cursor : Fin (n + 1)

noncomputable def scanUpdate {d n : ℕ} (η : ℝ) (state : ScanState d n)
    (reply : Reply d) : ScanState d n :=
  ⟨if reply.margin ≤ 0 then state.point + η • reply.direction else state.point,
    finRotate (n + 1) state.cursor⟩

noncomputable def stepSize (p : Params) : ℝ := p.margin / (96 * p.upper)

noncomputable def algorithm (p : Params) :
    Algorithm (Query p.dimension p.samples) (Reply p.dimension) (Space p.dimension) where
  State := ScanState p.dimension p.samples
  initial _ := ⟨identityStart p.dimension, 0⟩
  query state := (0, state.cursor, state.point)
  update := scanUpdate (stepSize p)
  output state := state.point

noncomputable def output (p : Params)
    (O : Oracle (Query p.dimension p.samples) (Reply p.dimension)) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) : Space p.dimension :=
  execute O (algorithm p) (fun _ => K) seed ξ

end LongTails.Algorithms.TwoSidedConvolutionalPerceptron
