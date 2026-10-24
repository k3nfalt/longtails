import LongTails.Setups.ManySampleConvolutionalPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Algorithms.ManySampleConvolutionalPerceptron

open LongTails.Setups.ManySampleConvolutionalPerceptron

structure ScanState (d n : ℕ) where
  point : Space d
  cursor : Fin (n + 1)

noncomputable def unstableCoordinate {d : ℕ} (θ : Space d) : ℝ :=
  (θ.1.1 + θ.1.2) / Real.sqrt 2 + ⟪θ.2, axis d⟫

noncomputable def referenceKick {d : ℕ} (σ : ℝ) (θ : Space d) : Space d :=
  let k := (if 0 ≤ unstableCoordinate θ then σ else -σ) / Real.sqrt 2
  ((k, k), 0)

noncomputable def scanUpdate {d n : ℕ} (η σ : ℝ) (state : ScanState d n)
    (reply : Reply d) : ScanState d n :=
  if reply.margin ≤ 0 then
    ⟨state.point + η • reply.direction +
      (if state.cursor = 0 then referenceKick σ state.point else 0), 0⟩
  else if h : state.cursor.val = n then
    ⟨state.point, 0⟩
  else
    ⟨state.point, ⟨state.cursor.val + 1, by have := state.cursor.isLt; omega⟩⟩

noncomputable def algorithm (p : Params) :
    Algorithm (Query p.dimension p.samples) (Reply p.dimension) (Space p.dimension) where
  State := ScanState p.dimension p.samples
  initial _ := ⟨((Real.sqrt 2, 0), 0), 0⟩
  query state := (0, state.cursor, state.point)
  update := scanUpdate (1 / (4 * p.upper)) ((p.contrast / (4 * p.upper)) ^ 4)
  output state := state.point

noncomputable def output (p : Params)
    (O : Oracle (Query p.dimension p.samples) (Reply p.dimension)) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) : Space p.dimension :=
  execute O (algorithm p) (fun _ => K) seed ξ

end LongTails.Algorithms.ManySampleConvolutionalPerceptron
