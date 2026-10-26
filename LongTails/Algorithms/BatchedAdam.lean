import LongTails.Setups.SpectralSmoothAdamComparison

namespace LongTails.Algorithms.BatchedAdam

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar
open LongTails.Setups.SpectralSmoothAdamComparison

noncomputable def method {r : ℕ} (a : AdamTuning) (B T : ℕ) (x0 : Space r r) :
    Algorithm (Space r r) (Space r r) (Space r r) where
  Seed := Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := Fin (T + 1) × ℕ × (ℕ → Space r r)
  initial k := (k, 0, fun _ => 0)
  query state := (0, adamIterate a B x0 state.2.2 (state.2.1 / B))
  update state g := (state.1, state.2.1 + 1, Function.update state.2.2 state.2.1 g)
  output state := adamIterate a B x0 state.2.2 state.1

end LongTails.Algorithms.BatchedAdam
