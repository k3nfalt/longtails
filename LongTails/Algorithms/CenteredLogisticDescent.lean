import LongTails.Setups.CenteredLogisticClassification
import LongTails.Algorithms.Batched

open OracleTemplate
open scoped BigOperators

namespace LongTails.Algorithms.CenteredLogisticDescent

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.ManySampleConvolutionalPerceptron (Reply Space)

noncomputable def tuning {p : Params} (batch : Batch p) : ℝ × ℝ :=
  let energy := 𝔼 i, ‖(batch i).direction.2‖ ^ 2
  let S := Real.sqrt energy
  if 0 < S then ((Real.sqrt S)⁻¹, 8 / S) else (1, 1)

noncomputable def full (p : Params) : Algorithm (Query p) (Batch p) (Space p.d) where
  State := Space p.d × Option ℝ
  initial _ := (initialPoint p.d, none)
  query s := (0, (⟨0, p.n.pos⟩, s.1))
  update := batchStep tuning
  output := Prod.fst

noncomputable def algorithm (p : Params) : Algorithm (Query p) (Reply p.d) (Space p.d) :=
  batched p.n.pos (full p) (fun s i => (i, s.1)) (fun _ b => b) (emptyReply p.d)

noncomputable def output (p : Params) (O : Oracle (Query p) (Reply p.d))
    (N : ℕ) (seed : (algorithm p).Seed) (ω : (k : ℕ) → O.Seed k) : Space p.d :=
  execute O (algorithm p) (fun _ => N) seed ω

end LongTails.Algorithms.CenteredLogisticDescent
