import LongTails.Setups.CyclicLogisticFeatureLearning

open OracleTemplate
open LongTails.Setups.CyclicLogisticFeatureLearning
open LongTails.Setups.ManySampleConvolutionalPerceptron (Reply Space)

namespace LongTails.Algorithms.CyclicLogisticFeatureLearning

noncomputable def stepSize (p : Params) : ℝ :=
  p.ρ * p.κ / (65536 * p.n * (1 + Real.log (2 + p.n / (p.μ * p.κ))))

noncomputable def algorithm (p : Params) : Algorithm (Query p) (Reply p.d) (Space p.d) where
  State := Scan p
  initial _ := start p
  query s := (0, s.cursor, s.point)
  update := advance p (stepSize p)
  output := Scan.point

noncomputable def output (p : Params) (O : Oracle (Query p) (Reply p.d)) (K : ℕ)
    (ξ : (k : ℕ) → O.Seed k) : Space p.d :=
  execute O (algorithm p) (fun _ => K) () ξ

lemma compliant (p : Params) (hη : 0 < stepSize p) : family p (algorithm p) :=
  ⟨stepSize p, id, hη, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end LongTails.Algorithms.CyclicLogisticFeatureLearning
