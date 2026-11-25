import LongTails.Setups.NoisyTwoSamplePerceptron

open MeasureTheory OracleTemplate ProbabilityTheory
open LongTails.Setups.FiniteLogisticTwoTap (Weights Reply)
open LongTails.Setups.NoisyTwoSamplePerceptron

namespace LongTails.Algorithms.NoisyTwoSamplePerceptron

def output {d : ℕ} (s : State d) : Weights d := s.point

noncomputable def algorithm (p : Params) (η σ : ℝ) :
    Algorithm (Bool × Weights p.d) (Reply p.d) (Weights p.d) where
  Seed := ℕ → Weights p.d
  law := ⟨Measure.infinitePi (fun _ : ℕ => stdGaussian (Weights p.d)), inferInstance⟩
  State := State p.d
  initial ω := ⟨p.x₀, none, 0, ω⟩
  query s := (0, s.first.isSome, s.point)
  update := update η σ
  output := output

end LongTails.Algorithms.NoisyTwoSamplePerceptron
