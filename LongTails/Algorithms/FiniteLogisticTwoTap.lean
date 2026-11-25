import LongTails.Setups.FiniteLogisticTwoTap

open OracleTemplate MeasureTheory ProbabilityTheory

namespace LongTails.Algorithms.FiniteLogisticTwoTap

open LongTails.Setups.FiniteLogisticTwoTap

def output {d : ℕ} (s : State d) : Weights d := s.point

noncomputable def algorithm (p : Params) (η : ℝ) :
    Algorithm (Bool × Weights p.d) (Reply p.d) (Weights p.d) where
  Seed := Weights p.d
  law := ⟨stdGaussian _, inferInstance⟩
  State := State p.d
  initial g := ⟨start p.r g, none⟩
  query s := (0, s.first.isSome, s.point)
  update := update η
  output := output

end LongTails.Algorithms.FiniteLogisticTwoTap
