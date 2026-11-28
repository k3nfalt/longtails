import LongTails.Setups.BrightnessScaledTwoTap

open OracleTemplate

namespace LongTails.Algorithms.BrightnessScaledTwoTap

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space)

noncomputable def tuning (p : Params) : ℝ :=
  (scales p).κ

def output (p : Params) (θ : Space p.d) := θ

noncomputable def algorithm (p : Params) (η : ℝ) :
    Algorithm (Space p.d) (Reply p.d) (Space p.d) where
  State := Space p.d
  initial _ := start p
  query θ := (0,θ)
  update θ r := if r.fitted then θ else θ + η • r.descent
  output := output p

end LongTails.Algorithms.BrightnessScaledTwoTap
