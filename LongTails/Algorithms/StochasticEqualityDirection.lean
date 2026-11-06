import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

namespace LongTails.Algorithms.StochasticEqualityDirection

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def regular (ν : ℝ) (J : F →L[ℝ] E) : Prop := ∀ v, ν * ‖v‖ ≤ ‖J v‖

def multiplier (J : F →L[ℝ] E) (g : E) : F :=
  -(Ring.inverse (J.adjoint.comp J)) (J.adjoint g)

def tangent (J : F →L[ℝ] E) (g : E) : E := g + J (multiplier J g)

def thresholdedMultiplier (ν : ℝ) (J : F →L[ℝ] E) (g : E) : F :=
  by classical exact if regular (ν / 2) J then multiplier J g else 0

def direction (ν : ℝ) (J : F →L[ℝ] E) (g : E) (c : F) : E :=
  -(g + J (thresholdedMultiplier ν J g)) - J c

end

end LongTails.Algorithms.StochasticEqualityDirection
