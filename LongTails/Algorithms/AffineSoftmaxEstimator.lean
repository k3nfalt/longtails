import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.NormNum

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.AffineSoftmaxEstimator

noncomputable def halfSuccess : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

noncomputable def countLaw : MeasureTheory.ProbabilityMeasure ℕ :=
  ⟨ProbabilityTheory.geometricMeasure halfSuccess, inferInstance⟩

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]


noncomputable def gibbsWeight (τ : ℝ) (v : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (v i / τ) / ∑ j, Real.exp (v j / τ)

noncomputable def smoothValue (τ : ℝ) (v : ι → ℝ) : ℝ :=
  τ * Real.log (∑ i, Real.exp (v i / τ))

structure Snapshot (ι E : Type*) where
  anchor : E
  value : ι → ℝ
  field : ι → E

def affine (s : Snapshot ι E) (i : ι) (x : E) : ℝ :=
  s.value i + ⟪s.field i, x - s.anchor⟫

noncomputable def weight (s : Snapshot ι E) (τ : ℝ) (x : E) (i : ι) : ℝ :=
  gibbsWeight τ (fun j => affine s j x) i

noncomputable def base (s : Snapshot ι E) (τ : ℝ) (x : E) : E :=
  ∑ i, weight s τ x i • s.field i

def correction (w : ℝ) (g a b : E) : E :=
  w • (g - a) + (w - 1) • (a - b)

noncomputable def numerator (s : Snapshot ι E) (τ : ℝ) (x : E)
    (i : ι) (reply : ℝ × E) : E :=
  correction (Real.exp ((reply.1 - affine s i x) / τ)) reply.2
    (s.field i) (base s τ x)

def reciprocal : List ℝ → ℝ
  | [] => 1
  | w :: ws => (2 - w) * reciprocal ws

noncomputable def estimate (s : Snapshot ι E) (τ : ℝ) (x : E)
    (i : ι) (reply : ℝ × E) (weights : List ℝ) : E :=
  base s τ x + reciprocal weights • numerator s τ x i reply

end LongTails.Algorithms.AffineSoftmaxEstimator
