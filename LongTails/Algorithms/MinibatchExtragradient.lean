import LongTails.Algorithms.QueryPlan
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.MinibatchExtragradient

open OracleTemplate MeasureTheory

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def batchSum (x : E) : (b : ℕ) → QueryPlan E E E b
  | 0 => .done 0
  | b + 1 => .ask x (fun r => (batchSum x b).map (r + ·))

noncomputable def extrapolate (γ : ℝ) (b : ℕ) (x : E) : QueryPlan E E E b :=
  (batchSum x b).map fun s => x - γ • ((1 / (b : ℝ)) • s)

noncomputable def egStep (γ : ℝ) (b : ℕ) (x : E) : QueryPlan E E E (b + b) :=
  (extrapolate γ b x).bind fun xb => (batchSum xb b).map fun s => x - γ • ((1 / (b : ℝ)) • s)

def stopLen (b : ℕ) : ℕ → ℕ
  | 0 => b
  | n + 1 => stopLen b n + (b + b)

noncomputable def stoppedPlan (γ : ℝ) (b : ℕ) : (n : ℕ) → E → QueryPlan E E E (stopLen b n)
  | 0, x => extrapolate γ b x
  | n + 1, x => (egStep γ b x).bind fun y => stoppedPlan γ b n y

noncomputable def algorithm (γ : ℝ) (b K : ℕ) (x0 : E) : Algorithm E E E where
  Seed := Fin (K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (K + 1))).toMeasure, inferInstance⟩
  State := Σ k, QueryPlan E E E k
  initial ι := ⟨stopLen b ι.val, stoppedPlan γ b ι.val x0⟩
  query s := (0, QueryPlan.query x0 s)
  update := QueryPlan.update
  output := QueryPlan.output x0

end LongTails.Algorithms.MinibatchExtragradient
