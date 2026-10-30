import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OracleTemplate.FractalChebyshev

noncomputable def split (ψ : ℝ) : List ℝ := [Real.pi / 2 - ψ / 2, Real.pi / 2 + ψ / 2]

noncomputable def angles : ℕ → List ℝ
  | 0 => [Real.pi / 2]
  | k + 1 => (angles k).flatMap split

noncomputable def stepOf (L μ θ : ℝ) : ℝ := 1 / ((L + μ) / 2 + (L - μ) / 2 * Real.cos θ)

noncomputable def schedule (L μ : ℝ) (k : ℕ) : List ℝ := (angles k).map (stepOf L μ)

noncomputable def tauOf (k : ℕ) : ℝ := 2 * ((k : ℝ) + 2) / 2 ^ k

noncomputable def muOf (L : ℝ) (k : ℕ) : ℝ :=
  L * (Real.cosh (tauOf k) - 1) / (Real.cosh (tauOf k) + 1)

end OracleTemplate.FractalChebyshev
