import LongTails.Setups.StructuredGaussianVariationalInference
import LongTails.Algorithms.ReparameterizedProxSgd

open MeasureTheory

namespace OracleTemplate.StructuredGaussianVariational

open LongTails.Setups.GaussianVariationalInference
open OracleTemplate.GaussianVariational

variable {d : ℕ}

noncomputable def maskScale (S : Fin d → Finset (Fin d)) (U : Scale d) : Scale d :=
  fun i j => if j ∈ S i then U i j else 0

noncomputable def maskedStep (S : Fin d → Finset (Fin d)) (η : ℝ) (z : Location d × Scale d)
    (g : Point d) (ξ : Fin d → ℝ) : Location d × Scale d :=
  (z.1 - η • gradLoc g, proxScale η (z.2 - η • maskScale S (gradScale g ξ)))

noncomputable def patternTau (d w : ℕ) (κ : ℝ) : ℝ := 3 * w + 8 * Real.log (48 * d * κ)

noncomputable def patternSmooth (L μ : ℝ) (d w : ℕ) : ℝ := L * (2 + patternTau d w (L / μ))

noncomputable def patternOffset (L μ : ℝ) (d w : ℕ) : ℝ := 16 * patternSmooth L μ d w / μ + 2

structure MaskedState (d : ℕ) where
  seeds : ℕ → Fin d → ℝ
  count : ℕ
  current : Location d × Scale d
  total : Location d × Scale d
  mass : ℝ

noncomputable def structuredProxSgd (S : Fin d → Finset (Fin d)) (μ a : ℝ) (m0 : Location d)
    (C0 : Scale d) : Algorithm (Point d) (Point d) (Location d × Scale d) where
  Seed := ℕ → Fin d → ℝ
  law := ⟨Measure.infinitePi fun _ : ℕ => noiseLaw d, inferInstance⟩
  State := MaskedState d
  initial ω := ⟨ω, 0, (m0, C0), 0, 0⟩
  query s := (0, sample s.current.1 s.current.2 (s.seeds s.count))
  update s g :=
    let next := maskedStep S (stepSize μ a s.count) s.current g (s.seeds s.count)
    ⟨s.seeds, s.count + 1, next, s.total + averageWeight a s.count • next,
      s.mass + averageWeight a s.count⟩
  output s := if s.mass = 0 then s.current else s.mass⁻¹ • s.total

end OracleTemplate.StructuredGaussianVariational
