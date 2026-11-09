import LongTails.Setups.GaussianVariationalInference
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProductMeasure

open MeasureTheory

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ}

noncomputable def gradLoc (g : Point d) : Location d := fun i => g i

noncomputable def gradScale (g : Point d) (ξ : Fin d → ℝ) : Scale d :=
  fun i j => if j ≤ i then g i * ξ j else 0

noncomputable def proxLog (η y : ℝ) : ℝ := (y + Real.sqrt (y ^ 2 + 4 * η)) / 2

noncomputable def proxScale (η : ℝ) (Y : Scale d) : Scale d :=
  fun i j => if i = j then proxLog η (Y i i) else Y i j

noncomputable def proxStep (η : ℝ) (z : Location d × Scale d) (g : Point d) (ξ : Fin d → ℝ) :
    Location d × Scale d :=
  (z.1 - η • gradLoc g, proxScale η (z.2 - η • gradScale g ξ))

noncomputable def stepSize (μ a : ℝ) (k : ℕ) : ℝ := 2 / (μ * (k + a))

noncomputable def tau (d : ℕ) (κ : ℝ) : ℝ := 3 * d + 8 * Real.log (48 * κ)

noncomputable def smoothConst (L μ : ℝ) (d : ℕ) : ℝ := L * (2 + tau d (L / μ))

noncomputable def offset (L μ : ℝ) (d : ℕ) : ℝ := 16 * smoothConst L μ d / μ + 2

noncomputable def averageWeight (a : ℝ) (k : ℕ) : ℝ := k + a - 1

structure SgdState (d : ℕ) where
  seeds : ℕ → Fin d → ℝ
  count : ℕ
  current : Location d × Scale d
  total : Location d × Scale d
  mass : ℝ

noncomputable def reparameterizedProxSgd (μ a : ℝ) (m0 : Location d) (C0 : Scale d) :
    Algorithm (Point d) (Point d) (Location d × Scale d) where
  Seed := ℕ → Fin d → ℝ
  law := ⟨Measure.infinitePi fun _ : ℕ => noiseLaw d, inferInstance⟩
  State := SgdState d
  initial ω := ⟨ω, 0, (m0, C0), 0, 0⟩
  query s := (0, sample s.current.1 s.current.2 (s.seeds s.count))
  update s g :=
    let next := proxStep (stepSize μ a s.count) s.current g (s.seeds s.count)
    ⟨s.seeds, s.count + 1, next, s.total + averageWeight a s.count • next,
      s.mass + averageWeight a s.count⟩
  output s := if s.mass = 0 then s.current else s.mass⁻¹ • s.total

end OracleTemplate.GaussianVariational
