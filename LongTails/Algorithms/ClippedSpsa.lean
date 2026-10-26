import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

open MeasureTheory

namespace OracleTemplate.ClippedSpsa

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Sign (d : ℕ) := Fin d → Bool

noncomputable def signVec {d : ℕ} (s : Sign d) : Point d :=
  WithLp.toLp 2 (fun i => if s i then (1 : ℝ) else -1)

noncomputable def clipScalar (c y : ℝ) : ℝ := max (-c) (min c y)

noncomputable def signLaw (d : ℕ) : Measure (Sign d) := (PMF.uniformOfFintype (Sign d)).toMeasure

instance (d : ℕ) : IsProbabilityMeasure (signLaw d) := by
  unfold signLaw; infer_instance

noncomputable def increment {d : ℕ} (μ c : ℝ) (s : Sign d) (r : ℝ × ℝ) : Point d :=
  clipScalar c ((r.1 - r.2) / (2 * μ)) • signVec s

noncomputable def method {d : ℕ} (μ η c : ℝ) (T : ℕ) (x0 : Point d) :
    Algorithm (Point d × Point d) (ℝ × ℝ) (Point d) where
  Seed := (ℕ → Sign d) × Fin (T + 1)
  law := ⟨(Measure.infinitePi fun _ : ℕ => signLaw d).prod
    (PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := (ℕ → Sign d) × ℕ × ℕ × Point d
  initial seed := (seed.1, seed.2.val, 0, x0)
  query st := (0, (st.2.2.2 + μ • signVec (st.1 st.2.2.1), st.2.2.2 - μ • signVec (st.1 st.2.2.1)))
  update st r :=
    if st.2.2.1 < st.2.1 then
      (st.1, st.2.1, st.2.2.1 + 1, st.2.2.2 - η • increment μ c (st.1 st.2.2.1) r)
    else st
  output st := st.2.2.2

end OracleTemplate.ClippedSpsa
