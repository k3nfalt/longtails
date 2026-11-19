import LongTails.Setups.SphericalRandomUtility
import LongTails.Algorithms.AcceleratedTwoPointZerothOrderConvex
import LongTails.Algorithms.Clipping
import Mathlib.Probability.ConditionalProbability

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace LongTails.Algorithms.SphericalPreferenceDescent

open OracleTemplate LongTails.Setups.SphericalRandomUtility

noncomputable def project (p : Params) (x : Point p.d) : Feasible p :=
  ⟨clip p.R x, mem_closedBall_zero_iff.mpr (norm_clip_le p.R.coe_nonneg x)⟩

noncomputable def jitterLaw (d : ℕ) (r : ℝ) : ProbabilityMeasure (Point d) := by
  by_cases hr : 0 < r
  · let μ := (volume : Measure (Point d))
    exact ⟨ProbabilityTheory.cond μ (ball 0 r), ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne⟩
  · exact ⟨Measure.dirac 0, inferInstance⟩

noncomputable def directionLaw (d : ℕ) : ProbabilityMeasure (Point d) := by
  by_cases hd : d = 0
  · exact ⟨Measure.dirac 0, inferInstance⟩
  · letI : NeZero d := ⟨hd⟩
    exact (ZerothOrder.sphereLaw (Point d)).map Subtype.val

noncomputable def stepSize (p : Params) (n : ℕ) : ℝ := p.R / Real.sqrt n

noncomputable def radius (p : Params) (n : ℕ) : ℝ := stepSize p n / 4

noncomputable def probe (p : Params) (n : ℕ) : ℝ := radius p n / (4 * p.d * Real.sqrt n)

abbrev Draw (d : ℕ) := Point d × Point d

noncomputable def drawLaw (p : Params) (n : ℕ) : ProbabilityMeasure (Draw p.d) :=
  ⟨((jitterLaw p.d (radius p n) : Measure _).prod (directionLaw p.d : Measure _)), inferInstance⟩

noncomputable def pair (p : Params) (n : ℕ) (x : Point p.d) (v : Draw p.d) :
    Feasible p × Feasible p :=
  let y := (1 - 2 * radius p n / p.R) • x + v.1
  (project p (y + probe p n • v.2), project p (y - probe p n • v.2))

noncomputable def next (p : Params) (n : ℕ) (x u : Point p.d) (reply : Bool) : Point p.d :=
  project p (x - (if reply then stepSize p n else -(stepSize p n)) • u)

noncomputable def output (p : Params) (k : ℕ) (total : Point p.d) : Feasible p :=
  project p ((k : ℝ)⁻¹ • total)

noncomputable def method (p : Params) (n : ℕ) :
    Algorithm (Feasible p × Feasible p) Bool (Feasible p) where
  Seed := ℕ → Draw p.d
  law := ⟨Measure.infinitePi (fun _ : ℕ => (drawLaw p n : Measure _)), inferInstance⟩
  State := (ℕ → Draw p.d) × ℕ × Point p.d × Point p.d
  initial seed := (seed, 0, 0, 0)
  query := fun ⟨v, k, x, _⟩ => (0, pair p n x (v k))
  update := fun ⟨v, k, x, total⟩ reply => (v, k + 1, next p n x (v k).2 reply, total + x)
  output := fun ⟨_, k, _, total⟩ => output p k total

end LongTails.Algorithms.SphericalPreferenceDescent
