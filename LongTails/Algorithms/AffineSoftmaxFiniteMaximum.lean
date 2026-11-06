import LongTails.Algorithms.AffineSoftmaxCompiler
import LongTails.Algorithms.AffineSoftmaxRadius
import LongTails.Setups.SmoothFiniteMaximum

namespace LongTails.Algorithms.AffineSoftmaxFiniteMaximum

open MeasureTheory
open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Setups.SmoothFiniteMaximum
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxRadius
open LongTails.Algorithms.AffineSoftmaxAmplification

abbrev Seeds := ℕ → ℕ → OuterSeed

instance : MeasurableSpace Seeds := MeasurableSpace.pi

noncomputable def law : ProbabilityMeasure Seeds :=
  ⟨Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed))), inferInstance⟩

instance publicMNeZero (p : Public) : NeZero p.m := ⟨by have := p.hm; omega⟩

noncomputable def plan (p : Public) (seed : Seeds) : Program (Fin p.m × p.E) (ℝ × p.E) p.E :=
  if 2 * p.G * p.R ≤ p.ε then .done p.x0 else
    let r := publicRadius p.m p.G p.L p.R p.ε
    let τ := p.ε / (2 * Real.log p.m)
    let H := compilerDepth p.G (2 * p.R) r (p.ε / 2)
    amplifiedOuterPlan p.m (domain p) p.x0 τ p.L p.G r (2 * p.R) (p.ε / 2)
      (compilerFloor p.G (2 * p.R) r (p.ε / 2)) (compilerCap p.G (2 * p.R) r (p.ε / 2))
      H (compilerBoost p.G (2 * p.R) r (p.ε / 2)) (compilerHorizon p.G (2 * p.R) r (p.ε / 2))
      (5 * H) (Nat.ceil (6 * meanCostBound p.m p.G p.L p.R p.ε)) seed

noncomputable def algorithm (p : Public) : Algorithm (Fin p.m × p.E) (ℝ × p.E) p.E :=
  AffineSoftmaxCompiler.programAlgorithm law p.m p.x0 (plan p)

noncomputable def output (p : Public) (oracle : Oracle (Fin p.m × p.E) (ℝ × p.E)) (K : ℕ)
    (seed : Seeds) (oracleSeed : (k : ℕ) → oracle.Seed k) : p.E :=
  execute oracle (algorithm p) (fun _ => K) seed oracleSeed

end LongTails.Algorithms.AffineSoftmaxFiniteMaximum
