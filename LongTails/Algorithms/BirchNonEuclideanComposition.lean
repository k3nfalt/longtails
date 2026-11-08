import LongTails.Setups.BirchNonEuclideanComposition
import LongTails.Algorithms.BirchCausalTuning
import LongTails.Algorithms.BirchNonEuclideanFramework

namespace LongTails.Algorithms.BirchNonEuclideanComposition

open LongTails.Setups.BirchNonEuclideanComposition

noncomputable def program (p : Params) :=
  LongTails.Algorithms.BirchCausalTuning.program (native p) p.credits p.word
    (fun K B job => p.recipe K B job.worker job.source job.serial)

noncomputable def algorithm (p : Params) :=
  LongTails.Setups.BirchNonEuclidean.programAlgorithm (native p) (program p)
    (LongTails.Algorithms.BirchNonEuclideanFramework.chosenLMO (native p))

noncomputable def output {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : OracleTemplate.Rennala.Point p.d → Ω → OracleTemplate.Rennala.Point p.d)
    (Q : ℕ) (z : (algorithm p).Seed × (ℕ → Ω)) : OracleTemplate.Rennala.Point p.d :=
  OracleTemplate.execute (OracleTemplate.BirchSgd.gradientOracle P g)
    (algorithm p) (fun _ => Q) z.1 z.2

end LongTails.Algorithms.BirchNonEuclideanComposition
