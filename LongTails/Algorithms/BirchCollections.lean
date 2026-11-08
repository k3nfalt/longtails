import LongTails.Algorithms.BirchNonEuclideanFramework

namespace LongTails.Algorithms.BirchCollections

open LongTails.Setups.BirchCollections
open OracleTemplate.Rennala (Point)

noncomputable def output {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) (Q : ℕ)
    (z : (algorithm p).Seed × (ℕ → Ω)) : Point p.d :=
  OracleTemplate.execute (OracleTemplate.BirchSgd.gradientOracle P g)
    (algorithm p) (fun _ => Q) z.1 z.2

end LongTails.Algorithms.BirchCollections
