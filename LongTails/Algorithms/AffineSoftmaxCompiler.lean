import LongTails.Algorithms.AffineSoftmaxAmplification

namespace LongTails.Algorithms.AffineSoftmaxCompiler

open MeasureTheory
open OracleTemplate
open OracleTemplate.ComponentEnvelope

noncomputable def programAlgorithm {E Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (m : ℕ) [NeZero m] (initial : E)
    (plan : Ω → Program (Fin m × E) (ℝ × E) E) : Algorithm (Fin m × E) (ℝ × E) E where
  Seed := Ω
  seedSpace := inferInstance
  law := P
  State := Program (Fin m × E) (ℝ × E) E
  initial := plan
  query state := (0, state.query (0, initial))
  update := Program.update
  output := Program.output initial

noncomputable def output {E Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (m : ℕ) [NeZero m] (initial : E)
    (plan : Ω → Program (Fin m × E) (ℝ × E) E) (oracle : Oracle (Fin m × E) (ℝ × E)) (K : ℕ)
    (seed : Ω) (oracleSeed : (k : ℕ) → oracle.Seed k) : E :=
  execute oracle (programAlgorithm P m initial plan) (fun _ => K) seed oracleSeed

end LongTails.Algorithms.AffineSoftmaxCompiler
