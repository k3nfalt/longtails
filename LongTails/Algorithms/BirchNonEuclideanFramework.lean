import LongTails.Setups.BirchCollectionExecutionModel

namespace LongTails.Algorithms.BirchNonEuclideanFramework

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonEuclidean

noncomputable def batchSize (p : Params) : ℕ :=
  p.profile.minimumBatch + ⌈64 * p.κ * p.σ ^ 2 * p.profile.noiseLinear / p.ε +
    8 * Real.sqrt (p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε)⌉₊

noncomputable def stepSize (p : Params) : ℝ :=
  1 / (4 * p.L * (1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p))

noncomputable def horizon (p : Params) : ℕ :=
  1 + ⌈48 * p.L * p.Δ *
    (1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p) / p.ε⌉₊

noncomputable def program (p : Params) : Program :=
  p.protocol.instantiate (horizon p) (batchSize p) (canonicalTuning (stepSize p) (batchSize p))

noncomputable def algorithm (p : Params) := programAlgorithm p (program p) (chosenLMO p)

end LongTails.Algorithms.BirchNonEuclideanFramework
