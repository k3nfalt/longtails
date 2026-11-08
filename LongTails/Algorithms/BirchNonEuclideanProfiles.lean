import LongTails.Algorithms.BirchNonEuclideanFamilies

namespace LongTails.Algorithms.BirchNonEuclideanProfiles

open LongTails.Setups.BirchNonEuclidean

noncomputable def deltaProfile (H R : ℕ) : StructuralProfile where
  minimumBatch := max (2 * H) (4 * H * R)
  driftConstant := 3 * (R : ℝ) + 2
  driftLinear := 2 / (H : ℝ)
  noiseLinear := 1
  noiseQuadratic := 0

def deltaCalls (H K B : ℕ) : ℕ := B + K * H

def minibatchProfile : StructuralProfile where
  minimumBatch := 1
  driftConstant := 0
  driftLinear := 0
  noiseLinear := 1
  noiseQuadratic := 0

def minibatchCalls (K B : ℕ) : ℕ := K * B

noncomputable def sharedProfile (m H : ℕ) : StructuralProfile where
  minimumBatch := 2 * H
  driftConstant := 2
  driftLinear := 2 / (H : ℝ)
  noiseLinear := 1 / (m : ℝ)
  noiseQuadratic := H

def sharedCalls (m H K B : ℕ) : ℕ := m * B + K * (m * H)

end LongTails.Algorithms.BirchNonEuclideanProfiles
