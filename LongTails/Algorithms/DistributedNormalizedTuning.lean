import LongTails.Algorithms.DistributedNormalizedDownlink
import Mathlib.Data.Nat.Size

namespace LongTails.Algorithms.DistributedNormalizedTuning

open LongTails.Setups.DistributedHessianLipschitzNonconvex

noncomputable def iterations (p : Params) : ℕ+ :=
  ⟨max 1 ⌈1024 * p.L * p.Δ / p.ε ^ 2⌉₊, by omega⟩

noncomputable def stepSize (p : Params) : ℝ := p.ε / (128 * p.L)

noncomputable def accuracyScale (p : Params) : ℝ := 1 + p.L * p.Δ / p.ε ^ 2

noncomputable def downlinkWidth (p : Params) : ℕ :=
  Nat.size ⌈1048576 * (1 + accuracyScale p * Real.sqrt p.d)⌉₊ + 2

noncomputable def uplinkWidth (p : Params) : ℕ :=
  Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * accuracyScale p +
    p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 2

noncomputable def computationTime (p : Params) : DistributedTemplate.Time := Finset.univ.sup p.h

noncomputable def uplinkCost (p : Params) : ℝ := (p.b : ℝ) * (uplinkWidth p + 64 : ℕ)

noncomputable def downlinkCost (p : Params) : ℝ := (p.b : ℝ) * (downlinkWidth p + 64 : ℕ)

noncomputable def phaseScale (p : Params) : ℝ :=
  256 * max (computationTime p : ℝ)
    (max (uplinkCost p) (max (downlinkCost p)
      (max (p.d * uplinkCost p / p.n)
        (max (p.d * downlinkCost p / Real.sqrt p.n)
          (max (((p.d : ℝ) ^ 3 * uplinkCost p * downlinkCost p ^ 2 / p.n) ^ (1 / 3 : ℝ))
            (max (p.σ ^ 2 * (computationTime p : ℝ) / (p.n * p.ε ^ 2))
              (max (Real.sqrt (p.d * p.σ ^ 2 * (computationTime p : ℝ) * uplinkCost p / (p.n * p.ε ^ 2)))
                (p.d * downlinkCost p * min 1 (Real.sqrt (p.Q * p.ε) / p.L)))))))))

noncomputable def fullUplink (p : Params) : Bool :=
  decide (uplinkCost p = 0 ∨ p.d * uplinkCost p ≤ phaseScale p)

noncomputable def fullDownlink (p : Params) : Bool :=
  decide (downlinkCost p = 0 ∨ p.d * downlinkCost p ≤ phaseScale p)

noncomputable def uplinkCount (p : Params) : ℕ+ :=
  if fullUplink p then 1 else ⟨max 1 ⌊phaseScale p / uplinkCost p⌋₊, by omega⟩

noncomputable def downlinkCount (p : Params) : ℕ+ :=
  if fullDownlink p then 1 else ⟨max 1 ⌊phaseScale p / downlinkCost p⌋₊, by omega⟩

noncomputable def refreshPeriod (p : Params) : ℕ+ :=
  if fullDownlink p then 1 else ⟨max 1 ⌊p.d * downlinkCost p / phaseScale p⌋₊, by omega⟩

noncomputable def compressionVariance (p : Params) : ℝ :=
  if fullUplink p then 0 else ((p.d : ℝ) - 1) / uplinkCount p

noncomputable def batch (p : Params) : ℕ+ :=
  ⟨max 1 ⌈16384 * p.σ ^ 2 * (1 + compressionVariance p) / (p.n * p.ε ^ 2)⌉₊, by omega⟩

noncomputable def gradientRadius (p : Params) : ℝ :=
  Real.sqrt (2 * p.L * p.Δ) + 4 * p.L * p.d * ((iterations p : ℕ) + 1 : ℕ) * stepSize p

noncomputable def clipMargin (p : Params) : ℝ := p.ε + 32 * (p.σ ^ 2 / batch p) / p.ε

noncomputable def config (p : Params) : DistributedNormalizedDownlink.Config where
  iterations := iterations p
  batch := batch p
  uplinkWidth := uplinkWidth p
  downlinkWidth := downlinkWidth p
  uplinkCount := uplinkCount p
  downlinkCount := downlinkCount p
  refreshPeriod := refreshPeriod p
  fullUplink := fullUplink p
  stepSize := stepSize p
  clipRadius := gradientRadius p + clipMargin p
  uplinkSpacing := if fullUplink p then p.ε * Real.sqrt ((p.n : ℝ) / p.d) / 64
    else p.ε * Real.sqrt ((uplinkCount p : ℝ) * p.n) / 64
  incrementSpacing := stepSize p * Real.sqrt p.d
  refreshSpacing := stepSize p / (4 * Real.sqrt p.d)

end LongTails.Algorithms.DistributedNormalizedTuning
