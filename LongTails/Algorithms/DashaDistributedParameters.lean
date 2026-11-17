import LongTails.Algorithms.DashaDistributed

namespace LongTails.Algorithms.DashaDistributedParameters

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open DashaScaling DashaDistributed

noncomputable def initialEnvelope (p : Params) (c : Choice p) (initializer : Option (Choice p)) : ℝ :=
  match initializer with
  | none => 2 * (p.G + spacing p c * Real.sqrt (p.d : ℝ))
  | some c₀ => (2 * DashaCyclic.multiplier c₀.block + 1) * p.G + 2 * spacing p c * Real.sqrt (p.d : ℝ)

noncomputable def growthFactor (p : Params) (c : Choice p) : ℝ :=
  (2 + 2 * DashaCyclic.multiplier c.block) * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c)

noncomputable def inputBound (p : Params) (c : Choice p) (initializer : Option (Choice p)) : ℝ :=
  DashaCyclic.multiplier c.block * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) *
    initialEnvelope p c initializer / spacing p c

noncomputable def roundCount (p : Params) (c : Choice p) (initializer : Option (Choice p)) : ℕ+ :=
  match initializer with
  | none => iterations p c
  | some c₀ => sparseIterations p c c₀

noncomputable def config (p : Params) (c : Choice p) (initializer : Option (Choice p)) : Config p where
  choice := c
  initializer := initializer
  iterations := roundCount p c initializer
  exponentWidth := Nat.size (Nat.size ⌈inputBound p c initializer⌉₊ + roundCount p c initializer * Nat.size ⌈growthFactor p c⌉₊)
  initialWidth := match initializer with
    | none => Nat.size ⌈p.G / spacing p c + 1⌉₊ + 1
    | some c₀ => Nat.size (Nat.size ⌈DashaCyclic.multiplier c₀.block * p.G / spacing p c⌉₊)
  broadcastWidth := Nat.size ⌈(p.n : ℝ) * initialEnvelope p c initializer * growthFactor p c ^ (roundCount p c initializer : ℕ) / spacing p c⌉₊ + 1

end LongTails.Algorithms.DashaDistributedParameters
