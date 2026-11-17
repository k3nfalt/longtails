import LongTails.Algorithms.DashaDistributedParameters

namespace LongTails.Algorithms.DashaDistributedTrackedParameters

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open DashaScaling DashaDistributed DashaDistributedParameters

noncomputable def globalInitialBound (p : Params) : ℝ :=
  min p.G (Real.sqrt (2 * min p.L p.Lhat * p.Δ))

noncomputable def trackingInitialEnvelope (p : Params) (c : Choice p) (initializer : Option (Choice p)) : ℝ :=
  globalInitialBound p + (match initializer with
    | none => 0
    | some c₀ => (2 * DashaCyclic.multiplier c₀.block + 1) * p.G) +
    3 * spacing p c * Real.sqrt (p.d : ℝ)

noncomputable def trackingInputBound (p : Params) (c : Choice p) (initializer : Option (Choice p)) : ℝ :=
  DashaCyclic.multiplier c.block * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) *
    trackingInitialEnvelope p c initializer / spacing p c

noncomputable def modularInitialBound (p : Params) (c : Choice p) : ℝ :=
  (p.n : ℝ) * (globalInitialBound p + spacing p c * Real.sqrt (p.d : ℝ)) / spacing p c

noncomputable def trackedConfig (p : Params) (c : Choice p) (initializer : Option (Choice p))
    (modularInitialization : Bool) : Config p :=
  { config p c initializer with
    modularInitialization := modularInitialization
    exponentWidth := Nat.size (Nat.size ⌈trackingInputBound p c initializer⌉₊ +
      roundCount p c initializer * Nat.size ⌈growthFactor p c⌉₊)
    initialWidth := if modularInitialization && initializer.isNone then
      Nat.size ⌈modularInitialBound p c⌉₊ + 1 else (config p c initializer).initialWidth
    broadcastWidth := Nat.size ⌈(p.n : ℝ) * trackingInitialEnvelope p c initializer *
      growthFactor p c ^ (roundCount p c initializer : ℕ) / spacing p c⌉₊ + 1 }

end LongTails.Algorithms.DashaDistributedTrackedParameters
