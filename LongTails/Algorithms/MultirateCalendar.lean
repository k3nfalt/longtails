import LongTails.Algorithms.MultirateAllocation
import LongTails.Algorithms.MultiscaleAggregate

namespace LongTails.Algorithms.MultirateCalendar

open LongTails.Setups.MultirateSmoothNonconvex
open MultirateAllocation

noncomputable def steps (p : Params) := MultiscaleAggregate.rounds (aggregate p)

noncomputable def packetTime (p : Params) : ℝ :=
  p.l + (p.b : ℝ) * (p.d * MultiscaleAggregate.width (aggregate p) 0 + DistributedTemplate.clockBits : ℕ)

noncomputable def service (p : Params) (i : Fin p.n) : ℝ := p.h i * (batch p i : ℝ)

noncomputable def trip (p : Params) (i : Fin p.n) : ℝ := 2 * packetTime p + service p i

noncomputable def slot (p : Params) : ℝ :=
  2 * packetTime p + ((Finset.univ.sup p.h : NNReal) : ℝ) / steps p +
    (∑ i, p.L i * service p i) / (∑ i, p.L i)

noncomputable def period (p : Params) (i : Fin p.n) : ℕ :=
  1 + ⌊trip p i / slot p⌋₊

noncomputable def epoch (p : Params) (i : Fin p.n) (k : ℕ) : ℕ := k / period p i

noncomputable def origin (p : Params) (i : Fin p.n) (k : ℕ) : ℕ :=
  (epoch p i k - 1) * period p i

end LongTails.Algorithms.MultirateCalendar
