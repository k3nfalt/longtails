import LongTails.Algorithms.MultirateCalendar
import LongTails.Algorithms.NormalizedStorm

namespace LongTails.Algorithms.MultirateTrajectory

open LongTails.Setups.MultirateSmoothNonconvex
open MultirateCalendar MultirateAllocation

noncomputable def stepSize (p : Params) : ℝ :=
  MultiscaleAggregate.precision (aggregate p) / (aggregate p).L

abbrev Code (p : Params) := MultiscaleAggregate.Code (aggregate p)

noncomputable def pack (p : Params) (z : Code p) :=
  MultiscaleAggregate.packet (aggregate p) 0 z

noncomputable def read (p : Params) (bits : List Bool) : Code p :=
  MultiscaleAggregate.readPacket (aggregate p) 0 bits

noncomputable def liftCode (p : Params) (z : Code p) : Point p :=
  MultiscaleAggregate.recover (aggregate p) 0 0 z

noncomputable def queryPacket (p : Params) (x : Point p) : List Bool :=
  pack p (∑ _i : Fin p.n, MultiscaleAggregate.localCode (aggregate p) ((aggregate p).L • (x - p.x0)))

noncomputable def queryPoint (p : Params) (bits : List Bool) : Point p :=
  p.x0 + (aggregate p).L⁻¹ • liftCode p (read p bits)

noncomputable def replyPacket (p : Params) (v : Point p) : List Bool :=
  pack p (MultiscaleAggregate.localCode (aggregate p) v)

noncomputable def batchMean (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (i : Fin p.n) (a : ℕ) (x : Point p) : Point p :=
  (batch p i : ℝ)⁻¹ • ∑ j ∈ Finset.range (batch p i), g i x (s i (a * batch p i + j))

structure Model (p : Params) where
  points : ℕ → Point p
  estimates : ℕ → Point p

def initial (p : Params) : Model p := ⟨fun _ => p.x0, fun _ => 0⟩

noncomputable def advance (p : Params) (m : Model p) (k : ℕ) (sum : Code p) : Model p :=
  let v := liftCode p sum
  ⟨Function.update m.points (k + 1) (OracleTemplate.NormalizedStorm.stormStep (stepSize p) (m.points k) v),
    Function.update m.estimates k v⟩

noncomputable def input (p : Params) (k : ℕ) (i : Fin p.n) (m : Model p) : Point p :=
  queryPoint p (queryPacket p (m.points (origin p i k)))

noncomputable def message (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (k : ℕ) (i : Fin p.n) (m : Model p) :=
  replyPacket p (batchMean p g s i (epoch p i k) (input p k i m))

noncomputable def trajectory (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) :
    ℕ → Model p
  | 0 => initial p
  | k + 1 =>
    let m := trajectory p g s k
    advance p m k (∑ i, read p (message p g s k i m))

noncomputable def output (p : Params) (m : Model p) (a b : ℕ) : Point p :=
  if ‖m.estimates a‖ ≤ ‖m.estimates b‖ then m.points a else m.points b

end LongTails.Algorithms.MultirateTrajectory
