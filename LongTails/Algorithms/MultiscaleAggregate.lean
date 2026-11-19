import LongTails.Setups.DistributedAggregateSmoothNonconvex
import LongTails.Algorithms.DashaModular
import LongTails.Algorithms.DyadicVarianceReduction

namespace LongTails.Algorithms.MultiscaleAggregate

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open OracleTemplate.DyadicHolder
open DistributedTemplate

noncomputable def precision (p : Params) : ℝ := p.ε / 512

noncomputable def depth (p : Params) : ℕ :=
  Nat.size ⌈2 * p.L * p.Δ / precision p ^ 2⌉₊

noncomputable def rounds (p : Params) : ℕ := 2 ^ depth p

noncomputable def schedule (p : Params) : DyadicConfig :=
  ⟨precision p / p.L, rounds p, depth p, 0, fun _ => 0⟩

noncomputable def exponent (p : Params) (k : ℕ) : ℕ :=
  if k = 0 then depth p else (schedule p).level k

noncomputable def radius (p : Params) (k : ℕ) : ℝ := 2 ^ exponent p k * precision p

noncomputable def width (p : Params) (k : ℕ) : ℕ :=
  4 + Nat.size ((p.n : ℕ) * (p.d + 1)) + exponent p k

noncomputable def targetTime (p : Params) : ℝ :=
  (∑ i, (p.h i : ℝ) * p.σ i ^ 2) / ((p.n : ℝ) ^ 2 * precision p ^ 2)

noncomputable def batch (p : Params) (i : Fin p.n) : ℕ :=
  max 1 ⌈targetTime p / (p.h i : ℝ)⌉₊

noncomputable def spacing (p : Params) : ℝ := precision p / (p.d + 1 : ℕ)

noncomputable def aggregateSpacing (p : Params) : ℝ := spacing p / p.n

abbrev Code (p : Params) := Fin p.d → ℤ

noncomputable def localCode (p : Params) (x : Point p) : Code p :=
  DashaQuantization.indices p.d false (spacing p) x (fun _ => 0)

noncomputable def unpack (p : Params) (z : Code p) : Point p :=
  DashaQuantization.reconstruct (aggregateSpacing p) z

def congruent (w : ℕ) {d : ℕ} (a b : Fin d → ℤ) : Prop :=
  ∀ j, a j % DashaModular.modulus w = b j % DashaModular.modulus w

noncomputable def recover (p : Params) (k : ℕ) (anchor : Point p) (received : Code p) :
    Point p := by
  classical
  let C := fun z : Code p =>
    congruent (width p k) z received ∧ ‖unpack p z - anchor‖ ≤ 3 * radius p k
  exact if h : ∃ z, C z then unpack p (Classical.choose h) else anchor

noncomputable def packet (p : Params) (k : ℕ) (z : Code p) : List Bool :=
  DashaModular.encode p.d (width p k) z

noncomputable def readPacket (p : Params) (k : ℕ) (bits : List Bool) : Code p :=
  DashaModular.decode p.d (width p k) bits

end LongTails.Algorithms.MultiscaleAggregate
