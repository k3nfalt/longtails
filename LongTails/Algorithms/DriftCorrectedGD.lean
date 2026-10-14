import LongTails.Setups.AffineDriftPL
import LongTails.Algorithms.AcceleratedZerothOrderConvex
import LongTails.Algorithms.Gd

namespace OracleTemplate.AffineDriftPL

open LongTails.Setups.AffineDriftPL

open ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def driftQuery {d : ℕ} (h : ℝ) (x : Point d) (j : Fin (d + 2)) : Point d :=
  if hj : j.val = 0 ∨ j.val = d + 1 then x
  else x + h • direction ⟨j.val - 1, by omega⟩

noncomputable def driftDecode {d : ℕ} (h : ℝ) (r : Fin (d + 2) → ℝ) : Point d :=
  ∑ i : Fin d, ((r ⟨i.val + 1, by omega⟩ -
    ((1 - ((i.val : ℝ) + 1) / ((d : ℝ) + 1)) * r 0 +
      (((i.val : ℝ) + 1) / ((d : ℝ) + 1)) * r ⟨d + 1, by omega⟩)) / h) • direction i

noncomputable def driftCorrectedGD (p : Public) : Algorithm (Point p.d) ℝ (Point p.d) :=
  let h := Real.sqrt (p.μ * p.ε / (p.d : ℝ)) / p.L
  batched (by omega : 0 < p.d + 2) (Gradient.gd (p.L, p.x0))
    (driftQuery h) (fun _ => driftDecode h) 0

end OracleTemplate.AffineDriftPL
