import Init
import LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
import Mathlib.Data.Nat.Log

namespace LongTails.Algorithms.LeonCalendar

def levels : Nat → List Nat
  | 0 => [0]
  | j + 1 =>
    let sub := levels j
    (j + 1) :: (sub ++ sub ++ sub ++ sub)

end LongTails.Algorithms.LeonCalendar

namespace LongTails.Algorithms.LeonTuning

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex

noncomputable def resolution (p : Params) : ℝ := p.ε / 512

noncomputable def height (p : Params) : ℕ :=
  Nat.clog 4 (max 1 ⌈2 * p.L * p.Δ / resolution p ^ 2⌉₊)

noncomputable def iterations (p : Params) : ℕ := 4 ^ height p

noncomputable def batch (p : Params) (i : Fin p.n) (level : ℕ) : ℕ+ :=
  ⟨2 ^ level * max 1 ⌈p.σ ^ 2 * (∑ j, (p.h j : ℝ)) /
    ((p.n : ℝ) ^ 2 * resolution p ^ 2 * (p.h i : ℝ))⌉₊, by positivity⟩

noncomputable def spacing (p : Params) : ℝ := resolution p / (p.d + 1 : ℕ)

noncomputable def radius (p : Params) (level : ℕ) : ℝ := 8 * 4 ^ level * resolution p

def width (p : Params) (level : ℕ) : ℕ :=
  7 + Nat.log2 ((p.n : ℕ) * (p.d + 1)) + 2 * level

def blockSize (p : Params) : ℕ := (p.d + p.n - 1) / p.n

end LongTails.Algorithms.LeonTuning
