import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LongTails.Algorithms.LoraGd
import LongTails.Algorithms.SilverSchedule
import LongTails.Setups.LocalSmoothStronglyConvexLora

namespace LongTails.Algorithms.LoraSilver

open LongTails.Setups.LocalSmoothStronglyConvexLora

noncomputable def depth (p : Params) : ℕ :=
  ⌈Real.log (1 + 512 * p.ρ * p.R ^ 2 / (p.μ * p.s ^ 2)) /
    Real.log (1 + Real.sqrt 2)⌉₊

noncomputable def warmup (p : Params) : ℕ :=
  128 * ⌈64 * p.ρ * p.R ^ 2 / (p.μ * p.s ^ 2)⌉₊ * (depth p + 1)

noncomputable def epochs (p : Params) : ℕ :=
  ⌈Real.log (1 + 32 * p.ρ * p.R ^ 4 / p.ε) / Real.log 4⌉₊

noncomputable def schedule (p : Params) : List ℝ :=
  List.replicate (warmup p) 1 ++ (List.replicate (epochs p) (SilverSchedule.steps (depth p))).flatten

noncomputable def method (p : Params) :=
  LoraGd.method (fun k => ((schedule p)[k]?.getD 1) / (8 * p.ρ * p.R ^ 2)) p.x₀

end LongTails.Algorithms.LoraSilver
