import LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
import LongTails.Proofs.DashaDistributedBudget

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DashaFreeBroadcastDeterministic

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex

noncomputable def effectiveParameters (p : Params) : Params :=
  { p with L := min p.L p.Lhat
           Lhat := if p.n = 1 then min p.L p.Lhat else p.Lhat
           G := if p.n = 1 then min p.G (Real.sqrt (2 * min p.L p.Lhat * p.Δ)) else p.G }

noncomputable def compressionVariance (p : Params) (k : Fin p.d) (r : ℕ) : ℝ :=
  (1 + 2 / (4 : ℝ) ^ r) * ((p.d : ℝ) / (k.val + 1)) - 1

noncomputable def mainPrecisionLimit (p : Params) : ℕ :=
  2 + Nat.size ⌈2 * p.Lhat / (min p.L p.Lhat * Real.sqrt (p.n : ℝ))⌉₊

abbrev MainIndex (p : Params) := Fin p.d × Fin (mainPrecisionLimit p + 1)

noncomputable def initialPrecisionLimit (p : Params) (i : MainIndex p) : ℕ :=
  2 + Nat.size ⌈Real.sqrt (2 * (4 * compressionVariance p i.1 i.2.val + 1)) * p.G / (p.ε * Real.sqrt (p.n : ℝ))⌉₊

abbrev SearchSpace (p : Params) := (i : MainIndex p) × (Option (Fin p.d × Fin (initialPrecisionLimit p i + 1)) × Bool)

noncomputable def rateDenominator (p : Params) (i : MainIndex p) : ℝ :=
  min p.L p.Lhat + p.Lhat * Real.sqrt (compressionVariance p i.1 i.2.val * (2 * compressionVariance p i.1 i.2.val + 1) / p.n)

noncomputable def latticeSpacing (p : Params) (i : MainIndex p) : ℝ :=
  p.ε * Real.sqrt ((p.n : ℝ) / (p.d * (compressionVariance p i.1 i.2.val + 1))) / 16

noncomputable def iterationCount (p : Params) (c : SearchSpace p) : ℕ :=
  match c.2.1 with
  | none => 1 + ⌈32 * p.Δ * rateDenominator p c.1 / p.ε ^ 2⌉₊
  | some i₀ => 1 + ⌈(32 * p.Δ * rateDenominator p c.1 +
      4 * ((4 * compressionVariance p c.1.1 c.1.2.val + 1) * compressionVariance p i₀.1 i₀.2.val * p.G ^ 2 / p.n)) / p.ε ^ 2⌉₊

noncomputable def initialTrackingRange (p : Params) (c : SearchSpace p) : ℝ :=
  min p.G (Real.sqrt (2 * min p.L p.Lhat * p.Δ)) +
    (match c.2.1 with | none => 0 | some i₀ => (2 * ((p.d : ℝ) / (i₀.1.val + 1)) + 1) * p.G) +
    3 * latticeSpacing p c.1 * Real.sqrt (p.d : ℝ)

noncomputable def inputRange (p : Params) (c : SearchSpace p) : ℝ :=
  ((p.d : ℝ) / (c.1.1.val + 1)) * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * (1 / (8 * rateDenominator p c.1))) *
    initialTrackingRange p c / latticeSpacing p c.1

noncomputable def rangeGrowth (p : Params) (i : MainIndex p) : ℝ :=
  (2 + 2 * ((p.d : ℝ) / (i.1.val + 1))) * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * (1 / (8 * rateDenominator p i)))

noncomputable def initialPayload (p : Params) (c : SearchSpace p) : ℕ :=
  match c.2.1 with
  | none => p.d * (if c.2.2 then Nat.size ⌈(p.n : ℝ) *
      (min p.G (Real.sqrt (2 * min p.L p.Lhat * p.Δ)) + latticeSpacing p c.1 * Real.sqrt (p.d : ℝ)) / latticeSpacing p c.1⌉₊ + 1
      else Nat.size ⌈p.G / latticeSpacing p c.1 + 1⌉₊ + 1)
  | some i₀ => (i₀.1.val + 1) * (i₀.2.val + Nat.size (Nat.size ⌈((p.d : ℝ) / (i₀.1.val + 1)) * p.G / latticeSpacing p c.1⌉₊) + 3)

noncomputable def roundPayload (p : Params) (c : SearchSpace p) : ℕ :=
  (c.1.1.val + 1) * (c.1.2.val + Nat.size (Nat.size ⌈inputRange p c⌉₊ + iterationCount p c * Nat.size ⌈rangeGrowth p c.1⌉₊) + 3)

noncomputable def budget (p : Params) : Time := if min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2 then 0 else Finset.univ.inf' Finset.univ_nonempty (fun c : SearchSpace (effectiveParameters p) => (iterationCount (effectiveParameters p) c : Time) * (Finset.univ.sup p.h + p.l + 64 * p.b) + p.b * ((initialPayload (effectiveParameters p) c : Time) + ((iterationCount (effectiveParameters p) c - 1 : ℕ) : Time) * (roundPayload (effectiveParameters p) c : Time)))

theorem result : TimedConvergence LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex.spec budget := by
  classical
  refine ⟨LongTails.Algorithms.DashaDistributedSelection.tuned, ?_⟩
  intro p hp
  refine ⟨trivial, ?_⟩
  intro f O hO
  have hcost (p : Params) (c : SearchSpace p) :
      LongTails.Algorithms.DashaDistributedSelection.candidateCost p c =
        (iterationCount p c : Time) * (Finset.univ.sup p.h + p.l + 64 * p.b) +
          p.b * ((initialPayload p c : Time) + ((iterationCount p c - 1 : ℕ) : Time) * (roundPayload p c : Time)) := by
    change LongTails.Algorithms.DashaDistributed.timeBudget p
      (LongTails.Algorithms.DashaDistributedTrackedParameters.trackedConfig p
        (LongTails.Algorithms.DashaDistributedSelection.mainChoice p c.1)
        (LongTails.Algorithms.DashaDistributedSelection.initializerChoice p c) c.2.2) = _
    rw [LongTails.Proofs.DashaDistributedBudget.timeBudget_expanded]
    rcases c with ⟨i, j, modular⟩
    cases j <;> cases modular <;>
      simp only [LongTails.Algorithms.DashaDistributedTrackedParameters.trackedConfig,
        LongTails.Algorithms.DashaDistributedParameters.config,
        LongTails.Algorithms.DashaDistributedSelection.initializerChoice,
        LongTails.Algorithms.DashaDistributed.initialBits,
        LongTails.Algorithms.DashaDistributed.roundBits,
        Option.map_none, Option.map_some, Option.isNone_none, Option.isNone_some,
        Bool.and_false, Bool.and_true, Bool.false_eq_true,
        ite_false, ite_true, add_zero, iterationCount, initialPayload, roundPayload] <;> rfl
  have hb : budget p = LongTails.Algorithms.DashaDistributedSelection.timeBound p := by
    unfold budget LongTails.Algorithms.DashaDistributedSelection.timeBound
    split_ifs
    · rfl
    · rw [LongTails.Proofs.DashaDistributedSelection.selected_inf]
      apply congrArg (Finset.univ.inf' Finset.univ_nonempty)
      funext c
      exact (hcost _ c).symm
  rw [hb]
  exact LongTails.Proofs.DashaDistributedSelection.tuned_guarantee hp f O hO

end LongTails.Theorems.DashaFreeBroadcastDeterministic
