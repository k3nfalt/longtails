import LongTails.Algorithms.DashaDistributedNormalization
import LongTails.Algorithms.DashaDistributedTrackedParameters
import Mathlib.Data.Finset.Max

namespace LongTails.Algorithms.DashaDistributedSelection

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open DashaScaling DashaDistributed DashaDistributedParameters DashaDistributedNormalization DashaDistributedTrackedParameters

noncomputable def mainPrecision (p : Params) : ℕ :=
  2 + Nat.size ⌈2 * p.Lhat / (min p.L p.Lhat * Real.sqrt (p.n : ℝ))⌉₊

noncomputable def initialPrecision (p : Params) (c : Choice p) : ℕ :=
  2 + Nat.size ⌈Real.sqrt (2 * (4 * variance p c + 1)) * p.G / (p.ε * Real.sqrt (p.n : ℝ))⌉₊

noncomputable def capChoice (p : Params) (c : Choice p) : Choice p :=
  ⟨c.block, min c.precision (mainPrecision p)⟩

noncomputable def capInitializer (p : Params) (c initializer : Choice p) : Choice p :=
  ⟨initializer.block, min initializer.precision (initialPrecision p c)⟩

abbrev MainIndex (p : Params) := Fin p.d × Fin (mainPrecision p + 1)

noncomputable def mainChoice (p : Params) (index : MainIndex p) : Choice p :=
  ⟨index.1, index.2.val⟩

abbrev InitialIndex (p : Params) (index : MainIndex p) :=
  Option (Fin p.d × Fin (initialPrecision p (mainChoice p index) + 1)) × Bool

abbrev Candidate (p : Params) := (index : MainIndex p) × InitialIndex p index

instance (p : Params) : Nonempty (Candidate p) :=
  ⟨⟨(⟨0, p.d.pos⟩, ⟨0, Nat.zero_lt_succ _⟩), (none, false)⟩⟩

noncomputable def candidateOfChoices (p : Params) (c : Choice p) (initializer : Option (Choice p))
    (modularInitialization : Bool) : Candidate p := by
  let index : MainIndex p := (c.block, ⟨min c.precision (mainPrecision p), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
  exact ⟨index, (initializer.map (fun c₀ => (c₀.block,
    ⟨min c₀.precision (initialPrecision p (mainChoice p index)), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)),
    modularInitialization)⟩

noncomputable def initializerChoice (p : Params) (candidate : Candidate p) : Option (Choice p) :=
  candidate.2.1.map fun index => ⟨index.1, index.2.val⟩

noncomputable def candidateCost (p : Params) (candidate : Candidate p) : Time :=
  timeBudget p (trackedConfig p (mainChoice p candidate.1) (initializerChoice p candidate) candidate.2.2)

noncomputable def selected (p : Params) : Candidate p := by
  classical
  exact Classical.choose (Finset.univ.exists_min_image (candidateCost p) Finset.univ_nonempty)

noncomputable def chosenConfig (p : Params) : Config p :=
  trackedConfig p (mainChoice p (selected p).1) (initializerChoice p (selected p)) (selected p).2.2

noncomputable def timeBound (p : Params) : Time :=
  if min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2 then 0
  else candidateCost (normalize p) (selected (normalize p))

noncomputable def tuned (p : Params) : Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) (p.n + 1) := by
  classical
  exact if min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2 then idle p
    else algorithm (normalize p) (chosenConfig (normalize p))

end LongTails.Algorithms.DashaDistributedSelection
