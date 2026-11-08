import LongTails.Algorithms.BirchCollectionNested
import LongTails.Algorithms.BirchCollectionBatches
import LongTails.Algorithms.BirchCollectionRetune

namespace LongTails.Algorithms.BirchCollectionRetainedQuota

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested (Layout State runRound start advance workers)
open LongTails.Algorithms.BirchCollectionBatches (batchAndMarkWithMove)
open LongTails.Algorithms.BirchCollectionRetune (retune)

structure Phase (m : ℕ) where
  batch : ℕ
  arrivals : List (Fin m)

def Phase.work {m : ℕ} (phase : Phase m) : ℕ :=
  phase.batch * phase.arrivals.length

def Phase.Valid {m : ℕ} (B : ℕ) (phase : Phase m) : Prop :=
  0 < phase.batch ∧ 0 < phase.arrivals.length ∧ B ≤ 2 * phase.work ∧ phase.work ≤ B

def Complete {m : ℕ} (schedule : ℕ → Phase m) (B K : ℕ) : Prop :=
  ∀ k, 0 < k → k < K → (schedule k).Valid B

def volume {m : ℕ} (schedule : ℕ → Phase m) (B k : ℕ) : ℕ :=
  if k = 0 then B else (schedule k).work

def cut {m : ℕ} (schedule : ℕ → Phase m) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cut schedule k + if k = 0 then 1 else (schedule k).arrivals.length

noncomputable def leafGain (B batch : ℕ) : ℝ := (batch : ℝ) / (8 * B)

noncomputable def gain (w : ℝ) : ℝ × ℝ :=
  if w = 1 / 2 then (1, 1 / 8) else (w, w)

noncomputable def stepRound {m : ℕ} (layout : Layout m) (B : ℕ) (s : Round m)
    (k : ℕ) (phase : Phase m) : Round m :=
  if k = 0 then
    s.append (batchAndMarkWithMove s.trace 0 (s.trace.markers.getLast?.getD 0)
      (List.replicate B 0) (1 / 2))
  else runRound layout phase.arrivals.length phase.batch (leafGain B phase.batch) s phase.arrivals

noncomputable def rounds {m : ℕ} (layout : Layout m) (B : ℕ)
    (schedule : ℕ → Phase m) : ℕ → Round m
  | 0 => Round.initial m {} []
  | k + 1 => stepRound layout B (rounds layout B schedule k) k (schedule k)

noncomputable def phaseAt {m : ℕ} (schedule : ℕ → Phase m) (K n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, k < K ∧ cut schedule k ≤ n ∧ n < cut schedule (k + 1) then Nat.find h else 0

noncomputable def ordering {m : ℕ} (schedule : ℕ → Phase m) (K : ℕ) :
    LongTails.Setups.BirchCollections.Ordering where
  labels := List.range (cut schedule K)
  cut := cut schedule
  frontier := fun n => cut schedule (phaseAt schedule K n)
  anchor := fun _ => 0
  scale := fun _ j => if j = 0 then 1 else 2
  renewalFrontier := fun _ j => cut schedule (phaseAt schedule K j)

noncomputable def controls (D : ℕ) : Controls where
  lowerMass := 1 / 16
  upperMass := 1 / 8
  massRatio := 2
  amplification := 8
  initialization := 0
  waste := D

def extra {m : ℕ} (layout : Layout m) (Q : ℕ) (s : State m) (w : Fin m) : ℕ :=
  let i := layout.cluster (layout.group w)
  if s.outer.completed + 1 = Q then 0
  else if layout.quota i = some ((s.cluster i).completed + 1) then
    (workers layout i).length - 1
  else 0

def restartTally {m : ℕ} (layout : Layout m) (Q b : ℕ) (g : ℝ) :
    State m → List (Fin m) → ℕ
  | _, [] => 0
  | s, w :: tail => extra layout Q s w + restartTally layout Q b g (advance layout Q b g s w) tail

noncomputable def phaseWaste {m : ℕ} (layout : Layout m) (B : ℕ) (s : Round m)
    (phase : Phase m) : ℕ :=
  let Q := phase.arrivals.length
  let b := phase.batch
  let g := leafGain B b
  let root := start layout b g s.trace s.events
  b * (m - 1 + restartTally layout Q b g root phase.arrivals)

noncomputable def waste {m : ℕ} (layout : Layout m) (B : ℕ)
    (schedule : ℕ → Phase m) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K, if k = 0 then 0 else phaseWaste layout B (rounds layout B schedule k) (schedule k)

noncomputable def retainedQuota {m : ℕ} (p : Params) (layout : Layout m)
    (schedule : ℕ → Phase m) : Params :=
  let q := {p with workers := m + 1, controls := controls 0}
  let B := batchSize q
  let K := horizon q
  let s := rounds layout B schedule K
  {q with
    controls := controls (waste layout B schedule K)
    events := s.events.map (retune gain)
    ordering := ordering schedule K}

end LongTails.Algorithms.BirchCollectionRetainedQuota
