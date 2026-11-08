import LongTails.Setups.BirchResourceProtocol

namespace LongTails.Setups.BirchPowerTime

open Finset

structure Profile (Mode Device : Type*) where
  device : Mode → Device
  duration : Mode → ℝ
  samples : Mode → ℕ
  power : Mode → ℝ
  cap : ℝ

def Profile.Valid {Mode Device : Type*} (p : Profile Mode Device) : Prop :=
  (∀ i, 0 < p.duration i ∧ 0 < p.samples i ∧ 0 ≤ p.power i) ∧ 0 ≤ p.cap

def Admitted {Mode Device : Type*} (p : Profile Mode Device) (t : ℝ) (u : ℕ)
    (modes : Finset Mode) : Prop :=
  Set.InjOn p.device (modes : Set Mode) ∧ (∑ i ∈ modes, p.power i) ≤ p.cap ∧
    ∀ i ∈ modes, p.duration i ≤ t ∧ p.samples i ≤ u

noncomputable def rate {Mode Device : Type*} (p : Profile Mode Device) (modes : Finset Mode) : ℝ :=
  ∑ i ∈ modes, (p.samples i : ℝ) / p.duration i

noncomputable def envelope {Mode Device : Type*} [Fintype Mode]
    (p : Profile Mode Device) (t : ℝ) (u : ℕ) : ℝ := by
  classical
  exact (insert ∅ (Finset.univ.powerset.filter (Admitted p t u))).sup'
    (by exact ⟨∅, mem_insert_self _ _⟩) (rate p)

structure Job (Mode : Type*) where
  mode : Mode
  launch : ℝ

def Job.active {Mode Device : Type*} (p : Profile Mode Device) (j : Job Mode) (s : ℝ) : Prop :=
  s ∈ Set.Ico j.launch (j.launch + p.duration j.mode)

def Legal {Mode Device J : Type*} (p : Profile Mode Device) (jobs : J → Job Mode)
    (s : Finset J) : Prop := by
  classical
  exact ∀ t, (∀ j ∈ s, ∀ k ∈ s, (jobs j).active p t → (jobs k).active p t →
    p.device (jobs j).mode = p.device (jobs k).mode → j = k) ∧
    (∑ j ∈ s, if (jobs j).active p t then p.power (jobs j).mode else 0) ≤ p.cap

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Algorithms.BirchResourceNative

structure Params where
  geometry : BirchCollections.Params
  modes : ℕ
  devices : ℕ
  hardware : Profile (Fin modes) (Fin devices)
  cutoff : ℝ
  packetLimit : ℕ

noncomputable def block (p : Params) : ℕ := BirchCollections.batchSize (tuned p.geometry)

noncomputable def rounds (p : Params) : ℕ := BirchCollections.horizon (tuned p.geometry)

noncomputable def window (p : Params) : ℝ :=
  p.cutoff + (block p : ℝ) / envelope p.hardware p.cutoff p.packetLimit

def chargeOptions (p : Params) : Set ℕ :=
  {paid | block p ≤ paid ∧ ∃ modes, Admitted p.hardware p.cutoff p.packetLimit modes ∧
    rate p.hardware modes = envelope p.hardware p.cutoff p.packetLimit ∧
    ∃ packets ⊆ modes.sigma (fun i => range ⌊window p / p.hardware.duration i⌋₊),
      paid = ∑ j ∈ packets, p.hardware.samples j.1}

def Valid (p : Params) : Prop :=
  GeometryValid p.geometry ∧ p.hardware.Valid ∧ 0 < p.cutoff ∧
    0 < envelope p.hardware p.cutoff p.packetLimit

noncomputable def Allowed (p : Params)
    (A : Algorithm (Point p.geometry.d) (Point p.geometry.d) (Point p.geometry.d × ℝ)) : Prop :=
  ∃ (s : Finset (Σ _ : Fin p.modes, ℕ)) (jobs : (Σ _ : Fin p.modes, ℕ) → Job (Fin p.modes))
    (order : Fin s.card ≃ {j // j ∈ s}) (l : Layout s.card) (hS : 0 < s.card),
    Legal p.hardware jobs s ∧
    (∀ j ∈ s, 0 ≤ (jobs j).launch ∧ (jobs j).launch + p.hardware.duration (jobs j).mode ≤ window p ∧
      p.hardware.samples (jobs j).mode ≤ p.packetLimit) ∧
    (∀ i, 0 < l.accepted i ∧ l.accepted i ≤ l.paid i ∧
      l.paid i = p.hardware.samples (jobs (order i).val).mode) ∧
    (∑ i, l.accepted i) = block p ∧ (∑ i, l.paid i) ≤ block p + p.packetLimit ∧
    (∀ i j, l.parent i = some j →
      j.val < i.val ∧
      p.hardware.device (jobs (order j).val).mode = p.hardware.device (jobs (order i).val).mode ∧
      (jobs (order j).val).launch + p.hardware.duration (jobs (order j).val).mode ≤
        (jobs (order i).val).launch) ∧
    A = clocked (LongTails.Algorithms.BirchCollections.algorithm (compiledParams p.geometry l hS))
      (rounds p * window p)

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Instance p.geometry.d
  Query p := Point p.geometry.d
  Reply p := Point p.geometry.d
  Output p := Point p.geometry.d × ℝ
  publicInput := id
  valid := Valid
  admissible p I O := BirchCollections.spec.admissible (tuned p.geometry) I O
  successful p I out P :=
    Measurable out ∧ BirchCollections.spec.successful (tuned p.geometry) I (fun ω => (out ω).1) P ∧
      ∀ᵐ ω ∂(P : Measure _), (out ω).2 ≤ rounds p * window p
  allowedAlgorithm := Allowed

end LongTails.Setups.BirchPowerTime
