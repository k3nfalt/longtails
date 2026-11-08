import LongTails.Setups.BirchResourceProtocol

namespace LongTails.Setups.BirchRoutedTime

open Finset

structure Profile (Route Device : Type*) where
  duration : Device → ℝ
  path : Route → List Device

def Profile.Valid {Route Device : Type*} (p : Profile Route Device) (depth : ℕ) : Prop :=
  (∀ i, 0 < p.duration i) ∧ ∀ r, (p.path r).Nodup ∧ 0 < (p.path r).length ∧ (p.path r).length ≤ depth

def latency {Route Device : Type*} (p : Profile Route Device) (r : Route) : ℝ :=
  ((p.path r).map p.duration).sum

def offset {Route Device : Type*} [DecidableEq Device] (p : Profile Route Device)
    (r : Route) (i : Device) : ℝ :=
  (((p.path r).take ((p.path r).idxOf i)).map p.duration).sum

structure Job (Route : Type*) where
  route : Route
  launch : ℝ

def Job.active {Route Device : Type*} [DecidableEq Device] (p : Profile Route Device)
    (j : Job Route) (i : Device) (t : ℝ) : Prop :=
  i ∈ p.path j.route ∧
    t ∈ Set.Ico (j.launch + offset p j.route i) (j.launch + offset p j.route i + p.duration i)

def Legal {Route Device J : Type*} [DecidableEq Device] (p : Profile Route Device)
    (jobs : J → Job Route) (s : Finset J) : Prop :=
  ∀ i t, ∀ j ∈ s, ∀ k ∈ s, (jobs j).active p i t → (jobs k).active p i t → j = k

structure BufferedJob (Route Device : Type*) where
  route : Route
  start : Device → ℝ

def BufferedJob.active {Route Device : Type*} (p : Profile Route Device)
    (j : BufferedJob Route Device) (i : Device) (t : ℝ) : Prop :=
  i ∈ p.path j.route ∧ t ∈ Set.Ico (j.start i) (j.start i + p.duration i)

def BufferedLegal {Route Device J : Type*} (p : Profile Route Device)
    (jobs : J → BufferedJob Route Device) (s : Finset J) : Prop :=
  (∀ j ∈ s, (p.path (jobs j).route).Pairwise
    (fun i k => (jobs j).start i + p.duration i ≤ (jobs j).start k)) ∧
  ∀ i t, ∀ j ∈ s, ∀ k ∈ s, (jobs j).active p i t → (jobs k).active p i t → j = k

def FeasibleRate {Route Device : Type*} [Fintype Route] [DecidableEq Device]
    (p : Profile Route Device)
    (t : ℝ) (x : Route → ℝ) : Prop :=
  (∀ r, 0 ≤ x r) ∧ (∀ r, t < latency p r → x r = 0) ∧
    ∀ i, p.duration i * (∑ r, if i ∈ p.path r then x r else 0) ≤ 1

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Algorithms.BirchResourceNative

structure Params where
  geometry : BirchCollections.Params
  routes : ℕ
  devices : ℕ
  depth : ℕ
  hardware : Profile (Fin routes) (Fin devices)
  cutoff : ℝ
  fractionalRate : Fin routes → ℝ

noncomputable def block (p : Params) : ℕ := BirchCollections.batchSize (tuned p.geometry)

noncomputable def rounds (p : Params) : ℕ := BirchCollections.horizon (tuned p.geometry)

noncomputable def window (p : Params) : ℝ :=
  2 * (p.depth : ℝ) * ((p.depth : ℝ) * block p / (∑ r, p.fractionalRate r)) +
    (4 * p.depth + 2) * p.cutoff

def Valid (p : Params) : Prop :=
  GeometryValid p.geometry ∧ 0 < p.depth ∧ p.hardware.Valid p.depth ∧ 0 < p.cutoff ∧
    FeasibleRate p.hardware p.cutoff p.fractionalRate ∧ 0 < ∑ r, p.fractionalRate r

noncomputable def Allowed (p : Params)
    (A : Algorithm (Point p.geometry.d) (Point p.geometry.d) (Point p.geometry.d × ℝ)) : Prop :=
  ∃ (jobs : ℕ → Job (Fin p.routes)) (l : Layout (block p)) (hB : 0 < block p),
    Legal p.hardware jobs (range (block p)) ∧
    (∀ j < block p, 0 ≤ (jobs j).launch ∧
      (jobs j).launch + latency p.hardware (jobs j).route ≤ window p) ∧
    (∀ i, l.accepted i = 1 ∧ l.paid i = 1) ∧
    (∀ i j, l.parent i = some j →
      j.val < i.val ∧ (jobs j).route = (jobs i).route ∧
      (jobs j).launch + latency p.hardware (jobs j).route ≤ (jobs i).launch) ∧
    A = clocked (LongTails.Algorithms.BirchCollections.algorithm (compiledParams p.geometry l hB))
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

end LongTails.Setups.BirchRoutedTime
