import LongTails.Proofs.WassersteinExtrapolationGeometry

open MeasureTheory
open LongTails.Setups.WassersteinSmoothComposite

namespace LongTails.Algorithms.WassersteinAcceleratedProximal

noncomputable def extrapolate {d : ℕ} {μ ν : Distribution d}
    (A : Transport μ ν) (β : ℝ) : Distribution d where
  law := μ.law.map (fun x => (1 + β) • x - β • A.toFun x)
  secondMoment := by
    have hm : Measurable (fun x => (1 + β) • x - β • A.toFun x) := by
      have hA := A.measurable
      fun_prop
    exact (integrable_map_measure (by fun_prop) hm.aemeasurable).mpr
      (LongTails.Proofs.WassersteinExtrapolationGeometry.extrapolated_second_moment A β)

inductive Phase where
  | forward
  | proximal
  | transport

structure State (d : ℕ) where
  phase : Phase
  previous : Distribution d
  current : Distribution d
  probe : Distribution d
  steps : ℕ

noncomputable def query (L : ℝ) {d : ℕ} (s : State d) : Query d :=
  match s.phase with
  | .forward => .forward (1 / (2 * L)) s.probe
  | .proximal => .proximal (1 / (2 * L)) s.probe
  | .transport => .transport s.current s.previous

noncomputable def update {d : ℕ} (s : State d) (r : Reply d) : State d :=
  match s.phase, r with
  | .forward, .distribution b => { s with phase := .proximal, probe := b }
  | .proximal, .distribution u =>
      { s with phase := .transport, previous := s.current, current := u, steps := s.steps + 1 }
  | .transport, .transport _ _ T =>
      { s with phase := .forward, probe := extrapolate T (((s.steps : ℝ) - 1) / ((s.steps : ℝ) + 2)) }
  | _, _ => s

noncomputable def algorithm (p : Public) :
    OracleTemplate.Algorithm (Query p.d) (Reply p.d) (Distribution p.d) where
  State := State p.d
  initial := fun _ => ⟨.forward, p.initial, p.initial, p.initial, 0⟩
  query := fun s => (0, query p.L s)
  update := update
  output := State.current

end LongTails.Algorithms.WassersteinAcceleratedProximal
