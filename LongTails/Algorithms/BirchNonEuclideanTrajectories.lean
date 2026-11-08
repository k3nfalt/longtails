import LongTails.Algorithms.BirchNonEuclideanEvents

namespace LongTails.Algorithms.BirchNonEuclideanTrajectories

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents

noncomputable def localValues (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (start : Point p.d × Point p.d) : ℕ → Point p.d × Point p.d
  | 0 => start
  | n + 1 =>
      let old := localValues p lmo response η B H start n
      let v := (1 / (B : ℝ)) • response n old.1 + (1 - 1 / (B : ℝ)) • old.2
      (old.1 + (1 / (H : ℝ) * η) • (dualNorm p.N v • lmo v), v)

noncomputable def pairedValues (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → ℕ → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (dispatch : ℕ → ℕ) (initial : Point p.d) : ℕ → (ℕ → Point p.d) × (ℕ → Point p.d)
  | 0 => (fun _ => p.x0, fun _ => initial)
  | k + 1 =>
      let old := pairedValues p lmo response η B H dispatch initial k
      let src := dispatch k
      let packet := localValues p lmo (response k) η B H (old.1 src, old.2 src) H
      (Function.update old.1 (k + 1) (old.1 k + (packet.1 - old.1 src)),
        Function.update old.2 (k + 1) (old.2 k + (packet.2 - old.2 src)))

@[ext]
structure Values (d m : ℕ) where
  points : ℕ → Point d
  momenta : ℕ → Point d
  launchPoint : Fin m → Point d
  launchMomentum : Fin m → Point d
  point : Fin m → Point d
  momentum : Fin m → Point d

noncomputable def eventValues {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (e : Event m) (s : EventState m × Values p.d m) : EventState m × Values p.d m :=
  let publicState := s.1
  let regs := s.2
  let next := eventStep K R publicState e
  match e with
  | .query w =>
      let v := (1 / (B : ℝ)) • response (Sum.inr (w, publicState.schedule.serial w, publicState.progress w))
        (regs.point w) + (1 - 1 / (B : ℝ)) • regs.momentum w
      let x := regs.point w + (1 / (H : ℝ) * η) • (dualNorm p.N v • lmo v)
      (next, { regs with
        point := Function.update regs.point w x
        momentum := Function.update regs.momentum w v })
  | .complete w =>
      let k := publicState.schedule.accepted.length
      let committed := if k < K ∧ k - publicState.schedule.source w ≤ R then
        { regs with
          points := Function.update regs.points (k + 1)
            (regs.points k + (regs.point w - regs.launchPoint w))
          momenta := Function.update regs.momenta (k + 1)
            (regs.momenta k + (regs.momentum w - regs.launchMomentum w)) }
        else regs
      let launched := if k < K ∧ next.schedule.accepted.length < K then
        { committed with
          launchPoint := Function.update committed.launchPoint w (committed.points next.schedule.accepted.length)
          launchMomentum := Function.update committed.launchMomentum w (committed.momenta next.schedule.accepted.length)
          point := Function.update committed.point w (committed.points next.schedule.accepted.length)
          momentum := Function.update committed.momentum w (committed.momenta next.schedule.accepted.length) }
        else committed
      (next, launched)

end LongTails.Algorithms.BirchNonEuclideanTrajectories
