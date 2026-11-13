import LongTails.Proofs.BirchAveragingReplay

namespace LongTails.Setups.BirchNonIID

open OracleTemplate
open OracleTemplate.Rennala (Point)

def scheduledWorker (workers : ℕ) (hw : 0 < workers) (t : ℕ) : Fin workers :=
  ⟨t % workers, Nat.mod_lt _ hw⟩

def replyBlocks {workers d : ℕ} (K : ℕ) (tape : ℕ → Point d)
    (r k : ℕ) (i : Fin workers) : Point d :=
  tape ((r * K + k) * workers + i.val)

/-- Public query reconstruction from the reply tape, with no instance argument. -/
noncomputable def averagingQuery {workers d : ℕ} (hw : 0 < workers)
    (x0 : Point d) (η : ℝ) (K t : ℕ) (tape : ℕ → Point d) : Fin workers × Point d :=
  let i := scheduledWorker workers hw t
  let r := t / workers / K
  let k := t / workers % K
  let replies := replyBlocks (workers := workers) K tape
  (i, replayLocal (replayServer x0 η K replies r) η (replies r) i k)

structure AveragingState (d : ℕ) where
  count : ℕ
  tape : ℕ → Point d
  selected : ℕ
  saved : Point d

/-- Fresh-anchor corrected averaging, with a uniformly selected queried point.
The first block of each round is both its control collection and first local query block. -/
noncomputable def correctedAveraging (workers d K R : ℕ)
    (hw : 0 < workers) (hK : 0 < K) (hR : 0 < R) (x0 : Point d) (η : ℝ) :
    Algorithm (Point d) (Point d) (Point d) workers := by
  let T := workers * K * R
  have hT : 0 < T := Nat.mul_pos (Nat.mul_pos hw hK) hR
  letI : NeZero T := ⟨Nat.ne_of_gt hT⟩
  exact {
    Seed := Fin T
    law := ⟨(PMF.uniformOfFintype (Fin T)).toMeasure, inferInstance⟩
    State := AveragingState d
    initial := fun j => ⟨0, fun _ => 0, j.val, x0⟩
    query := fun s => averagingQuery hw x0 η K s.count s.tape
    update := fun s reply =>
      ⟨s.count + 1, Function.update s.tape s.count reply, s.selected,
        if s.count = s.selected then (averagingQuery hw x0 η K s.count s.tape).2 else s.saved⟩
    output := fun s => s.saved }

theorem measurable_averagingQuery {workers d : ℕ} (hw : 0 < workers)
    (x0 : Point d) (η : ℝ) (K t : ℕ) :
    Measurable (fun tape : ℕ → Point d => (averagingQuery hw x0 η K t tape).2) := by
  apply measurable_replayLocal
  · apply measurable_replayServer
    intro r k i
    exact measurable_pi_apply _
  · intro k i
    exact measurable_pi_apply _

end LongTails.Setups.BirchNonIID
