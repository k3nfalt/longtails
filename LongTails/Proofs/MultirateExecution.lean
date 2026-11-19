import LongTails.Proofs.LocalReservationExecution
import LongTails.Proofs.MultirateTermination

namespace LongTails.Proofs.MultirateExecution

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex (system)
open LongTails.Algorithms.MultirateSchedule
open MultirateTermination LocalReservations

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
  {limit : Time} {seed : Samples p} {out : Point p}
  {rows : Fin p.n → List (LeonReservations.Frame (network p))}

lemma execute (cert : Certified g seed limit rows) (ab : (algorithm p limit).Seed)
    (htr : ∀ i, LeonTranscript.Trace ((algorithm p limit).initial i ab).program
      ((rows i).map (fun c => c.op i)) out) :
    DistributedTemplate.execute (system (network p) g P) (algorithm p limit) limit ab seed = out := by
  let A := algorithm p limit
  let O := system (network p) g P
  let init := DistributedTemplate.initial O A limit (ab,seed)
  let start : (i : Fin p.n) → LeonReservations.Cursor (rows i) := fun i => ⟨[],rows i,rfl⟩
  have hinit : Valid g P limit seed rows out (asLeon g P limit init) start := by
    refine ⟨⟨htr,fun _ => ⟨rfl,rfl,rfl⟩,fun _ _ => LeonLinkLedger.empty⟩,fun _ => zero_le,fun _ _ => le_rfl⟩
  obtain ⟨k,hend⟩ := finite g P limit (ab,seed) limit le_rfl
  rw [DistributedExecution.execute_eq_terminal O A limit (ab,seed) k hend]
  have hrun (k : ℕ) (c : RunState g P limit) (hc : c.time ≤ c.deadline) (hd : c.deadline = limit)
      (cur : (i : Fin p.n) → LeonReservations.Cursor (rows i)) (h : Valid g P limit seed rows out (asLeon g P limit c) cur) :
      ∃ cur', Valid g P limit seed rows out (asLeon g P limit (run O A k c)) cur' := by
    induction k generalizing c cur with
    | zero => exact ⟨cur,h⟩
    | succ k ih =>
      cases hs : step O A c with
      | none => simpa [run,hs] using (show ∃ cs, Valid g P limit seed rows out (asLeon g P limit c) cs from ⟨cur,h⟩)
      | some d =>
        have hstep := step_eq g P limit c
        change (step O A c).map _ = _ at hstep
        rw [hs,Option.map_some] at hstep
        obtain ⟨cs,hcs⟩ := LocalReservationExecution.step_valid cert _ _ hd hc cur h hstep.symm
        simpa [run,hs] using ih d (DistributedExecution.step_time_le_deadline O A c d hc hs)
          ((DistributedExecution.step_deadline O A c d hs).trans hd) cs hcs
  obtain ⟨cs,hcs⟩ := hrun k init zero_le rfl start hinit
  have hend' := step_eq g P limit (run O A k init)
  change (step O A _).map _ = _ at hend'
  change step O A (run O A k init) = none at hend
  rw [hend, Option.map_none] at hend'
  exact LocalReservationExecution.terminal_output cert _
    (DistributedExecution.run_deadline O A init k) (DistributedExecution.run_time_le_deadline O A init k zero_le)
    cs hcs hend'.symm

end LongTails.Proofs.MultirateExecution
