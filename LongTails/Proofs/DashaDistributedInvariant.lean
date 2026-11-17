import LongTails.Proofs.DashaDistributedDownlink

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedInvariant

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedTiming
open LongTails.Proofs.DashaDistributedPipeline
open LongTails.Proofs.DashaDistributedBroadcast
open LongTails.Proofs.DashaDistributedComplete
open LongTails.Proofs.DashaDistributedDownlink

variable {p : Params}

lemma event_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (v : Fin (p.n + 1)) (notification : Event (ComputeReply p) (CommReply p))
    (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, notification), next)) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  cases notification with
  | wake => exact wake_step_pipeline cfg f seed selected c hp hdeadline v next hevent
  | computed reply =>
      cases reply with
      | computed input value =>
          induction v using Fin.cases with
          | zero =>
              obtain ⟨state, ha, _⟩ := DistributedExecution.computed_event (system p f) (algorithm p cfg)
                c c.time 0 (.computed input value) next hevent
              simp [system, LongTails.Setups.StarNetwork.computation] at ha
          | succ i => exact computed_step_pipeline cfg f seed selected c hp hexact htimely hdeadline i input value next hevent
  | received reply =>
      cases reply with
      | received source bits =>
          induction v using Fin.cases with
          | zero =>
              induction source using Fin.cases with
              | zero =>
                  have hm := (received_at_finish cfg f c htimely 0 0 bits next hevent).1
                  rw [hp.links 0 0] at hm
                  simp only [Fin.cases_zero, reduceCtorEq] at hm
              | succ i => exact upload_step_pipeline cfg f seed selected c hp hexact htimely hdeadline i (hpos i) bits next hevent
          | succ i =>
              induction source using Fin.cases with
              | zero => exact downlink_step_pipeline cfg f seed selected c hp hexact htimely hdeadline i bits next hevent
              | succ j =>
                  have hm := (received_at_finish cfg f c htimely j.succ i.succ bits next hevent).1
                  rw [hp.links j.succ i.succ] at hm
                  simp only [Fin.cases_succ, Fin.succ_ne_zero, false_and, ite_false, reduceCtorEq] at hm

lemma step_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c next : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) (htimely : Timely cfg f c)
    (hstep : step (system p f) (algorithm p cfg) c = some next) :
    Pipeline cfg f seed selected next := by
  by_cases hlate : c.deadline < c.time
  · simp only [step, ite_eq_left hlate, reduceCtorEq] at hstep
  · cases he : event (system p f) (algorithm p cfg) c c.time with
    | none =>
        simp only [step, ite_eq_right hlate, he] at hstep
        split_ifs at hstep with ht
        have hn := Option.some.inj hstep
        subst next
        exact jump_pipeline cfg f seed selected c hp he
    | some value =>
        rcases value with ⟨⟨v, notification⟩, oracle⟩
        obtain ⟨nextState, hs, hn⟩ := event_pipeline cfg f seed selected c hp hexact hpos htimely
          (le_of_not_gt hlate) v notification oracle he
        have heq : next = nextState := Option.some.inj (hstep.symm.trans hs)
        exact heq ▸ hn

lemma run_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) (T : Time) (k : ℕ) :
    Pipeline cfg f seed selected (run (system p f) (algorithm p cfg) k
      (initial (system p f) (algorithm p cfg) T ((selected, seed), ()))) := by
  have hrun : ∀ j (c : ExecutionState (system p f) (algorithm p cfg)),
      Pipeline cfg f seed selected c → Timely cfg f c →
      Pipeline cfg f seed selected (run (system p f) (algorithm p cfg) j c) := by
    intro j
    induction j with
    | zero => intro c hc _; exact hc
    | succ j ih =>
        intro c hc ht
        cases hs : step (system p f) (algorithm p cfg) c with
        | none => simpa only [run, hs] using hc
        | some next =>
            simpa only [run, hs] using ih next (step_pipeline cfg f seed selected c next hc hexact hpos ht hs)
              (step_timely cfg f c next ht hs)
  exact hrun k _ (initial_pipeline cfg f seed selected T) (initial_timely cfg f T ((selected, seed), ()))

lemma execute_eq_ideal_of_finite (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i)
    (hfinite : FiniteEvents (system p f) (algorithm p cfg) (timeBudget p cfg) ((selected, seed), ())) :
    execute (system p f) (algorithm p cfg) (timeBudget p cfg) (selected, seed) () =
      idealOutput p cfg f (selected, seed) := by
  obtain ⟨k, hk⟩ := hfinite (timeBudget p cfg) le_rfl
  rw [DistributedExecution.execute_eq_terminal (system p f) (algorithm p cfg) (timeBudget p cfg)
    ((selected, seed), ()) k hk]
  apply terminal_pipeline_output cfg f seed selected _ (run_pipeline cfg f seed selected hexact hpos _ k)
  · exact DistributedExecution.run_time_le_deadline (system p f) (algorithm p cfg) _ k (by simp [initial])
  · rw [DistributedExecution.run_deadline]
    exact le_rfl
  · exact hk

end LongTails.Proofs.DashaDistributedInvariant
