import LongTails.TemplateTimed

namespace LongTails.Setups.NetworkModels

open OracleTemplate

structure QueueNetwork (n : ℕ) where
  computeTime : Fin n → ℝ
  channel : Fin n → Fin n → ℕ
  latency : Fin n → Fin n → ℝ
  timePerFloat : Fin n → Fin n → ℝ
  connected : Fin n → Fin n → Bool

structure QueueState (n : ℕ) where
  computeFree : Fin n → ℝ
  channelFree : ℕ → ℝ
  scheduled : List (ℝ × Fin n × Completion n)

variable {n : ℕ}

noncomputable def scheduleCall (N : QueueNetwork n) (s : QueueState n) (t : ℝ) (v : Fin n)
    (id : ℕ) : QueueState n :=
  let finish := max t (s.computeFree v) + N.computeTime v
  { s with
    computeFree := Function.update s.computeFree v finish
    scheduled := s.scheduled ++ [(finish, v, .done id)] }

noncomputable def scheduleDelivery (N : QueueNetwork n) (t : ℝ) (source : Fin n) (size id : ℕ)
    (acc : QueueState n × List (ℕ × ℝ)) (target : Fin n) : QueueState n × List (ℕ × ℝ) :=
  let s := acc.1
  let c := N.channel source target
  let transmitted := match acc.2.lookup c with
    | some finish => finish
    | none => max t (s.channelFree c) + N.timePerFloat source target * size
  ({ s with
      channelFree := Function.update s.channelFree c transmitted
      scheduled := s.scheduled ++
        [(transmitted + N.latency source target, source, .delivered id target)] },
    (c, transmitted) :: acc.2)

noncomputable def scheduleSend (N : QueueNetwork n) (s : QueueState n) (t : ℝ) (source : Fin n)
    (targets : Finset (Fin n)) (size id : ℕ) : QueueState n :=
  (((List.finRange n).filter fun w => w ∈ targets ∧ N.connected source w).foldl
    (scheduleDelivery N t source size id) (s, [])).1

def abortCalls (s : QueueState n) (t : ℝ) (v : Fin n) : QueueState n :=
  { s with
    computeFree := Function.update s.computeFree v t
    scheduled := s.scheduled.filter fun entry =>
      match entry.2.2 with
      | .done _ => entry.2.1 ≠ v
      | .delivered _ _ => true }

noncomputable def queueSubmit (N : QueueNetwork n) (s : QueueState n) (t : ℝ) :
    Header n → QueueState n
  | .call v id => scheduleCall N s t v id
  | .send source targets size id => scheduleSend N s t source targets size id
  | .abort v => abortCalls s t v

noncomputable def earliest {α : Type} (l : List (ℝ × α)) : Option (ℝ × α) :=
  l.foldl (fun best entry => match best with
    | none => some entry
    | some b => if entry.1 < b.1 then some entry else some b) none

noncomputable def queueNext (s : QueueState n) : Option (ℝ × Completion n × QueueState n) :=
  (earliest s.scheduled).map fun entry =>
    (entry.1, entry.2.2,
      { s with scheduled := s.scheduled.filter fun other => other.2.2 ≠ entry.2.2 })

noncomputable def queueEnvironment (N : QueueNetwork n) : Environment n where
  State := QueueState n
  initial _ := ⟨fun _ => 0, fun _ => 0, []⟩
  submit := queueSubmit N
  next := queueNext

def starNetwork (m : ℕ) (τ : Fin m → ℝ) (hUp hDown : ℝ) : QueueNetwork (m + 1) where
  computeTime := Fin.cases 0 τ
  channel u _ := u.val
  latency _ _ := 0
  timePerFloat u _ := if u = 0 then hDown else hUp
  connected u v := decide ((u = 0) ≠ (v = 0))

def SilentOracle {Query Reply : Type} [Zero Reply] (oracle : Oracle Query Reply) : Prop :=
  ∀ history query seed, oracle.answer history query seed = 0

end LongTails.Setups.NetworkModels
