import LongTails.TemplateDistributed
import LongTails.Setups.StarNetwork
import Mathlib.Tactic
import Mathlib.Data.Finset.Option

namespace LongTails.Proofs.DistributedExecution

open DistributedTemplate

lemma argmin_ready {α : Type} (times : α → Time) (items : List α) (time : Time) :
    (∃ item, items.argmin times = some item ∧ times item ≤ time) ↔
      ∃ item ∈ items, times item ≤ time := by
  constructor
  · rintro ⟨item, hi, ht⟩
    exact ⟨item, List.argmin_mem hi, ht⟩
  · rintro ⟨item, hi, ht⟩
    cases hmin : items.argmin times with
    | none =>
        have hempty := List.argmin_eq_none.mp hmin
        simp [hempty] at hi
    | some first =>
        exact ⟨first, rfl, (List.le_of_mem_argmin hi hmin).trans ht⟩

lemma computation_ready {Input Output Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (compute : Fin n → Input → Seed → ℕ → Output)
    (i : Fin n) (s : LongTails.Setups.StarNetwork.ComputationState Input Seed) (time : Time) :
    ((LongTails.Setups.StarNetwork.computation N compute).answer i.succ s time).isSome ↔
      ∃ finish input, s.pending = some (finish, input) ∧ finish ≤ time := by
  cases hp : s.pending with
  | none => simp [LongTails.Setups.StarNetwork.computation, hp]
  | some value =>
      rcases value with ⟨finish, input⟩
      by_cases ht : finish ≤ time <;>
        simp [LongTails.Setups.StarNetwork.computation, hp, ht]

lemma computation_submit_idle {Input Output Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (compute : Fin n → Input → Seed → ℕ → Output)
    (i : Fin n) (s : LongTails.Setups.StarNetwork.ComputationState Input Seed)
    (time : Time) (input : Input) (hpending : s.pending = none) :
    (LongTails.Setups.StarNetwork.computation N compute).submit i.succ s time (.evaluate input) =
      { s with pending := some (time + N.computeTime i, input) } := by
  simp [LongTails.Setups.StarNetwork.computation, hpending]

lemma computation_wait {Input Output Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (compute : Fin n → Input → Seed → ℕ → Output)
    (i : Fin n) (s : LongTails.Setups.StarNetwork.ComputationState Input Seed)
    (time finish : Time) (input : Input)
    (hpending : s.pending = some (finish, input)) (ht : time < finish) :
    (LongTails.Setups.StarNetwork.computation N compute).answer i.succ s time = none := by
  simp [LongTails.Setups.StarNetwork.computation, hpending, not_le.mpr ht]

lemma computation_complete {Input Output Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (compute : Fin n → Input → Seed → ℕ → Output)
    (i : Fin n) (s : LongTails.Setups.StarNetwork.ComputationState Input Seed)
    (time finish : Time) (input : Input)
    (hpending : s.pending = some (finish, input)) (ht : finish ≤ time) :
    (LongTails.Setups.StarNetwork.computation N compute).answer i.succ s time =
      some (.computed input (compute i input s.seed s.used),
        { s with pending := none, used := s.used + 1 }) := by
  simp [LongTails.Setups.StarNetwork.computation, hpending, ht]

lemma computation_completed_data {Input Output Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (compute : Fin n → Input → Seed → ℕ → Output) (i : Fin n)
    (s next : LongTails.Setups.StarNetwork.ComputationState Input Seed) (time : Time)
    (input : Input) (value : Output)
    (h : (LongTails.Setups.StarNetwork.computation N compute).answer i.succ s time =
      some (.computed input value, next)) :
    ∃ finish, s.pending = some (finish, input) ∧ finish ≤ time ∧
      value = compute i input s.seed s.used ∧ next = { s with pending := none, used := s.used + 1 } := by
  cases hp : s.pending with
  | none => simp [LongTails.Setups.StarNetwork.computation, hp] at h
  | some entry =>
      rcases entry with ⟨finish, input'⟩
      by_cases ht : finish ≤ time
      · have he : (LongTails.Setups.StarNetwork.ComputeReply.computed input' (compute i input' s.seed s.used),
            { s with pending := none, used := s.used + 1 }) =
            (LongTails.Setups.StarNetwork.ComputeReply.computed input value, next) := by
          simpa [LongTails.Setups.StarNetwork.computation, hp, ht] using h
        have hr := congrArg Prod.fst he
        have hi : input' = input := (LongTails.Setups.StarNetwork.ComputeReply.computed.inj hr).1
        have hv := (LongTails.Setups.StarNetwork.ComputeReply.computed.inj hr).2
        subst input'
        exact ⟨finish, rfl, ht, hv.symm, by simpa using (congrArg Prod.snd he).symm⟩
      · simp [LongTails.Setups.StarNetwork.computation, hp, ht] at h

lemma computation_submit_timely {Input Output Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (compute : Fin n → Input → Seed → ℕ → Output) (i : Fin n)
    (s : LongTails.Setups.StarNetwork.ComputationState Input Seed) (time : Time)
    (query : LongTails.Setups.StarNetwork.ComputeQuery Input)
    (hold : ∀ finish input, s.pending = some (finish, input) → time ≤ finish) :
    ∀ finish input, ((LongTails.Setups.StarNetwork.computation N compute).submit i.succ s time query).pending =
      some (finish, input) → time ≤ finish := by
  intro finish input hpending
  cases query with
  | abort => simp [LongTails.Setups.StarNetwork.computation] at hpending
  | evaluate x =>
      cases hs : s.pending with
      | none =>
          have he : (time + N.computeTime i, x) = (finish, input) := by
            simpa [LongTails.Setups.StarNetwork.computation, hs] using hpending
          have hf : time + N.computeTime i = finish := congrArg Prod.fst he
          rw [← hf]
          exact le_add_of_nonneg_right zero_le
      | some value =>
          apply hold finish input
          simpa [LongTails.Setups.StarNetwork.computation, hs] using hpending

lemma communication_submit_timely {Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (s : LongTails.Setups.StarNetwork.CommunicationState n) (time : Time)
    (v : Fin (n + 1)) (query : Fin (n + 1) × List Bool)
    (hold : ∀ source target finish bits, s.messages source target = some (finish, bits) → time ≤ finish) :
    ∀ source target finish bits,
      ((LongTails.Setups.StarNetwork.communication (Seed := Seed) N).submit s time v query).messages source target =
        some (finish, bits) → time ≤ finish := by
  classical
  intro source target finish bits hpending
  unfold LongTails.Setups.StarNetwork.communication at hpending
  dsimp only at hpending
  split_ifs at hpending with hedge
  · cases hbusy : s.messages v query.1 with
    | some old =>
        simp only [hbusy] at hpending
        exact hold source target finish bits hpending
    | none =>
        simp only [hbusy] at hpending
        by_cases hv : source = v
        · subst source
          simp only [Function.update_self] at hpending
          by_cases ht : target = query.1
          · subst target
            simp only [Function.update_self] at hpending
            have hf := congrArg Prod.fst (Option.some.inj hpending)
            dsimp only at hf
            rw [← hf]
            exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
          · exact hold v target finish bits (by simpa only [Function.update_of_ne ht] using hpending)
        · exact hold source target finish bits (by simpa only [Function.update_of_ne hv] using hpending)
  · exact hold source target finish bits hpending

lemma communication_submit_free {Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (s : LongTails.Setups.StarNetwork.CommunicationState n) (time : Time)
    (source target : Fin (n + 1)) (bits : List Bool)
    (hedge : (source = 0 ∧ target ≠ 0) ∨ (source ≠ 0 ∧ target = 0))
    (hfree : s.messages source target = none) :
    (LongTails.Setups.StarNetwork.communication (Seed := Seed) N).submit s time source (target, bits) =
      { s with messages := (Function.update s.messages source (Function.update (s.messages source) target
          (some (time + N.timePerBit * bits.length + N.latency, bits)))) } := by
  simp only [LongTails.Setups.StarNetwork.communication, ite_eq_left hedge, hfree]

lemma computation_answer_pending {Input Output Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (compute : Fin n → Input → Seed → ℕ → Output) (v : Fin (n + 1))
    (s next : LongTails.Setups.StarNetwork.ComputationState Input Seed) (time : Time)
    (reply : LongTails.Setups.StarNetwork.ComputeReply Input Output)
    (h : (LongTails.Setups.StarNetwork.computation N compute).answer v s time = some (reply, next)) :
    next.pending = none ∨ next.pending = s.pending := by
  induction v using Fin.cases with
  | zero => simp [LongTails.Setups.StarNetwork.computation] at h
  | succ i =>
      cases hp : s.pending with
      | none => simp [LongTails.Setups.StarNetwork.computation, hp] at h
      | some value =>
          rcases value with ⟨finish, input⟩
          by_cases ht : finish ≤ time
          · have he : (.computed input (compute i input s.seed s.used),
                { s with pending := none, used := s.used + 1 }) = (reply, next) := by
              simpa [LongTails.Setups.StarNetwork.computation, hp, ht] using h
            have hs := congrArg Prod.snd he
            exact Or.inl (congrArg (fun state => state.pending) hs).symm
          · simp [LongTails.Setups.StarNetwork.computation, hp, ht] at h

lemma communication_answer_pending {Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (s next : LongTails.Setups.StarNetwork.CommunicationState n) (time : Time)
    (v : Fin (n + 1)) (reply : LongTails.Setups.StarNetwork.CommReply n)
    (h : (LongTails.Setups.StarNetwork.communication (Seed := Seed) N).answer s time =
      some ((v, reply), next)) :
    ∀ source target, next.messages source target = none ∨
      next.messages source target = s.messages source target := by
  classical
  let messages := (List.finRange (n + 1)).flatMap fun source =>
    (List.finRange (n + 1)).filterMap fun target =>
      (s.messages source target).map fun (finish, bits) => (finish, source, target, bits)
  cases hm : messages.argmin Prod.fst with
  | none =>
      dsimp only [messages] at hm
      simp [LongTails.Setups.StarNetwork.communication, hm] at h
  | some value =>
      rcases value with ⟨finish, source, target, bits⟩
      dsimp only [messages] at hm
      by_cases ht : finish ≤ time
      · have he : ((target, .received source bits),
            { s with messages := (Function.update s.messages source
              (Function.update (s.messages source) target none)) }) = ((v, reply), next) := by
          simpa [LongTails.Setups.StarNetwork.communication, hm, ht] using h
        have hs := congrArg Prod.snd he
        dsimp only at hs
        intro source' target'
        rw [← hs]
        by_cases hsource : source' = source <;> by_cases htarget : target' = target <;>
          simp [hsource, htarget]
      · simp [LongTails.Setups.StarNetwork.communication, hm, ht] at h

lemma communication_ready {Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (s : LongTails.Setups.StarNetwork.CommunicationState n) (time : Time) :
    ((LongTails.Setups.StarNetwork.communication (Seed := Seed) N).answer s time).isSome ↔
      ∃ source target finish bits,
        s.messages source target = some (finish, bits) ∧ finish ≤ time := by
  classical
  let messages := (List.finRange (n + 1)).flatMap fun source =>
    (List.finRange (n + 1)).filterMap fun target =>
      (s.messages source target).map fun (finish, bits) => (finish, source, target, bits)
  have hm : (∃ item ∈ messages, item.1 ≤ time) ↔
      ∃ source target finish bits, s.messages source target = some (finish, bits) ∧ finish ≤ time := by
    simp only [messages, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff]
    constructor
    · rintro ⟨item, ⟨source, _, target, _, ⟨finish, bits⟩, he, rfl⟩, ht⟩
      exact ⟨source, target, finish, bits, he, ht⟩
    · rintro ⟨source, target, finish, bits, he, ht⟩
      exact ⟨(finish, source, target, bits),
        ⟨source, by simp, target, by simp, (finish, bits), he, rfl⟩, ht⟩
  have ha := (argmin_ready Prod.fst messages time).trans hm
  cases hmin : messages.argmin Prod.fst with
  | none =>
      have hnone : ¬ ∃ source target finish bits,
          s.messages source target = some (finish, bits) ∧ finish ≤ time := by
        simpa [hmin] using ha.symm
      dsimp only [messages] at hmin
      simp [LongTails.Setups.StarNetwork.communication, hmin]
      intro source target finish bits he
      exact lt_of_not_ge (fun ht => hnone ⟨source, target, finish, bits, he, ht⟩)
  | some item =>
      rcases item with ⟨finish, source, target, bits⟩
      have hsome : finish ≤ time ↔ ∃ source target finish bits,
          s.messages source target = some (finish, bits) ∧ finish ≤ time := by
        simpa [hmin] using ha
      dsimp only [messages] at hmin
      rw [← hsome]
      by_cases ht : finish ≤ time <;>
        simp [LongTails.Setups.StarNetwork.communication, hmin, ht]

lemma communication_received_data {Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (s next : LongTails.Setups.StarNetwork.CommunicationState n) (time : Time)
    (source target : Fin (n + 1)) (bits : List Bool)
    (h : (LongTails.Setups.StarNetwork.communication (Seed := Seed) N).answer s time =
      some ((target, .received source bits), next)) :
    ∃ finish, s.messages source target = some (finish, bits) ∧ finish ≤ time ∧
      next = { s with messages := (Function.update s.messages source
        (Function.update (s.messages source) target none)) } := by
  classical
  let messages := (List.finRange (n + 1)).flatMap fun sender =>
    (List.finRange (n + 1)).filterMap fun receiver =>
      (s.messages sender receiver).map fun (finish, payload) => (finish, sender, receiver, payload)
  cases hm : messages.argmin Prod.fst with
  | none =>
      dsimp only [messages] at hm
      simp [LongTails.Setups.StarNetwork.communication, hm] at h
  | some value =>
      rcases value with ⟨finish, sender, receiver, payload⟩
      have hmem := List.argmin_mem hm
      have hstored : s.messages sender receiver = some (finish, payload) := by
        simpa [messages, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff,
          Prod.exists] using hmem
      dsimp only [messages] at hm
      by_cases ht : finish ≤ time
      · have he : ((receiver, .received sender payload),
            { s with messages := (Function.update s.messages sender
              (Function.update (s.messages sender) receiver none)) }) =
            ((target, LongTails.Setups.StarNetwork.CommReply.received source bits), next) := by
          simpa [LongTails.Setups.StarNetwork.communication, hm, ht] using h
        have htarget : receiver = target := congrArg (fun z => z.1.1) he
        have hr := congrArg (fun z => z.1.2) he
        have hsource : sender = source := (LongTails.Setups.StarNetwork.CommReply.received.inj hr).1
        have hbits : payload = bits := (LongTails.Setups.StarNetwork.CommReply.received.inj hr).2
        subst receiver
        subst sender
        subst payload
        exact ⟨finish, hstored, ht, by simpa using (congrArg Prod.snd he).symm⟩
      · simp [LongTails.Setups.StarNetwork.communication, hm, ht] at h

lemma computation_thresholds {Input Output Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (compute : Fin n → Input → Seed → ℕ → Output)
    (v : Fin (n + 1)) (s : LongTails.Setups.StarNetwork.ComputationState Input Seed) :
    ∃ times : Finset Time, ∀ time,
      ((LongTails.Setups.StarNetwork.computation N compute).answer v s time).isSome ↔
        ∃ finish ∈ times, finish ≤ time := by
  classical
  induction v using Fin.cases with
  | zero => exact ⟨∅, fun time => by simp [LongTails.Setups.StarNetwork.computation]⟩
  | succ i =>
      cases hp : s.pending with
      | none => exact ⟨∅, fun time => by simp [computation_ready, hp]⟩
      | some value =>
          rcases value with ⟨finish, input⟩
          exact ⟨{finish}, fun time => by simp [computation_ready, hp]⟩

lemma communication_thresholds {Seed : Type} {n : ℕ}
    (N : LongTails.Setups.StarNetwork.Network n)
    (s : LongTails.Setups.StarNetwork.CommunicationState n) :
    ∃ times : Finset Time, ∀ time,
      ((LongTails.Setups.StarNetwork.communication (Seed := Seed) N).answer s time).isSome ↔
        ∃ finish ∈ times, finish ≤ time := by
  classical
  let times := Finset.univ.biUnion fun source => Finset.univ.biUnion fun target =>
    ((s.messages source target).map Prod.fst).toFinset
  have hp (source target : Fin (n + 1)) (time : Time) :
      (∃ finish ∈ ((s.messages source target).map Prod.fst).toFinset, finish ≤ time) ↔
        ∃ finish bits, s.messages source target = some (finish, bits) ∧ finish ≤ time := by
    cases he : s.messages source target with
    | none => simp only [Option.map_none, Option.toFinset_none, Finset.notMem_empty, false_and, exists_false, reduceCtorEq]
    | some value =>
        rcases value with ⟨finish, bits⟩
        simp only [Option.map_some, Option.toFinset_some, Finset.mem_singleton, Option.some.injEq, Prod.mk.injEq]
        simp
  refine ⟨times, ?_⟩
  intro time
  rw [communication_ready]
  simp only [times, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨source, target, finish, bits, he, ht⟩
    obtain ⟨finish', hf, ht'⟩ := (hp source target time).mpr ⟨finish, bits, he, ht⟩
    exact ⟨finish', ⟨source, target, hf⟩, ht'⟩
  · rintro ⟨finish, ⟨source, target, hf⟩, ht⟩
    obtain ⟨finish', bits, he, ht'⟩ := (hp source target time).mp ⟨finish, hf, ht⟩
    exact ⟨source, target, finish', bits, he, ht'⟩

lemma nextTime_spec {α : Type} (event : Time → Option α) (time limit : Time)
    (hex : ∃ t, IsLeast {t | time ≤ t ∧ t ≤ limit ∧
      (t = limit ∨ (event t).isSome)} t) :
    IsLeast {t | time ≤ t ∧ t ≤ limit ∧ (t = limit ∨ (event t).isSome)}
      (nextTime event time limit) := by
  unfold nextTime
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

lemma nextTime_ge {α : Type} (event : Time → Option α) (time limit : Time) :
    time ≤ nextTime event time limit := by
  classical
  unfold nextTime
  split_ifs with h
  · exact (Classical.choose_spec h).1.1
  · exact le_rfl

lemma nextTime_le {α : Type} (event : Time → Option α) (time limit : Time)
    (h : time ≤ limit) : nextTime event time limit ≤ limit := by
  classical
  unfold nextTime
  split_ifs with hex
  · exact (Classical.choose_spec hex).1.2.1
  · exact h

lemma nextTime_le_event {α : Type} (event : Time → Option α) (time limit ready : Time)
    (hex : ∃ t, IsLeast {t | time ≤ t ∧ t ≤ limit ∧
      (t = limit ∨ (event t).isSome)} t)
    (ht : time ≤ ready) (hl : ready ≤ limit) (hr : (event ready).isSome) :
    nextTime event time limit ≤ ready :=
  (nextTime_spec event time limit hex).2 ⟨ht, hl, Or.inr hr⟩

lemma nextTime_le_ready {α : Type} (event : Time → Option α) (time limit ready : Time)
    (hex : ∃ t, IsLeast {t | time ≤ t ∧ t ≤ limit ∧
      (t = limit ∨ (event t).isSome)} t)
    (ht : time ≤ ready) (hr : (event ready).isSome) :
    nextTime event time limit ≤ ready := by
  by_cases hl : ready ≤ limit
  · exact nextTime_le_event event time limit ready hex ht hl hr
  · exact (nextTime_spec event time limit hex).1.2.1.trans (le_of_not_ge hl)

lemma nextTime_gt {α : Type} (event : Time → Option α) (time limit : Time)
    (hex : ∃ t, IsLeast {t | time ≤ t ∧ t ≤ limit ∧
      (t = limit ∨ (event t).isSome)} t)
    (ht : time < limit) (he : event time = none) :
    time < nextTime event time limit := by
  have hs := nextTime_spec event time limit hex
  apply lt_of_le_of_ne hs.1.1
  intro h
  rcases hs.1.2.2 with hl | hr
  · exact ht.ne (h.trans hl)
  · rw [← h, he] at hr
    simp at hr

lemma nextTime_exists_of_thresholds {α : Type} (event : Time → Option α)
    (times : Finset Time) (time limit : Time) (ht : time ≤ limit)
    (hready : ∀ t, (event t).isSome ↔ ∃ r ∈ times, r ≤ t) :
    ∃ t, IsLeast {t | time ≤ t ∧ t ≤ limit ∧ (t = limit ∨ (event t).isSome)} t := by
  classical
  let candidates := insert limit ((times.image (max time)).filter fun t => t ≤ limit)
  have hne : candidates.Nonempty := ⟨limit, Finset.mem_insert_self _ _⟩
  have hmem : ∀ t ∈ candidates,
      time ≤ t ∧ t ≤ limit ∧ (t = limit ∨ (event t).isSome) := by
    intro t ht'
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · exact ⟨ht, le_rfl, Or.inl rfl⟩
    obtain ⟨ht', hlimit⟩ := Finset.mem_filter.mp ht'
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht'
    exact ⟨le_max_left _ _, hlimit, Or.inr ((hready _).mpr ⟨r, hr, le_max_right _ _⟩)⟩
  refine ⟨candidates.min' hne, hmem _ (Finset.min'_mem _ _), ?_⟩
  intro t ht'
  rcases ht'.2.2 with rfl | hsome
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  · obtain ⟨r, hr, hrt⟩ := (hready t).mp hsome
    have hm : max time r ≤ t := max_le ht'.1 hrt
    have hc : max time r ∈ candidates :=
      Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨r, hr, rfl⟩, hm.trans ht'.2.1⟩)
    exact (Finset.min'_le _ _ hc).trans hm

variable {n : ℕ} {ComputeQuery ComputeReply CommReply Output : Type}
  (O : Oracle ComputeQuery ComputeReply CommReply n)
  (A : Algorithm ComputeQuery ComputeReply CommReply Output n)

lemma oracle_ready (s : OracleState O) (time : Time) :
    (O.answer s time).isSome ↔
      (∃ v, (O.computation.answer v (s.computation v) time).isSome) ∨
        (O.communication.answer s.communication time).isSome := by
  let found := (List.finRange n).findSome? (fun v =>
    (O.computation.answer v (s.computation v) time).map fun (reply, state) =>
      ((v, Event.computed (CommReply := CommReply) reply),
        { s with computation := Function.update s.computation v state }))
  have hf : found.isSome ↔ ∃ v, (O.computation.answer v (s.computation v) time).isSome := by
    simp [found, List.isSome_findSome?]
  change (match found with
    | some result => some result
    | none => (O.communication.answer s.communication time).map fun ((v, reply), state) =>
      ((v, Event.received reply), { s with communication := state })).isSome ↔ _
  cases h : found <;> simp_all

lemma oracle_answer_cases (s next : OracleState O) (time : Time)
    (v : Fin n) (notification : Event ComputeReply CommReply)
    (h : O.answer s time = some ((v, notification), next)) :
    (∃ reply state, notification = .computed reply ∧
      O.computation.answer v (s.computation v) time = some (reply, state) ∧
      next = { s with computation := Function.update s.computation v state }) ∨
    (∃ reply state, notification = .received reply ∧
      O.communication.answer s.communication time = some ((v, reply), state) ∧
      next = { s with communication := state }) := by
  classical
  let search := (List.finRange n).findSome? (fun w =>
    (O.computation.answer w (s.computation w) time).map fun (reply, state) =>
      ((w, Event.computed (CommReply := CommReply) reply),
        { s with computation := Function.update s.computation w state }))
  change (match search with
    | some result => some result
    | none => (O.communication.answer s.communication time).map fun ((w, reply), state) =>
      ((w, Event.received reply), { s with communication := state })) = _ at h
  cases hs : search with
  | none =>
      rw [hs] at h
      obtain ⟨⟨⟨w, reply⟩, state⟩, ha, he⟩ := Option.map_eq_some_iff.mp h
      have hv : w = v := congrArg (fun z => z.1.1) he
      have hn : Event.received reply = notification := congrArg (fun z => z.1.2) he
      have hstate : ({ s with communication := state } : OracleState O) = next := congrArg Prod.snd he
      subst w
      exact Or.inr ⟨reply, state, hn.symm, ha, hstate.symm⟩
  | some result =>
      have he : result = ((v, notification), next) := by simpa only [hs, Option.some.injEq] using h
      obtain ⟨w, _, hw⟩ := List.exists_of_findSome?_eq_some hs
      obtain ⟨⟨reply, state⟩, ha, he'⟩ := Option.map_eq_some_iff.mp hw
      have he'' := he'.trans he
      have hv : w = v := congrArg (fun z => z.1.1) he''
      have hn : Event.computed reply = notification := congrArg (fun z => z.1.2) he''
      have hstate : ({ s with computation := Function.update s.computation w state } : OracleState O) = next :=
        congrArg Prod.snd he''
      subst w
      exact Or.inl ⟨reply, state, hn.symm, ha, hstate.symm⟩

lemma event_ready (c : ExecutionState O A) (time : Time) :
    (event O A c time).isSome ↔ (O.answer c.oracle time).isSome ∨ ∃ v, c.wakeTime v ≤ time := by
  have hw : ((((List.finRange n).rotate c.turn).find? fun v => c.wakeTime v ≤ time).isSome) ↔
      ∃ v, c.wakeTime v ≤ time := by
    simp [List.isSome_find?]
  unfold event
  cases h : O.answer c.oracle time <;> simp_all

lemma event_cases (c : ExecutionState O A) (time : Time) (v : Fin n)
    (notification : Event ComputeReply CommReply) (next : OracleState O)
    (h : event O A c time = some ((v, notification), next)) :
    O.answer c.oracle time = some ((v, notification), next) ∨
      notification = .wake ∧ next = c.oracle ∧ c.wakeTime v ≤ time := by
  unfold event at h
  cases ho : O.answer c.oracle time with
  | some result =>
      have he : result = ((v, notification), next) := by simpa only [ho, Option.some.injEq] using h
      exact Or.inl (congrArg some he)
  | none =>
      rw [ho] at h
      obtain ⟨w, hw, he⟩ := Option.map_eq_some_iff.mp h
      have hv : w = v := congrArg (fun z => z.1.1) he
      have hn : Event.wake = notification := congrArg (fun z => z.1.2) he
      have hstate : c.oracle = next := congrArg Prod.snd he
      have hready : c.wakeTime w ≤ time := by simpa using List.find?_some hw
      subst w
      exact Or.inr ⟨hn.symm, hstate.symm, hready⟩

lemma wake_event (c : ExecutionState O A) (time : Time) (v : Fin n) (next : OracleState O)
    (h : event O A c time = some ((v, .wake), next)) : next = c.oracle ∧ c.wakeTime v ≤ time := by
  rcases event_cases O A c time v .wake next h with ho | ⟨_, hn, ht⟩
  · rcases oracle_answer_cases O c.oracle next time v .wake ho with
      ⟨reply, state, he, _⟩ | ⟨reply, state, he, _⟩ <;> cases he
  · exact ⟨hn, ht⟩

lemma computed_event (c : ExecutionState O A) (time : Time) (v : Fin n)
    (reply : ComputeReply) (next : OracleState O)
    (h : event O A c time = some ((v, .computed reply), next)) :
    ∃ state, O.computation.answer v (c.oracle.computation v) time = some (reply, state) ∧
      next = { c.oracle with computation := Function.update c.oracle.computation v state } := by
  rcases event_cases O A c time v (.computed reply) next h with ho | ⟨he, _⟩
  · rcases oracle_answer_cases O c.oracle next time v (.computed reply) ho with
      ⟨reply', state, he, ha, hn⟩ | ⟨reply', state, he, _⟩
    · cases he
      exact ⟨state, ha, hn⟩
    · cases he
  · cases he

lemma received_event (c : ExecutionState O A) (time : Time) (v : Fin n)
    (reply : CommReply) (next : OracleState O)
    (h : event O A c time = some ((v, .received reply), next)) :
    ∃ state, O.communication.answer c.oracle.communication time = some ((v, reply), state) ∧
      next = { c.oracle with communication := state } := by
  rcases event_cases O A c time v (.received reply) next h with ho | ⟨he, _⟩
  · rcases oracle_answer_cases O c.oracle next time v (.received reply) ho with
      ⟨reply', state, he, _⟩ | ⟨reply', state, he, ha, hn⟩
    · cases he
    · cases he
      exact ⟨state, ha, hn⟩
  · cases he

lemma star_event_thresholds {Input Value Seed Result : Type} [MeasurableSpace Seed] {m : ℕ}
    (N : LongTails.Setups.StarNetwork.Network m)
    (compute : Fin m → Input → Seed → ℕ → Value) (P : MeasureTheory.ProbabilityMeasure Seed)
    (A : Algorithm (LongTails.Setups.StarNetwork.ComputeQuery Input)
      (LongTails.Setups.StarNetwork.ComputeReply Input Value)
      (LongTails.Setups.StarNetwork.CommReply m) Result (m + 1)) :
    let O := LongTails.Setups.StarNetwork.system N compute P
    ∀ c : ExecutionState O A, ∃ times : Finset Time, ∀ time,
      (event O A c time).isSome ↔ ∃ finish ∈ times, finish ≤ time := by
  classical
  intro O c
  choose times htimes using fun v => computation_thresholds N compute v (c.oracle.computation v)
  obtain ⟨comm, hcomm⟩ := communication_thresholds (Seed := Seed) N c.oracle.communication
  refine ⟨(Finset.univ.biUnion times) ∪ comm ∪ (Finset.univ.image c.wakeTime), ?_⟩
  intro time
  rw [event_ready, oracle_ready]
  change ((∃ v, ((LongTails.Setups.StarNetwork.computation N compute).answer v
    (c.oracle.computation v) time).isSome) ∨
    ((LongTails.Setups.StarNetwork.communication (Seed := Seed) N).answer c.oracle.communication time).isSome) ∨
    (∃ v, c.wakeTime v ≤ time) ↔ _
  simp only [htimes, hcomm, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  aesop

lemma star_nextTime_exists {Input Value Seed Result : Type} [MeasurableSpace Seed] {m : ℕ}
    (N : LongTails.Setups.StarNetwork.Network m)
    (compute : Fin m → Input → Seed → ℕ → Value) (P : MeasureTheory.ProbabilityMeasure Seed)
    (A : Algorithm (LongTails.Setups.StarNetwork.ComputeQuery Input)
      (LongTails.Setups.StarNetwork.ComputeReply Input Value)
      (LongTails.Setups.StarNetwork.CommReply m) Result (m + 1)) :
    let O := LongTails.Setups.StarNetwork.system N compute P
    ∀ c : ExecutionState O A, c.time ≤ c.deadline →
      ∃ t, IsLeast {t | c.time ≤ t ∧ t ≤ c.deadline ∧
        (t = c.deadline ∨ (event O A c t).isSome)} t := by
  intro O c hc
  obtain ⟨times, htimes⟩ := star_event_thresholds N compute P A c
  exact nextTime_exists_of_thresholds (event O A c) times c.time c.deadline hc htimes

lemma step_time_mono (c next : ExecutionState O A) (h : step O A c = some next) :
    c.time ≤ next.time := by
  classical
  by_cases hlate : c.deadline < c.time
  · simp [step, hlate] at h
  · simp only [step, ite_eq_right hlate] at h
    cases he : event O A c c.time with
    | some value =>
        rcases value with ⟨⟨v, notification⟩, oracle⟩
        rw [he] at h
        dsimp only at h
        cases ha : (A.query v (A.update v (c.workers v) (A.clock c.time) notification)
            (A.clock c.time)).1 <;>
          simp only [ha, Option.some.injEq] at h <;> subst next <;> exact le_rfl
    | none =>
        simp only [he] at h
        by_cases hdeadline : c.time = c.deadline
        · simp [hdeadline] at h
        · simp only [ite_eq_right hdeadline, Option.some.injEq] at h
          subst next
          exact nextTime_ge _ _ _

lemma step_terminal_iff (c : ExecutionState O A) (hc : c.time ≤ c.deadline) :
    step O A c = none ↔ c.time = c.deadline ∧ event O A c c.time = none := by
  classical
  unfold step
  rw [ite_eq_right (not_lt.mpr hc)]
  cases he : event O A c c.time with
  | none =>
      by_cases ht : c.time = c.deadline <;> simp [ht]
  | some value =>
      rcases value with ⟨⟨v, notification⟩, oracle⟩
      cases hq : A.query v (A.update v (c.workers v) (A.clock c.time) notification) (A.clock c.time) with
      | mk action state => cases action <;> simp [hq]

lemma step_deadline (c next : ExecutionState O A) (h : step O A c = some next) :
    next.deadline = c.deadline := by
  classical
  by_cases hlate : c.deadline < c.time
  · simp [step, hlate] at h
  · simp only [step, ite_eq_right hlate] at h
    cases he : event O A c c.time with
    | none =>
        simp only [he] at h
        by_cases ht : c.time = c.deadline
        · simp [ht] at h
        · simp only [ite_eq_right ht, Option.some.injEq] at h
          exact (congrArg ExecutionState.deadline h).symm
    | some value =>
        rcases value with ⟨⟨v, notification⟩, oracle⟩
        rw [he] at h
        cases hq : A.query v (A.update v (c.workers v) (A.clock c.time) notification) (A.clock c.time) with
        | mk action state =>
            cases action <;> simp only [hq, Option.some.injEq] at h <;>
              exact (congrArg ExecutionState.deadline h).symm

lemma step_event_state (c next : ExecutionState O A) (v : Fin n)
    (notification : Event ComputeReply CommReply) (oracle : OracleState O)
    (action : Action ComputeQuery n) (state : A.State)
    (he : event O A c c.time = some ((v, notification), oracle))
    (hq : A.query v (A.update v (c.workers v) (A.clock c.time) notification) (A.clock c.time) = (action, state))
    (hs : step O A c = some next) :
    next.workers = Function.update c.workers v state ∧
      next.wakeTime = Function.update c.wakeTime v
        (match action with | .advance target => max c.time (A.timer target) | _ => c.time) := by
  classical
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · simp only [ite_eq_right hlate, he, hq] at hs
    cases action <;> simp only [Function.update_idem, Option.some.injEq] at hs <;> subst next <;>
      exact ⟨rfl, rfl⟩

lemma step_time_le_deadline (c next : ExecutionState O A) (hc : c.time ≤ c.deadline)
    (h : step O A c = some next) : next.time ≤ next.deadline := by
  classical
  simp only [step, ite_eq_right (not_lt.mpr hc)] at h
  cases he : event O A c c.time with
  | none =>
      simp only [he] at h
      by_cases ht : c.time = c.deadline
      · simp only [ite_eq_left ht, reduceCtorEq] at h
      · simp only [ite_eq_right ht, Option.some.injEq] at h
        subst next
        exact nextTime_le _ _ _ hc
  | some value =>
      rcases value with ⟨⟨v, notification⟩, oracle⟩
      rw [he] at h
      cases hq : A.query v (A.update v (c.workers v) (A.clock c.time) notification) (A.clock c.time) with
      | mk action state =>
          cases action <;> simp only [hq, Option.some.injEq] at h <;> subst next <;> exact hc

lemma run_deadline (c : ExecutionState O A) (k : ℕ) : (run O A k c).deadline = c.deadline := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
      cases hs : step O A c with
      | none => simp only [run, hs]
      | some next =>
          simpa only [run, hs, step_deadline O A c next hs] using ih next

lemma run_time_le_deadline (c : ExecutionState O A) (k : ℕ) (hc : c.time ≤ c.deadline) :
    (run O A k c).time ≤ (run O A k c).deadline := by
  induction k generalizing c with
  | zero => exact hc
  | succ k ih =>
      cases hs : step O A c with
      | none => simpa only [run, hs] using hc
      | some next =>
          simpa only [run, hs] using ih next (step_time_le_deadline O A c next hc hs)

lemma run_terminal (c : ExecutionState O A) (h : step O A c = none) (k : ℕ) :
    run O A k c = c := by
  cases k with
  | zero => simp [run]
  | succ k => simp [run, h]

lemma run_add (m k : ℕ) (c : ExecutionState O A) :
    run O A (m + k) c = run O A k (run O A m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
      cases h : step O A c with
      | none => simp [Nat.succ_add, run, h, run_terminal O A c h]
      | some next => simpa [Nat.succ_add, run, h] using ih next

lemma terminal_run_eq (c : ExecutionState O A) (m k : ℕ)
    (h : step O A (run O A m c) = none) (hmk : m ≤ k) :
    run O A k c = run O A m c := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
  rw [run_add]
  exact run_terminal O A _ h _

lemma execute_eq_terminal (T : Time) (seed : A.Seed × O.Seed) (k : ℕ)
    (h : step O A (run O A k (initial O A T seed)) = none) :
    execute O A T seed.1 seed.2 =
      A.output ((run O A k (initial O A T seed)).workers A.root) := by
  classical
  have hex : ∃ j, step O A (run O A j (initial O A T seed)) = none := ⟨k, h⟩
  have heq := terminal_run_eq O A (initial O A T seed) (Nat.find hex) k
    (Nat.find_spec hex) (Nat.find_min' hex h)
  unfold execute
  dsimp only
  rw [dite_eq_left hex]
  exact congrArg (fun c : ExecutionState O A => A.output (c.workers A.root)) heq.symm

lemma termination_of_rank (Inv : ExecutionState O A → Prop)
    (rank : ExecutionState O A → ℕ)
    (hnext : ∀ c next, Inv c → step O A c = some next → Inv next ∧ rank next < rank c)
    (c : ExecutionState O A) (hc : Inv c) :
    ∃ k, step O A (run O A k c) = none := by
  have hterminate : ∀ r, ∀ c : ExecutionState O A, rank c = r → Inv c →
      ∃ k, step O A (run O A k c) = none := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro c hr hc
        cases hs : step O A c with
        | none => exact ⟨0, hs⟩
        | some next =>
            obtain ⟨hn, hlt⟩ := hnext c next hc hs
            obtain ⟨k, hk⟩ := ih (rank next) (by simpa [hr] using hlt) next rfl hn
            exact ⟨k + 1, by simpa [run, hs] using hk⟩
  exact hterminate (rank c) c rfl hc

end LongTails.Proofs.DistributedExecution
