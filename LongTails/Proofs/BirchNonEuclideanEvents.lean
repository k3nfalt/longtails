import LongTails.Algorithms.BirchNonEuclideanEvents
import LongTails.Proofs.BirchNonEuclideanScheduling
import LongTails.Proofs.BirchNonEuclideanUnused

namespace LongTails.Proofs.BirchNonEuclideanEvents

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanScheduling

lemma eventFold_invariant {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m)
    (P : EventState m → Prop)
    (hstep : ∀ s e, P s → e.Enabled H K word s → P (eventStep K R s e))
    (s : EventState m) (events : List (Event m))
    (hs : P s) (he : LongTails.Algorithms.BirchNonEuclideanEvents.LegalFrom H K R word s events) :
    P (events.foldl (eventStep K R) s) := by
  induction events generalizing s with
  | nil => exact hs
  | cons e events ih => exact ih _ (hstep s e hs he.1) he.2

lemma eventStep_schedule {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m)
    (s : EventState m) (e : Event m) (hs : s.schedule = scheduleRun K R word s.cursor)
    (he : e.Enabled H K word s) :
    (eventStep K R s e).schedule = scheduleRun K R word (eventStep K R s e).cursor := by
  cases e with
  | query w => exact hs
  | complete w =>
      by_cases ha : s.schedule.accepted.length < K
      · have hw := he.2.2 ha
        simp only [eventStep, ha, ite_true]
        rw [hw, hs, scheduleRun]
      · simpa only [eventStep, ha, ite_false] using hs

lemma eventRun_schedule {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (he : LongTails.Algorithms.BirchNonEuclideanEvents.LegalFrom H K R word {} events) :
    (eventRun K R events).schedule = scheduleRun K R word (eventRun K R events).cursor :=
  eventFold_invariant H K R word (fun s => s.schedule = scheduleRun K R word s.cursor)
    (eventStep_schedule H K R word) {} events rfl he

lemma eventStep_progress {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m)
    (s : EventState m) (e : Event m) (hs : ∀ w, s.progress w ≤ H)
    (he : e.Enabled H K word s) : ∀ w, (eventStep K R s e).progress w ≤ H := by
  cases e with
  | query v =>
      intro w
      change Function.update s.progress v (s.progress v + 1) w ≤ H
      by_cases hw : w = v
      · subst w
        rw [Function.update_self]
        exact Nat.succ_le_of_lt he.2
      · rw [Function.update_of_ne hw]
        exact hs w
  | complete v =>
      intro w
      by_cases ha : s.schedule.accepted.length < K
      · simp only [eventStep, ha, ite_true]
        split_ifs with hb
        · by_cases hw : w = v
          · subst w
            simp
          · rw [Function.update_of_ne hw]
            exact hs w
        · exact hs w
      · simpa only [eventStep, ha, ite_false] using hs w

lemma eventRun_progress {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (he : LongTails.Algorithms.BirchNonEuclideanEvents.LegalFrom H K R word {} events) :
    ∀ w, (eventRun K R events).progress w ≤ H :=
  eventFold_invariant H K R word (fun s => ∀ w, s.progress w ≤ H)
    (eventStep_progress H K R word) {} events (fun _ => Nat.zero_le _) he

def eventQueries {m : ℕ} : Event m → ℕ
  | .query _ => 1
  | .complete _ => 0

lemma eventStep_query_length {m : ℕ} (K R : ℕ) (s : EventState m) (e : Event m) :
    (eventStep K R s e).queries.length = s.queries.length + eventQueries e := by
  cases e with
  | query w => simp [eventStep, eventQueries]
  | complete w => by_cases h : s.schedule.accepted.length < K <;> simp [eventStep, h, eventQueries]

lemma eventFold_query_length {m : ℕ} (K R : ℕ) (s : EventState m) (events : List (Event m)) :
    (events.foldl (eventStep K R) s).queries.length = s.queries.length + (events.map eventQueries).sum := by
  induction events generalizing s with
  | nil => simp
  | cons e events ih =>
      rw [List.foldl_cons, ih, eventStep_query_length]
      simp [Nat.add_assoc]

lemma queryLabels_length {m : ℕ} (H K B : ℕ) (events : List (Event m)) :
    (queryLabels H K B events).length = B + (events.map eventQueries).sum := by
  simp only [queryLabels, List.length_append, List.length_map, List.length_range, eventRun,
    eventFold_query_length]
  simp

lemma privateStep_eq (w x v H h : ℕ) : privateStep w x v H h = momentumStep w H 0 h (x, v) := by
  simp only [privateStep, momentumStep, zero_mul, zero_add]

lemma privateStep_calls (w x v H h : ℕ) (s : CodeState) :
    codeCalls (privateStep w x v H h s).2 = codeCalls s + 1 := by
  rw [privateStep_eq]
  exact momentumStep_calls w H 0 h (x, v) s

def QueryPast {m : ℕ} (s : EventState m) : Prop :=
  ∀ w c h, Sum.inr (w, c, h) ∈ s.queries →
    c < s.schedule.serial w ∨ c = s.schedule.serial w ∧ h < s.progress w

lemma scheduleStep_serial {m : ℕ} (K R : ℕ) (w : Fin m) (s : PacketSchedule m)
    (ha : s.accepted.length < K) :
    (scheduleStep K R w s).serial = Function.update s.serial w (s.serial w + 1) := by
  simp only [scheduleStep, ha, ite_true]
  split_ifs <;> rfl

lemma eventStep_queryPast {m : ℕ} (K R : ℕ) (s : EventState m) (e : Event m) (hs : QueryPast s) :
    QueryPast (eventStep K R s e) := by
  cases e with
  | query v =>
      intro w c h hmem
      change Sum.inr (w, c, h) ∈ s.queries ++ [Sum.inr (v, s.schedule.serial v, s.progress v)] at hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · have hp := hs w c h hold
        change c < s.schedule.serial w ∨
          c = s.schedule.serial w ∧ h < Function.update s.progress v (s.progress v + 1) w
        by_cases hw : w = v
        · subst w
          rw [Function.update_self]
          rcases hp with hp | ⟨hc, hh⟩
          · exact Or.inl hp
          · exact Or.inr ⟨hc, by omega⟩
        · simpa only [Function.update_of_ne hw] using hp
      · have heq := List.mem_singleton.mp hnew
        cases heq
        change s.schedule.serial v < s.schedule.serial v ∨
          s.schedule.serial v = s.schedule.serial v ∧
            s.progress v < Function.update s.progress v (s.progress v + 1) v
        simp
  | complete v =>
      by_cases ha : s.schedule.accepted.length < K
      · intro w c h hmem
        have hp : c < s.schedule.serial w ∨ c = s.schedule.serial w ∧ h < s.progress w := by
          apply hs w c h
          simpa only [eventStep, ha, ite_true] using hmem
        simp only [eventStep, ha, ite_true, scheduleStep_serial K R v s.schedule ha]
        by_cases hw : w = v
        · subst w
          rw [Function.update_self]
          left
          rcases hp with hp | ⟨hp, _⟩ <;> omega
        · rw [Function.update_of_ne hw]
          split_ifs <;> simpa only [Function.update_of_ne hw] using hp
      · simpa only [eventStep, ha, ite_false, QueryPast] using hs

lemma eventStep_queries_nodup {m : ℕ} (K R : ℕ) (s : EventState m) (e : Event m)
    (hp : QueryPast s) (hn : s.queries.Nodup) : (eventStep K R s e).queries.Nodup := by
  cases e with
  | query w =>
      have hf : Sum.inr (w, s.schedule.serial w, s.progress w) ∉ s.queries := by
        intro hmem
        have hh := hp w _ _ hmem
        omega
      change (s.queries ++ [Sum.inr (w, s.schedule.serial w, s.progress w)]).Nodup
      refine List.nodup_append.mpr ⟨hn, by simp, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst b
      exact hf (hab ▸ ha)
  | complete w => by_cases ha : s.schedule.accepted.length < K <;> simpa [eventStep, ha] using hn

lemma eventRun_queries_nodup {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (he : LongTails.Algorithms.BirchNonEuclideanEvents.LegalFrom H K R word {} events) :
    (eventRun K R events).queries.Nodup := by
  have hi : QueryPast ({} : EventState m) ∧ ([] : List (QueryLabel m)).Nodup := by
    constructor
    · intro w c h hh
      cases hh
    · exact List.nodup_nil
  have hh := eventFold_invariant H K R word (fun s => QueryPast s ∧ s.queries.Nodup)
    (fun s e hs _ => ⟨eventStep_queryPast K R s e hs.1, eventStep_queries_nodup K R s e hs.1 hs.2⟩)
    {} events hi he
  exact hh.2

lemma eventCode_public {m : ℕ} (H K R : ℕ) (e : Event m) (state : EventState m × Registers m)
    (s : CodeState) : (eventCode H K R e state s).1.1 = eventStep K R state.1 e := by
  cases e <;> simp only [eventCode, returnCode, commitCode, relaunchCode, state_bind_apply, state_pure_apply]
  split_ifs <;> rfl

lemma state_map_apply {α β : Type} (f : α → β) (act : StateM CodeState α) (s : CodeState) :
    (f <$> act) s = (f (act s).1, (act s).2) := rfl

lemma eventCode_calls {m : ℕ} (H K R : ℕ) (e : Event m) (state : EventState m × Registers m)
    (s : CodeState) : codeCalls (eventCode H K R e state s).2 = codeCalls s + eventQueries e := by
  cases e with
  | query w => exact privateStep_calls _ _ _ _ _ s
  | complete w =>
      simp only [eventCode, returnCode, commitCode, relaunchCode, state_bind_apply]
      split_ifs <;>
        simp [state_bind_apply, state_pure_apply, state_map_apply, emit_apply, codeCalls,
          InstructionTemplate.instantiate, Instruction.oracleCost, eventQueries]

lemma state_forIn_weighted_cost {σ α β : Type} (cost : σ → ℕ)
    (step : α → β → StateM σ β) (c : α → ℕ)
    (hc : ∀ i b s, cost (step i b s).2 = cost s + c i) (xs : List α) (b : β) (s : σ) :
    cost ((forIn xs b (fun i b => ForInStep.yield <$> step i b) : StateM σ β) s).2 =
      cost s + (xs.map c).sum := by
  induction xs generalizing b s with
  | nil => simp only [List.forIn_nil, List.map_nil, List.sum_nil, Nat.add_zero]; rfl
  | cons i xs ih =>
      rw [state_forIn_cons, ih, hc]
      simp [Nat.add_assoc]

lemma launchCode_calls (w x v : ℕ) (s : CodeState) : codeCalls (launchCode w x v s).2 = codeCalls s := by
  simp [launchCode, state_bind_apply, state_map_apply, emit_apply, codeCalls,
    InstructionTemplate.instantiate, Instruction.oracleCost]

lemma eventsCode_run {m : ℕ} (H K B : ℕ) (events : List (Event m)) (s : CodeState) :
    (eventsCode H K B events).run s =
      let initial := (localBatch 0 0 B).run s
      let sent := (forIn (List.finRange m) () (fun w _ => ForInStep.yield <$>
        launchCode (w.val + 1) 0 initial.1) : StateM CodeState Unit) initial.2
      let regs : Registers m := ⟨fun _ => 0, fun _ => initial.1, fun _ => 0,
        fun _ => initial.1, fun _ => 0, fun _ => initial.1⟩
      let out := (forIn events (({} : EventState m), regs)
        (fun e state => ForInStep.yield <$> eventCode H K (packetCutoff H B) e state) :
          StateM CodeState (EventState m × Registers m)) sent.2
      (out.1.2.points, out.2) := rfl

lemma eventsCode_calls {m : ℕ} (H K B : ℕ) (events : List (Event m)) (s : CodeState) :
    codeCalls ((eventsCode H K B events).run s).2 = codeCalls s + B + (events.map eventQueries).sum := by
  rw [eventsCode_run]
  dsimp only
  rw [state_forIn_weighted_cost codeCalls _ eventQueries (eventCode_calls H K (packetCutoff H B))]
  rw [state_forIn_cost codeCalls _ 0 (fun w _ s => by simpa using launchCode_calls (w.val + 1) 0 _ s)]
  rw [localBatch_calls]
  simp

lemma eventsProgram_calls {m : ℕ} (H K B : ℕ) (events : List (Event m)) (t : Tuning) :
    (eventsProgram H K B events t).oracleCalls = (queryLabels H K B events).length := by
  rw [eventsProgram, template_tuning_oracleCalls _ t (canonicalTuning 0 1), queryLabels_length]
  change codeCalls ((eventsCode H K B events).run {}).2 = _
  rw [eventsCode_calls]
  simp [codeCalls]

lemma eventFold_no_initial {m : ℕ} (K R : ℕ) (events : List (Event m)) (s : EventState m)
    (hs : ∀ b, Sum.inl b ∉ s.queries) :
    ∀ b, Sum.inl b ∉ (events.foldl (eventStep K R) s).queries := by
  induction events generalizing s with
  | nil => exact hs
  | cons e events ih =>
      apply ih
      intro b
      cases e with
      | query w => simpa [eventStep] using hs b
      | complete w => by_cases ha : s.schedule.accepted.length < K <;> simpa [eventStep, ha] using hs b

lemma queryLabels_nodup {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (he : LongTails.Algorithms.BirchNonEuclideanEvents.LegalFrom H K (packetCutoff H B) word {} events) :
    (queryLabels H K B events).Nodup := by
  refine List.nodup_append.mpr ⟨?_, eventRun_queries_nodup H K (packetCutoff H B) word events he, ?_⟩
  · exact (List.nodup_range (n := B)).map Sum.inl_injective
  · intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    subst b
    exact eventFold_no_initial K (packetCutoff H B) events {} (by simp) i hb

end LongTails.Proofs.BirchNonEuclideanEvents
