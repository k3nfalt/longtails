import LongTails.Proofs.BirchNonEuclideanEvents

namespace LongTails.Proofs.BirchNonEuclideanEventCosts

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Proofs.BirchNonEuclideanScheduling
open LongTails.Proofs.BirchNonEuclideanEvents

def LiveBalance {m : ℕ} (K : ℕ) (s : EventState m) : Prop :=
  s.live.card + s.drained.length = if s.schedule.accepted.length < K then m else m - 1

lemma eventStep_liveBalance {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m)
    (s : EventState m) (e : Event m) (hs : LiveBalance K s) (he : e.Enabled H K word s) :
    LiveBalance K (eventStep K R s e) := by
  cases e with
  | query w => exact hs
  | complete w =>
      have hc := Finset.card_erase_add_one he.1
      by_cases ha : s.schedule.accepted.length < K
      · have hb : s.live.card + s.drained.length = m := by simpa only [LiveBalance, ha, ite_true] using hs
        simp only [LiveBalance, eventStep, ha, ite_true]
        split_ifs <;> omega
      · have hb : s.live.card + s.drained.length = m - 1 := by
          simpa only [LiveBalance, ha, ite_false] using hs
        simp only [LiveBalance, eventStep, ha, ite_false, List.length_append, List.length_singleton]
        omega

lemma eventRun_liveBalance {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (hK : 0 < K)
    (he : LongTails.Algorithms.BirchNonEuclideanEvents.LegalFrom H K R word {} events) :
    LiveBalance K (eventRun K R events) := by
  apply eventFold_invariant H K R word (LiveBalance K) (eventStep_liveBalance H K R word) {} events _ he
  simp [LiveBalance, hK]

def work {m : ℕ} (H : ℕ) (s : EventState m) : ℕ :=
  H * (s.schedule.completed.length + s.drained.length) + ∑ w ∈ s.live, s.progress w

lemma sum_update_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (i : ι)
    (hi : i ∈ s) (v : ℕ) : ∑ j ∈ s, Function.update f i v j = (∑ j ∈ s.erase i, f j) + v := by
  rw [Finset.sum_update_of_mem hi, Finset.sdiff_singleton_eq_erase]
  omega

lemma scheduleStep_completed_length {m : ℕ} (K R : ℕ) (w : Fin m) (s : PacketSchedule m)
    (ha : s.accepted.length < K) :
    (scheduleStep K R w s).completed.length = s.completed.length + 1 := by
  simp only [scheduleStep, ha, ite_true]
  split_ifs <;> simp

lemma eventStep_work {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m)
    (s : EventState m) (e : Event m) (he : e.Enabled H K word s) :
    work H (eventStep K R s e) = work H s + eventQueries e := by
  cases e with
  | query w =>
      have hsum := Finset.sum_erase_add s.live s.progress he.1
      simp only [work, eventStep, eventQueries]
      rw [sum_update_nat _ _ _ he.1]
      omega
  | complete w =>
      have hsum := Finset.sum_erase_add s.live s.progress he.1
      rw [he.2.1] at hsum
      by_cases ha : s.schedule.accepted.length < K
      · simp only [work, eventStep, eventQueries, ha, ite_true,
          scheduleStep_completed_length K R w s.schedule ha]
        split_ifs
        · rw [sum_update_nat _ _ _ he.1]
          nlinarith
        · nlinarith
      · simp only [work, eventStep, eventQueries, ha, ite_false, List.length_append, List.length_singleton]
        nlinarith

lemma eventRun_work {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (he : LongTails.Algorithms.BirchNonEuclideanEvents.LegalFrom H K R word {} events) :
    (eventRun K R events).queries.length = work H (eventRun K R events) := by
  apply eventFold_invariant H K R word (fun s => s.queries.length = work H s) _ {} events _ he
  · intro s e hs he
    rw [eventStep_query_length, eventStep_work H K R word s e he, hs]
  · simp [work]

lemma scheduleRun_stable {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n t : ℕ)
    (hn : (scheduleRun K R word n).accepted.length = K) :
    scheduleRun K R word (n + t) = scheduleRun K R word n := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.add_succ, scheduleRun, ih]
      simp [scheduleStep, hn]

lemma scheduleRun_stopped_unique {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n j : ℕ)
    (hn : (scheduleRun K R word n).accepted.length = K)
    (hj : (scheduleRun K R word j).accepted.length = K) :
    scheduleRun K R word n = scheduleRun K R word j := by
  rcases le_total n j with h | h
  · have hh := scheduleRun_stable K R word n (j - n) hn
    rw [Nat.add_sub_of_le h] at hh
    exact hh.symm
  · have hh := scheduleRun_stable K R word j (n - j) hj
    rw [Nat.add_sub_of_le h] at hh
    exact hh

lemma completeTrace_schedule {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (hK : 0 < K) (hm : 0 < m) (he : CompleteTrace H K B word events) :
    (eventRun K (packetCutoff H B) events).schedule = finalSchedule H K B word := by
  have hp := eventRun_schedule H K (packetCutoff H B) word events he.1
  rw [hp]
  apply scheduleRun_stopped_unique
  · rw [← hp]
    exact he.2.1
  · exact scheduleRun_stopped K (packetCutoff H B) word hK hm

lemma completeTrace_query_count {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (hK : 0 < K) (hm : 0 < m) (he : CompleteTrace H K B word events) :
    (queryLabels H K B events).length =
      B + H * (K + (finalSchedule H K B word).rejected.length + (m - 1)) := by
  let s := eventRun K (packetCutoff H B) events
  have hs := completeTrace_schedule H K B word events hK hm he
  have hb := eventRun_liveBalance H K (packetCutoff H B) word events hK he.1
  have hd : s.drained.length = m - 1 := by
    simpa only [LiveBalance, he.2.1, lt_self_iff_false, ite_false, he.2.2, Finset.card_empty, zero_add] using hb
  have hc := (scheduleRun_invariant K (packetCutoff H B) word
    (completionLimit m K (packetCutoff H B))).2.2.2
  change (finalSchedule H K B word).completed.length =
    (finalSchedule H K B word).accepted.length + (finalSchedule H K B word).rejected.length at hc
  rw [← hs, he.2.1] at hc
  simp only [queryLabels, List.length_append, List.length_map, List.length_range]
  rw [eventRun_work H K (packetCutoff H B) word events he.1]
  unfold work
  rw [he.2.2, Finset.sum_empty, Nat.add_zero, hc, hd]
  rw [hs]

lemma completeTrace_calls {m : ℕ} (H K B : ℕ) (word : ℕ → ℕ → ℕ → Fin m)
    (events : List (Event m)) (t : Tuning) (hK : 0 < K) (hm : 0 < m)
    (he : CompleteTrace H K B (word K B) events) :
    (eventsProgram H K B events t).oracleCalls = physicalLocalCalls H word K B := by
  rw [eventsProgram_calls, completeTrace_query_count H K B (word K B) events hK hm he,
    physicalLocalCalls, ignored_length H K B (word K B) hK hm]
  congr 2
  omega

end LongTails.Proofs.BirchNonEuclideanEventCosts
