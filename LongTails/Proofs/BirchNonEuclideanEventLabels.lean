import LongTails.Proofs.BirchNonEuclideanEventCosts
import Mathlib.Data.List.Perm.Subperm

namespace LongTails.Proofs.BirchNonEuclideanEventLabels

open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Proofs.BirchNonEuclideanScheduling
open LongTails.Proofs.BirchNonEuclideanEvents
open LongTails.Proofs.BirchNonEuclideanEventCosts

lemma scheduleStep_last {m : ℕ} (K R : ℕ) (w : Fin m) (s : PacketSchedule m)
    (ha : s.accepted.length < K) : (scheduleStep K R w s).last = some w := by
  simp only [scheduleStep, ha, ite_true]
  split_ifs <;> rfl

def SerialCoverage {m : ℕ} (s : PacketSchedule m) : Prop :=
  ∀ w c, c < s.serial w → ∃ job ∈ s.completed, job.worker = w ∧ job.serial = c

lemma scheduleStep_serialCoverage {m : ℕ} (K R : ℕ) (w : Fin m) (s : PacketSchedule m)
    (hs : SerialCoverage s) : SerialCoverage (scheduleStep K R w s) := by
  by_cases ha : s.accepted.length < K
  · have hc : (scheduleStep K R w s).completed =
        s.completed ++ [⟨w, s.source w, s.serial w⟩] := by
      simp only [scheduleStep, ha, ite_true]
      split_ifs <;> rfl
    intro v c hh
    rw [scheduleStep_serial K R w s ha] at hh
    by_cases hv : v = w
    · subst v
      rw [Function.update_self] at hh
      by_cases hold : c < s.serial w
      · obtain ⟨job, hj, hw, hs⟩ := hs w c hold
        exact ⟨job, by rw [hc]; exact List.mem_append_left _ hj, hw, hs⟩
      · have heq : c = s.serial w := by omega
        exact ⟨⟨w, s.source w, s.serial w⟩, by rw [hc]; simp, rfl, heq.symm⟩
    · rw [Function.update_of_ne hv] at hh
      obtain ⟨job, hj, hw, hs⟩ := hs v c hh
      exact ⟨job, by rw [hc]; exact List.mem_append_left _ hj, hw, hs⟩
  · simpa only [scheduleStep, ha, ite_false] using hs

lemma scheduleRun_serialCoverage {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ) :
    SerialCoverage (scheduleRun K R word n) := by
  induction n with
  | zero => simp [scheduleRun, SerialCoverage]
  | succ n ih => exact scheduleStep_serialCoverage K R (word n) _ ih

lemma scheduleRun_completed_mem {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ) (job : Packet m) :
    job ∈ (scheduleRun K R word n).completed ↔
      job ∈ (scheduleRun K R word n).accepted ∨ job ∈ (scheduleRun K R word n).rejected := by
  induction n with
  | zero => simp [scheduleRun]
  | succ n ih =>
      simp only [scheduleRun, scheduleStep]
      split_ifs <;> (try simp only [List.mem_append, List.mem_singleton])
      all_goals tauto

def LiveAllowed {m : ℕ} (K : ℕ) (s : EventState m) : Prop :=
  ∀ w ∈ s.live, s.schedule.accepted.length < K ∨ some w ≠ s.schedule.last

def QueryCovered {m : ℕ} (H K : ℕ) (s : EventState m) : Prop :=
  ∀ w c h, Sum.inr (w, c, h) ∈ s.queries → h < H ∧
    (c < s.schedule.serial w ∨ c = s.schedule.serial w ∧
      (s.schedule.accepted.length < K ∨ some w ≠ s.schedule.last))

lemma eventStep_liveAllowed {m : ℕ} (K R : ℕ)
    (s : EventState m) (e : Event m) (hs : LiveAllowed K s) :
    LiveAllowed K (eventStep K R s e) := by
  cases e with
  | query w => exact hs
  | complete w =>
      by_cases ha : s.schedule.accepted.length < K
      · simp only [LiveAllowed, eventStep, ha, ite_true]
        split_ifs with hb
        · exact fun _ _ => Or.inl hb
        · intro v hv
          right
          rw [scheduleStep_last K R w s.schedule ha]
          simpa only [ne_eq, Option.some.injEq] using (Finset.mem_erase.mp hv).1
      · simp only [LiveAllowed, eventStep, ha, ite_false]
        intro v hv
        exact Or.inr ((hs v (Finset.mem_erase.mp hv).2).resolve_left ha)

lemma eventStep_queryCovered {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m)
    (s : EventState m) (e : Event m) (hs : QueryCovered H K s) (hl : LiveAllowed K s)
    (he : e.Enabled H K word s) : QueryCovered H K (eventStep K R s e) := by
  cases e with
  | query v =>
      intro w c h hh
      change Sum.inr (w, c, h) ∈ s.queries ++ [Sum.inr (v, s.schedule.serial v, s.progress v)] at hh
      rcases List.mem_append.mp hh with hold | hnew
      · exact hs w c h hold
      · have hq := List.mem_singleton.mp hnew
        cases hq
        exact ⟨he.2, Or.inr ⟨rfl, hl v he.1⟩⟩
  | complete v =>
      by_cases ha : s.schedule.accepted.length < K
      · intro w c h hh
        have hp := hs w c h (by simpa only [eventStep, ha, ite_true] using hh)
        refine ⟨hp.1, ?_⟩
        simp only [eventStep, ha, ite_true, scheduleStep_serial K R v s.schedule ha,
          scheduleStep_last K R v s.schedule ha]
        by_cases hw : w = v
        · subst w
          rw [Function.update_self]
          left
          rcases hp.2 with h | ⟨h, _⟩ <;> omega
        · rw [Function.update_of_ne hw]
          rcases hp.2 with h | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, Or.inr (by simpa using hw)⟩
      · simpa only [QueryCovered, eventStep, ha, ite_false] using hs

lemma eventRun_queryCovered {m : ℕ} (H K R : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (hK : 0 < K)
    (he : LongTails.Algorithms.BirchNonEuclideanEvents.LegalFrom H K R word {} events) :
    QueryCovered H K (eventRun K R events) := by
  have hi : LiveAllowed K ({} : EventState m) ∧ QueryCovered H K ({} : EventState m) := by
    constructor
    · intro w _
      exact Or.inl hK
    · intro w c h hh
      cases hh
  exact (eventFold_invariant H K R word (fun s => LiveAllowed K s ∧ QueryCovered H K s)
    (fun s e hs he => ⟨eventStep_liveAllowed K R s e hs.1,
      eventStep_queryCovered H K R word s e hs.2 hs.1 he⟩) {} events hi he).2

lemma pending_mem {m : ℕ} (s : PacketSchedule m) (w : Fin m) (hw : some w ≠ s.last) :
    (⟨w, s.source w, s.serial w⟩ : Packet m) ∈ pending s := by
  apply List.mem_map.mpr
  refine ⟨w, ?_, rfl⟩
  simp [hw]

lemma packetLabels_mem {m : ℕ} (H : ℕ) (job : Packet m) (h : ℕ) (hh : h < H) :
    Sum.inr (job.worker, job.serial, h) ∈ packetLabels H job := by
  exact List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩

lemma completeTrace_labels_subset {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (hK : 0 < K) (hm : 0 < m) (he : CompleteTrace H K B word events) :
    queryLabels H K B events ⊆ normalLabels H K B word := by
  let s := finalSchedule H K B word
  have hs := completeTrace_schedule H K B word events hK hm he
  have hc := eventRun_queryCovered H K (packetCutoff H B) word events hK he.1
  have hp := scheduleRun_serialCoverage K (packetCutoff H B) word (completionLimit m K (packetCutoff H B))
  change SerialCoverage s at hp
  intro q hq
  rcases List.mem_append.mp hq with hinitial | hworker
  · exact List.mem_append_left _ hinitial
  · apply List.mem_append_right
    cases q with
    | inl b => exact False.elim (eventFold_no_initial K (packetCutoff H B) events {} (by simp) b hworker)
    | inr label =>
        rcases label with ⟨w, c, h⟩
        obtain ⟨hh, hj⟩ := hc w c h hworker
        rw [hs] at hj
        change c < s.serial w ∨ c = s.serial w ∧ (s.accepted.length < K ∨ some w ≠ s.last) at hj
        apply List.mem_flatMap.mpr
        rcases hj with hold | ⟨hserial, hlast⟩
        · obtain ⟨job, hjob, hw, hc⟩ := hp w c hold
          refine ⟨job, ?_, ?_⟩
          · have hd := (scheduleRun_completed_mem K (packetCutoff H B) word
              (completionLimit m K (packetCutoff H B)) job).mp hjob
            rcases hd with hd | hd
            · exact List.mem_append_left _ hd
            · exact List.mem_append_right _ (List.mem_append_left _ hd)
          · rw [← hw, ← hc]
            exact packetLabels_mem H job h hh
        · have ha : s.accepted.length = K := scheduleRun_stopped K (packetCutoff H B) word hK hm
          have hl : some w ≠ s.last := hlast.resolve_left (by omega)
          refine ⟨⟨w, s.source w, s.serial w⟩, ?_, ?_⟩
          · exact List.mem_append_right _ (List.mem_append_right _ (pending_mem s w hl))
          · rw [hserial]
            exact packetLabels_mem H _ h hh

lemma packetLabels_length {m : ℕ} (H : ℕ) (job : Packet m) :
    (packetLabels H job).length = H := by simp [packetLabels]

lemma packetsLabels_length {m : ℕ} (H : ℕ) (jobs : List (Packet m)) :
    (jobs.flatMap (packetLabels H)).length = H * jobs.length := by
  induction jobs with
  | nil => simp
  | cons job rest ih =>
      simp only [List.flatMap_cons, List.length_append, packetLabels_length, ih, List.length_cons]
      ring

lemma normalLabels_length {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (hK : 0 < K) (hm : 0 < m) :
    (normalLabels H K B word).length =
      B + H * (K + (finalSchedule H K B word).rejected.length + (m - 1)) := by
  simp only [normalLabels, List.length_append, List.length_map, List.length_range, packetsLabels_length]
  rw [ignored_length H K B word hK hm]
  have hs := scheduleRun_stopped K (packetCutoff H B) word hK hm
  change (finalSchedule H K B word).accepted.length = K at hs
  rw [hs]
  congr 2
  omega

lemma completeTrace_labels_perm {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (hK : 0 < K) (hm : 0 < m) (he : CompleteTrace H K B word events) :
    (queryLabels H K B events).Perm (normalLabels H K B word) := by
  apply ((queryLabels_nodup H K B word events he.1).subperm
    (completeTrace_labels_subset H K B word events hK hm he)).perm_of_length_le
  rw [normalLabels_length H K B word hK hm, completeTrace_query_count H K B word events hK hm he]

def labelIndex {α : Type*} [BEq α] [ReflBEq α] {xs ys : List α} (h : xs.Perm ys) (i : ℕ) : ℕ :=
  if hi : i < ys.length then (h.symm.idxBij ⟨i, hi⟩).val else i

lemma labelIndex_injective {α : Type*} [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs.Perm ys) :
    Function.Injective (labelIndex h) := by
  intro i j heq
  by_cases hi : i < ys.length <;> by_cases hj : j < ys.length
  · simp only [labelIndex, hi, hj, dite_true] at heq
    exact congrArg Fin.val (h.symm.idxBij_injective (Fin.ext heq))
  · simp only [labelIndex, hi, hj, dite_true, dite_false] at heq
    have hb := (h.symm.idxBij ⟨i, hi⟩).isLt
    have hl := h.length_eq
    omega
  · simp only [labelIndex, hi, hj, dite_true, dite_false] at heq
    have hb := (h.symm.idxBij ⟨j, hj⟩).isLt
    have hl := h.length_eq
    omega
  · simpa only [labelIndex, hi, hj, dite_false] using heq

lemma labelIndex_mem {α : Type*} [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs.Perm ys)
    (i : ℕ) (hi : i < ys.length) : labelIndex h i < xs.length := by
  simpa only [labelIndex, hi, dite_true] using (h.symm.idxBij ⟨i, hi⟩).isLt

lemma labelIndex_get {α : Type*} [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs.Perm ys)
    (i : ℕ) (hi : i < ys.length) : xs[labelIndex h i]'(labelIndex_mem h i hi) = ys[i] := by
  simpa only [labelIndex, hi, dite_true] using h.getElem_idxBij_symm_eq_getElem ⟨i, hi⟩

lemma completeTrace_iid {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {samples : ℕ → Ξ → Ω} {mu : MeasureTheory.Measure Ω} {P : MeasureTheory.Measure Ξ}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID samples mu P)
    {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (hK : 0 < K) (hm : 0 < m) (he : CompleteTrace H K B word events) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun i => samples (labelIndex (completeTrace_labels_perm H K B word events hK hm he) i)) mu P := by
  exact LongTails.Proofs.BirchNonEuclideanExecution.iid_reindex h_samples _ (labelIndex_injective _)

lemma completeTrace_initial_fixed {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (events : List (Event m))
    (hK : 0 < K) (hm : 0 < m) (he : CompleteTrace H K B word events) (b : ℕ) (hb : b < B) :
    labelIndex (completeTrace_labels_perm H K B word events hK hm he) b = b := by
  let perm := completeTrace_labels_perm H K B word events hK hm he
  have hbn : b < (normalLabels H K B word).length := by
    simp only [normalLabels, List.length_append, List.length_map, List.length_range]
    omega
  have hbp : b < (queryLabels H K B events).length := by
    simp only [queryLabels, List.length_append, List.length_map, List.length_range]
    omega
  have hbi : b < ((List.range B).map (Sum.inl : ℕ → QueryLabel m)).length := by simpa using hb
  have hn : (normalLabels H K B word)[b] = Sum.inl b := by
    simp only [normalLabels, List.getElem_append_left hbi, List.getElem_map, List.getElem_range]
  have hp : (queryLabels H K B events)[b] = Sum.inl b := by
    simp only [queryLabels, List.getElem_append_left hbi, List.getElem_map, List.getElem_range]
  have hg := labelIndex_get perm b hbn
  rw [hn, ← hp] at hg
  exact (queryLabels_nodup H K B word events he.1).getElem_inj_iff.mp hg

end LongTails.Proofs.BirchNonEuclideanEventLabels
