import LongTails.Algorithms.BirchNonEuclideanPhysical
import Mathlib.Tactic

namespace LongTails.Proofs.BirchNonEuclideanScheduling

open LongTails.Algorithms.BirchNonEuclideanPhysical

def agePotential {m : ℕ} (s : PacketSchedule m) : ℤ :=
  ∑ i : Fin m, ((s.accepted.length : ℤ) - (s.source i : ℤ))

def ScheduleInvariant {m : ℕ} (K R : ℕ) (s : PacketSchedule m) : Prop :=
  s.accepted.length ≤ K ∧ (∀ i, s.source i ≤ s.accepted.length) ∧
    ((R : ℤ) + 1) * s.rejected.length + agePotential s ≤ ((m : ℤ) - 1) * s.accepted.length ∧
    s.completed.length = s.accepted.length + s.rejected.length

lemma sum_update_int {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ) (w : ι) (b : ℤ) :
    (∑ i, Function.update f w b i) = (∑ i, f i) + b - f w := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ w)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hh := Finset.sum_erase_add Finset.univ f (Finset.mem_univ w)
  omega

lemma age_update {m : ℕ} (A A' : ℕ) (source : Fin m → ℕ) (w : Fin m) :
    (∑ i : Fin m, ((A' : ℤ) - (Function.update source w A' i : ℤ))) =
      (∑ i : Fin m, ((A : ℤ) - (source i : ℤ))) + (m : ℤ) * (A' - A) - (A' - source w) := by
  have he : (fun i => (A' : ℤ) - (Function.update source w A' i : ℤ)) =
      Function.update (fun i => (A' : ℤ) - (source i : ℤ)) w 0 := by
    funext i
    by_cases hi : i = w
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  rw [he, sum_update_int]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma agePotential_nonneg {m : ℕ} (s : PacketSchedule m) (hs : ∀ i, s.source i ≤ s.accepted.length) :
    0 ≤ agePotential s := by
  apply Finset.sum_nonneg
  intro i _
  exact sub_nonneg.mpr (by exact_mod_cast hs i)

lemma scheduleStep_invariant {m : ℕ} (K R : ℕ) (w : Fin m) (s : PacketSchedule m)
    (hs : ScheduleInvariant K R s) : ScheduleInvariant K R (scheduleStep K R w s) := by
  unfold scheduleStep
  split_ifs with hactive hgood
  · rcases hs with ⟨hK, hsrc, hcredit, hcount⟩
    refine ⟨by simp; omega, ?_, ?_, by simp only [List.length_append, List.length_singleton]; omega⟩
    · intro i
      by_cases hi : i = w
      · subst i
        simp
      · simp only [Function.update_of_ne hi, List.length_append, List.length_singleton]
        exact (hsrc i).trans (Nat.le_add_right _ _)
    · change ((R : ℤ) + 1) * s.rejected.length +
        (∑ i : Fin m, (((s.accepted ++ [(⟨w, s.source w, s.serial w⟩ : Packet m)]).length : ℤ) -
          (Function.update s.source w (s.accepted.length + 1) i : ℤ))) ≤
            ((m : ℤ) - 1) * (s.accepted ++ [(⟨w, s.source w, s.serial w⟩ : Packet m)]).length
      simp only [List.length_append, List.length_singleton]
      rw [age_update s.accepted.length (s.accepted.length + 1)]
      simp only [Nat.cast_add, Nat.cast_one]
      have hage : (0 : ℤ) ≤ (s.accepted.length : ℤ) - s.source w := sub_nonneg.mpr (by exact_mod_cast hsrc w)
      dsimp [agePotential] at hcredit
      nlinarith
  · rcases hs with ⟨hK, hsrc, hcredit, hcount⟩
    refine ⟨hK, ?_, ?_, by simp; omega⟩
    · intro i
      by_cases hi : i = w
      · subst i
        simp
      · simpa only [Function.update_of_ne hi] using hsrc i
    · change ((R : ℤ) + 1) * (s.rejected ++ [(⟨w, s.source w, s.serial w⟩ : Packet m)]).length +
        (∑ i : Fin m, ((s.accepted.length : ℤ) - (Function.update s.source w s.accepted.length i : ℤ))) ≤ _
      rw [age_update s.accepted.length s.accepted.length]
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      have hageNat : R + 1 ≤ s.accepted.length - s.source w := by omega
      have hage : (R : ℤ) + 1 ≤ (s.accepted.length : ℤ) - s.source w := by
        have hh : ((R + 1 : ℕ) : ℤ) ≤ ((s.accepted.length - s.source w : ℕ) : ℤ) := by exact_mod_cast hageNat
        simpa only [Nat.cast_add, Nat.cast_one, Int.natCast_sub (hsrc w)] using hh
      dsimp [agePotential] at hcredit
      nlinarith
  · exact hs

lemma scheduleRun_invariant {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ) :
    ScheduleInvariant K R (scheduleRun K R word n) := by
  induction n with
  | zero => simp [scheduleRun, ScheduleInvariant, agePotential]
  | succ n ih => exact scheduleStep_invariant K R (word n) _ ih

lemma scheduleStep_count {m : ℕ} (K R : ℕ) (w : Fin m) (s : PacketSchedule m)
    (ha : s.accepted.length < K) :
    (scheduleStep K R w s).completed.length = s.completed.length + 1 := by
  simp only [scheduleStep, ite_eq_left ha]
  split_ifs <;> simp

lemma scheduleStep_accept_mono {m : ℕ} (K R : ℕ) (w : Fin m) (s : PacketSchedule m) :
    s.accepted.length ≤ (scheduleStep K R w s).accepted.length := by
  unfold scheduleStep
  split_ifs <;> simp

lemma scheduleRun_active_count {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ)
    (ha : (scheduleRun K R word n).accepted.length < K) :
    (scheduleRun K R word n).completed.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev : (scheduleRun K R word n).accepted.length < K :=
        (scheduleStep_accept_mono K R (word n) _).trans_lt ha
      rw [scheduleRun, scheduleStep_count K R (word n) _ hprev, ih hprev]

lemma scheduleRun_rejected_bound {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ) (hm : 0 < m) :
    (R + 1) * (scheduleRun K R word n).rejected.length ≤
      (m - 1) * (scheduleRun K R word n).accepted.length := by
  have hs := scheduleRun_invariant K R word n
  have ha := agePotential_nonneg _ hs.2.1
  have he : ((R : ℤ) + 1) * (scheduleRun K R word n).rejected.length ≤
      ((m : ℤ) - 1) * (scheduleRun K R word n).accepted.length := by linarith [hs.2.2.1]
  have hm1 : (1 : ℕ) ≤ m := hm
  exact_mod_cast he

lemma scheduleRun_stopped {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (hK : 0 < K) (hm : 0 < m) :
    (scheduleRun K R word (completionLimit m K R)).accepted.length = K := by
  let s := scheduleRun K R word (completionLimit m K R)
  have hs := scheduleRun_invariant K R word (completionLimit m K R)
  apply Nat.le_antisymm hs.1
  by_contra hk
  change ¬ K ≤ s.accepted.length at hk
  have ha : s.accepted.length < K := by omega
  have hn := scheduleRun_active_count K R word (completionLimit m K R) ha
  have hd := scheduleRun_rejected_bound K R word (completionLimit m K R) hm
  change (R + 1) * s.rejected.length ≤ (m - 1) * s.accepted.length at hd
  have hmul : (R + 1) * s.rejected.length ≤ (m - 1) * (K - 1) :=
    hd.trans (Nat.mul_le_mul_left (m - 1) (by omega))
  have hdiv : s.rejected.length ≤ (m - 1) * (K - 1) / (R + 1) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < R + 1)).2 (by simpa [Nat.mul_comm] using hmul)
  have hc := hs.2.2.2
  change s.completed.length = s.accepted.length + s.rejected.length at hc
  change s.completed.length = completionLimit m K R at hn
  dsimp [completionLimit] at hn
  omega

lemma scheduleRun_rejected_final_bound {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ) (hm : 0 < m) :
    (R + 1) * (scheduleRun K R word n).rejected.length ≤ (m - 1) * (K - 1) := by
  induction n with
  | zero => simp [scheduleRun]
  | succ n ih =>
      let s := scheduleRun K R word n
      by_cases ha : s.accepted.length < K
      · by_cases hg : s.accepted.length - s.source (word n) ≤ R
        · simpa only [scheduleRun, scheduleStep, s, ite_eq_left ha, ite_eq_left hg] using ih
        · have hp := scheduleRun_rejected_bound K R word (n + 1) hm
          have he : (scheduleRun K R word (n + 1)).accepted.length = s.accepted.length := by
            change (scheduleStep K R (word n) s).accepted.length = s.accepted.length
            simp only [scheduleStep, ite_eq_left ha, ite_eq_right hg]
          rw [he] at hp
          exact hp.trans (Nat.mul_le_mul_left (m - 1) (by omega))
      · simpa only [scheduleRun, scheduleStep, s, ite_eq_right ha] using ih

lemma scheduleRun_last {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ)
    (ha : 0 < (scheduleRun K R word n).accepted.length) :
    ∃ w, (scheduleRun K R word n).last = some w := by
  induction n with
  | zero => simp [scheduleRun] at ha
  | succ n ih =>
      by_cases hactive : (scheduleRun K R word n).accepted.length < K
      · unfold scheduleRun scheduleStep
        rw [ite_eq_left hactive]
        split_ifs <;> exact ⟨word n, rfl⟩
      · have he : scheduleRun K R word (n + 1) = scheduleRun K R word n := by
          simp only [scheduleRun, scheduleStep, ite_eq_right hactive]
        rw [he] at ha ⊢
        exact ih ha

lemma scheduleRun_stopped_sources {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ) (hK : 0 < K)
    (ha : (scheduleRun K R word n).accepted.length = K) :
    ∀ i, some i ≠ (scheduleRun K R word n).last → (scheduleRun K R word n).source i < K := by
  induction n with
  | zero => simp [scheduleRun] at ha; omega
  | succ n ih =>
      let s := scheduleRun K R word n
      by_cases hactive : s.accepted.length < K
      · by_cases hgood : s.accepted.length - s.source (word n) ≤ R
        · have he : scheduleRun K R word (n + 1) =
              { accepted := s.accepted ++ [⟨word n, s.source (word n), s.serial (word n)⟩]
                rejected := s.rejected
                completed := s.completed ++ [⟨word n, s.source (word n), s.serial (word n)⟩]
                source := Function.update s.source (word n) (s.accepted.length + 1)
                serial := Function.update s.serial (word n) (s.serial (word n) + 1)
                last := some (word n) } := by
            change scheduleStep K R (word n) s = _
            simp only [scheduleStep, ite_eq_left hactive, ite_eq_left hgood]
          rw [he]
          intro i hi
          have hin : i ≠ word n := by simpa using hi
          change Function.update s.source (word n) (s.accepted.length + 1) i < K
          rw [Function.update_of_ne hin]
          exact ((scheduleRun_invariant K R word n).2.1 i).trans_lt hactive
        · have hlen : (scheduleRun K R word (n + 1)).accepted.length = s.accepted.length := by
            change (scheduleStep K R (word n) s).accepted.length = s.accepted.length
            simp only [scheduleStep, ite_eq_left hactive, ite_eq_right hgood]
          rw [hlen] at ha
          omega
      · have he : scheduleRun K R word (n + 1) = s := by
          change scheduleStep K R (word n) s = s
          simp only [scheduleStep, ite_eq_right hactive]
        rw [he] at ha ⊢
        exact ih ha

lemma scheduleRun_rejected_sources {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ) :
    ∀ job ∈ (scheduleRun K R word n).rejected, job.source < K := by
  induction n with
  | zero => simp [scheduleRun]
  | succ n ih =>
      let s := scheduleRun K R word n
      have hsource := (scheduleRun_invariant K R word n).2.1
      unfold scheduleRun scheduleStep
      split_ifs with ha hg
      · exact ih
      · intro job hj
        rcases List.mem_append.mp hj with hj | hj
        · exact ih job hj
        · have he : job = ⟨word n, s.source (word n), s.serial (word n)⟩ := by simpa using hj
          rw [he]
          exact (hsource (word n)).trans_lt ha
      · exact ih

def AcceptedValid {m : ℕ} (R : ℕ) (jobs : List (Packet m)) : Prop :=
  ∀ k (hk : k < jobs.length), jobs[k].source ≤ k ∧ k - jobs[k].source ≤ R

lemma acceptedValid_append {m : ℕ} (R : ℕ) (jobs : List (Packet m)) (job : Packet m)
    (hj : AcceptedValid R jobs) (hs : job.source ≤ jobs.length) (hr : jobs.length - job.source ≤ R) :
    AcceptedValid R (jobs ++ [job]) := by
  intro k hk
  by_cases hold : k < jobs.length
  · simpa only [List.getElem_append_left hold] using hj k hold
  · have he : k = jobs.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    simpa using And.intro hs hr

lemma scheduleRun_accepted_valid {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) (n : ℕ) :
    AcceptedValid R (scheduleRun K R word n).accepted := by
  induction n with
  | zero => simp [AcceptedValid, scheduleRun]
  | succ n ih =>
      have hs := (scheduleRun_invariant K R word n).2.1
      unfold scheduleRun scheduleStep
      split_ifs with ha hg
      · exact acceptedValid_append R _ _ ih (hs (word n)) hg
      · exact ih
      · exact ih

lemma packetSource_valid {m : ℕ} (R : ℕ) (jobs : List (Packet m)) (hv : AcceptedValid R jobs) :
    ∀ k, packetSource jobs k ≤ k ∧ k - packetSource jobs k ≤ R := by
  intro k
  by_cases hk : k < jobs.length
  · simpa [packetSource, List.getElem?_eq_getElem hk] using hv k hk
  · simp [packetSource, List.getElem?_eq_none (by omega : jobs.length ≤ k)]

lemma packetWorker_bound {m : ℕ} (jobs : List (Packet m)) (k : ℕ) : packetWorker jobs k < m + 1 := by
  by_cases hk : k < jobs.length
  · simp [packetWorker, List.getElem?_eq_getElem hk]
  · simp [packetWorker, List.getElem?_eq_none (by omega : jobs.length ≤ k)]

lemma pending_length {m : ℕ} (s : PacketSchedule m) (w : Fin m) (hw : s.last = some w) :
    (pending s).length = m - 1 := by
  let xs := (List.finRange m).filter (fun i => some i != s.last)
  have hn : xs.Nodup := (List.nodup_finRange m).filter _
  have he : xs.toFinset = Finset.univ.erase w := by
    ext i
    simp [xs, hw, ne_comm]
  unfold pending
  rw [List.length_map]
  change xs.length = m - 1
  rw [← List.toFinset_card_of_nodup hn, he]
  simp

lemma pending_sources {m : ℕ} (K : ℕ) (s : PacketSchedule m)
    (hs : ∀ i, some i ≠ s.last → s.source i < K) :
    ∀ job ∈ pending s, job.source < K := by
  intro job hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
  exact hs i (by simpa using (List.mem_filter.mp hi).2)

lemma finalSchedule_properties {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (hK : 0 < K) (hm : 0 < m) :
    let s := finalSchedule H K B word
    s.accepted.length = K ∧ (∃ w, s.last = some w) := by
  have hstop := scheduleRun_stopped K (packetCutoff H B) word hK hm
  exact ⟨hstop, scheduleRun_last K (packetCutoff H B) word _ (by rw [hstop]; exact hK)⟩

lemma ignored_length {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (hK : 0 < K) (hm : 0 < m) :
    (ignored (finalSchedule H K B word)).length = (finalSchedule H K B word).rejected.length + (m - 1) := by
  obtain ⟨w, hw⟩ := (finalSchedule_properties H K B word hK hm).2
  rw [ignored, List.length_append, pending_length _ w hw]

lemma ignored_sources {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (hK : 0 < K) (hm : 0 < m) :
    ∀ job ∈ ignored (finalSchedule H K B word), job.source < K := by
  intro job hj
  rcases List.mem_append.mp hj with hr | hp
  · exact scheduleRun_rejected_sources K (packetCutoff H B) word _ job hr
  · exact pending_sources K _ (scheduleRun_stopped_sources K (packetCutoff H B) word _ hK
      (scheduleRun_stopped K (packetCutoff H B) word hK hm)) job hp

lemma physicalLocalCalls_exact {m : ℕ} (H : ℕ) (word : ℕ → ℕ → ℕ → Fin m) (K B : ℕ)
    (hK : 0 < K) (hm : 0 < m) :
    physicalLocalCalls H word K B = B + H * (K + (finalSchedule H K B (word K B)).rejected.length + m - 1) := by
  rw [physicalLocalCalls, ignored_length H K B (word K B) hK hm]
  congr 2
  omega

lemma physicalLocalCalls_upper {m : ℕ} (H : ℕ) (word : ℕ → ℕ → ℕ → Fin m) (K B : ℕ)
    (hK : 0 < K) (hm : 0 < m) :
    physicalLocalCalls H word K B ≤
      B + H * (K + (m - 1) * (K - 1) / (packetCutoff H B + 1) + m - 1) := by
  rw [physicalLocalCalls_exact H word K B hK hm]
  have hb := scheduleRun_rejected_final_bound K (packetCutoff H B) (word K B)
    (completionLimit m K (packetCutoff H B)) hm
  have hd : (finalSchedule H K B (word K B)).rejected.length ≤
      (m - 1) * (K - 1) / (packetCutoff H B + 1) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < packetCutoff H B + 1)).2 (by simpa [finalSchedule, Nat.mul_comm] using hb)
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  omega

lemma packetCutoff_conditions (H B : ℕ) (hH : 0 < H) (hB : 8 * H ≤ B) :
    max (2 * H) (4 * H * packetCutoff H B) ≤ B ∧
      (3 * (packetCutoff H B : ℝ) + 2 + 2 * (B : ℝ) / H) ≤ 2 + 3 * (B : ℝ) / H := by
  have hdiv : 8 * H * packetCutoff H B ≤ B := by
    unfold packetCutoff
    simpa [Nat.mul_comm, Nat.mul_assoc] using Nat.div_mul_le_self B (8 * H)
  have hmax : max (2 * H) (4 * H * packetCutoff H B) ≤ B := by
    apply max_le
    · omega
    · nlinarith
  refine ⟨hmax, ?_⟩
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hdivr : (8 : ℝ) * H * packetCutoff H B ≤ B := by exact_mod_cast hdiv
  have h3 : (3 : ℝ) * packetCutoff H B ≤ (B : ℝ) / H := by
    apply (le_div_iff₀ hHr).2
    nlinarith [show (0 : ℝ) ≤ H * packetCutoff H B by positivity]
  simp only [div_eq_mul_inv] at h3 ⊢
  nlinarith

end LongTails.Proofs.BirchNonEuclideanScheduling
