import LongTails.Proofs.MultilevelTransportState

namespace LongTails.Proofs.MultilevelInformation

open DistributedTemplate
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelWorkerSchedule
open LongTails.Algorithms.MultilevelTransport (Bits)
open LongTails.Algorithms.MultilevelPipeline
open MultilevelWorkerSchedule MultilevelTimetable

noncomputable def modelTime (p : Params) (k : ℕ) : Time := warmTime p + k * period p

lemma modelTime_mono (p : Params) : Monotone (modelTime p) := by
  intro a b h
  unfold modelTime
  gcongr

lemma boundary_eq (p : Params) (j s : ℕ) :
    boundary (warmTime p) (period p) j s = modelTime p (s*2^j) := by simp [modelTime,boundary]

lemma entry_of_mem (p : Params) {e : Entry p} (he : e ∈ table p) :
    entry p ((table p).idxOf e) = e := by
  rw [entry_at p (List.idxOf_lt_length_of_mem he), List.getElem_idxOf]

lemma level_cells (p : Params) {j s : ℕ} (hj : j ≤ height p) (hs : (s+1)*2^j ≤ wanted p) :
    some (j,s) ∈ cells p := by
  have hpow : 0 < 2^j := by positivity
  have hsize : s < wanted p := by nlinarith
  simp [cells,Finset.mem_product,hj,hs,hsize]

lemma active_due (j k : ℕ) (h : 2^j ≤ k) :
    (k / 2^j - 1 + 1) * 2^j ≤ k := by
  rw [Nat.sub_add_cancel ((Nat.le_div_iff_mul_le (by positivity)).mpr (by simpa using h))]
  exact Nat.div_mul_le_self _ _

lemma avg_agree (p : Params) (hh : ∀ i, 0 < p.h i) (a b : ℕ → Bits)
    (k : ℕ) (h : ∀ m < (table p).length, finish p (entry p m) ≤ modelTime p k → a m = b m)
    (job : Job) (hc : job ∈ cells p)
    (hdue : match job with | none => True | some (j,s) => (s+1)*2^j ≤ k) :
    average p a job = average p b job := by
  dsimp only [average]
  apply congrArg
  apply Finset.sum_congr rfl
  intro z hz
  have hm := mem_table.mpr (show (job,z).1 ∈ cells p ∧ (job,z).2 ∈ reservations p (job,z).1 from ⟨hc,hz⟩)
  have him := List.idxOf_lt_length_of_mem hm
  have hb : finish p (job,z) ≤ modelTime p k := by
    cases job with
    | none =>
      have he := ((available_iff _ (physical_pos p hh) _ _ z).mp (warm_window p hh hz)).2
      refine le_trans (b := warmTime p) (by exact_mod_cast he) (le_add_of_nonneg_right zero_le)
    | some u =>
      rcases u with ⟨j,s⟩
      have he := ((available_iff _ (physical_pos p hh) _ _ z).mp (level_window p hh j s (in_level hc).1 hz)).2
      refine le_trans (b := boundary (warmTime p) (period p) j (s+1)) (by exact_mod_cast he) ?_
      rw [boundary_eq]
      exact modelTime_mono p hdue
  rw [h _ him (by simpa only [entry_of_mem p hm] using hb)]

lemma estimate_agree (p : Params) (hh : ∀ i, 0 < p.h i) (a b : ℕ → Bits) (k : ℕ)
    (hk : k ≤ wanted p)
    (h : ∀ m < (table p).length, finish p (entry p m) ≤ modelTime p k → a m = b m) :
    estimate p a k = estimate p b k := by
  have he (j : ℕ) (hj : j ≤ height p) (hw : 2^j ≤ k) :
      average p a (activeJob j k) = average p b (activeJob j k) :=
    avg_agree p hh a b k h _ (level_cells p hj ((active_due j k hw).trans hk)) (active_due j k hw)
  have h0 : average p a none = average p b none := avg_agree p hh a b k h _ (by simp [cells]) trivial
  unfold estimate
  congr 1
  · split <;> rename_i hx
    · exact he _ le_rfl hx
    · exact h0
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    by_cases hw : 2^j ≤ k
    · simp [hw, he j (Finset.mem_range.mp hj).le hw]
    · simp [hw]

lemma iterate_agree (p : Params) (hh : ∀ i, 0 < p.h i) (a b : ℕ → Bits) (k : ℕ)
    (hk : k ≤ wanted p)
    (h : ∀ m < (table p).length, finish p (entry p m) ≤ modelTime p k → a m = b m) :
    iterate p a k = iterate p b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' := (Nat.le_succ k).trans hk
    have h' := fun m hm (hd : finish p (entry p m) ≤ modelTime p k) =>
      h m hm (hd.trans (modelTime_mono p (Nat.le_succ k)))
    rw [iterate, iterate, ih hk' h', estimate_agree p hh a b k hk' h']

lemma data_at_send (p : Params) (hh : ∀ i, 0 < p.h i) (bits : ℕ → Bits) (k : ℕ)
    (hk : k < (table p).length) :
    MultilevelTransportState.payload (script p) bits k = queryBits p bits (entry p k).1 := by
  change queryBits p (fun j => if j < k ∧ finish p (entry p j) ≤ start p (entry p k) then bits j else [])
    (entry p k).1 = _
  have hm : entry p k ∈ table p := by rw [entry_at p hk]; exact List.getElem_mem ..
  obtain ⟨hc,hs⟩ := mem_table.mp hm
  generalize hj : (entry p k).1 = job at hc hs ⊢
  cases job with
  | none => rfl
  | some u =>
    rcases u with ⟨j,s⟩
    have hjs := in_level hc
    have hstart := ((available_iff _ (physical_pos p hh) _ _ _).mp (level_window p hh j s hjs.1 hs)).1
    have hrelease : modelTime p (s*2^j) ≤ start p (entry p k) := by
      rw [← boundary_eq]
      exact_mod_cast hstart
    have hsk : s*2^j ≤ wanted p := (Nat.mul_le_mul_right _ (Nat.le_succ s)).trans hjs.2
    have hhg (u : ℕ) (hu : u ≤ s*2^j) (m : ℕ) (hm : m < (table p).length)
        (hd : finish p (entry p m) ≤ modelTime p u) :
        (if m < k ∧ finish p (entry p m) ≤ start p (entry p k) then bits m else []) = bits m := by
      have hend := hd.trans ((modelTime_mono p hu).trans hrelease)
      have hstrict : start p (entry p m) < finish p (entry p m) := by
        unfold start finish
        exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self _) (physical_pos p hh _)
      have hmk : m < k := by
        by_contra! hn
        exact (not_lt_of_ge (ordered p hn hm)) (hstrict.trans_le hend)
      simp [hmk,hend]
    have left := iterate_agree p hh _ bits _ hsk (hhg _ le_rfl)
    have hp := parent_known (2^j) s (by positivity)
    have right := iterate_agree p hh _ bits _ (hp.trans hsk) (hhg _ hp)
    simp only [queryBits, left, right]

end LongTails.Proofs.MultilevelInformation
