import LongTails.Algorithms.MultilevelPipeline
import LongTails.Proofs.MultilevelWorkerSchedule
import LongTails.Proofs.DistributedQuantization

namespace LongTails.Proofs.MultilevelTimetable

open DistributedTemplate
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelWorkerSchedule
open LongTails.Algorithms.MultilevelTransport
open LongTails.Algorithms.MultilevelPipeline
open LongTails.Proofs.MultilevelWorkerSchedule

def wire (p : Params) (bs : Bits) : Time := p.b * (bs.length + clockBits : ℕ) + p.l

structure Timetable (p : Params) (t : Script p) (T : Time) : Prop where
  ordered : ∀ i j, i ≤ j → j < t.count → t.start i ≤ t.start j
  service : ∀ k < t.count, ∀ bits value,
    t.start k + wire p (t.request k bits) + 2 * p.h (t.worker k) +
      wire p (t.encode (t.request k bits) value) ≤ t.finish k
  exclusive : ∀ i j, i < j → j < t.count → t.worker i = t.worker j → t.finish i ≤ t.start j
  deadline : ∀ i < t.count, t.finish i ≤ T

lemma physical_pos (p : Params) (hh : ∀ i, 0 < p.h i) (i : Fin p.n) : 0 < (physical p).h i := by
  change 0 < 2 * p.h i + 2*p.l + p.b * _
  positivity [hh i]

lemma mem_table {p : Params} {e : Entry p} :
    e ∈ table p ↔ e.1 ∈ cells p ∧ e.2 ∈ reservations p e.1 := by
  classical
  simp [table, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff]

lemma entry_at (p : Params) {k : ℕ} (hk : k < (table p).length) : entry p k = (table p)[k] := by
  simp [entry, hk]

lemma table_order (p : Params) : (table p).Pairwise (fun x y => start p x ≤ start p y) := by
  unfold table
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort (le := fun a b : Entry p => decide (start p a ≤ start p b))
      (fun a b c => by simp only [decide_eq_true_eq]; exact le_trans)
      (fun a b => by simpa using le_total (start p a) (start p b)) _)

lemma in_level {p : Params} {j s : ℕ} (h : some (j,s) ∈ cells p) :
    j ≤ height p ∧ (s+1)*2^j ≤ wanted p := by
  simp [cells, Finset.mem_product] at h
  exact ⟨h.1.1, h.2⟩

lemma level_window (p : Params) (hh : ∀ i, 0 < p.h i) (j s : ℕ) (hj : j ≤ height p) :
    reservations p (some (j,s)) ⊆ window (physical p) (warmTime p) (period p) j s := by
  have hp := physical_pos p hh
  have hs := allocation_spec (window (physical p) (warmTime p) (period p))
    (multilevelBatch (height p) (fullBatch p)) (window_nested _ hp _ _) j
    (fun l hl => tick_capacity _ hp _ _ _ l (hl.trans hj)) s
  exact hs.2.2.1.trans hs.1

lemma warm_window (p : Params) (hh : ∀ i, 0 < p.h i) :
    reservations p none ⊆ available (physical p) 0 (warmTime p) :=
  (reserve_spec _ _ (available_capacity _ (physical_pos p hh) _ _ _ (by simp [warmTime]))).1

lemma member_interval (p : Params) (hh : ∀ i, 0 < p.h i) (e : Entry p) (h : e ∈ table p) :
    finish p e ≤ duration p := by
  rcases e with ⟨job,z⟩
  obtain ⟨hc, hz⟩ := mem_table.mp h
  have hp := physical_pos p hh
  cases job with
  | none =>
    have hb : fullBatch p ≤ (available (physical p) 0 (warmTime p)).card :=
      available_capacity _ hp _ _ _ (by simp [warmTime])
    have hs := (reserve_spec _ _ hb).1 hz
    have ht := ((available_iff _ hp _ _ z).mp hs).2
    change (z.2 + 1 : ℕ) * (physical p).h z.1 ≤ _
    apply le_trans (b := warmTime p) (by exact_mod_cast ht)
    exact le_add_of_nonneg_right zero_le
  | some js =>
    rcases js with ⟨j,s⟩
    have hh' := in_level hc
    have ht := ((available_iff _ hp _ _ z).mp (level_window p hh j s hh'.1 hz)).2
    refine le_trans (b := boundary (warmTime p) (period p) j (s+1)) (by exact_mod_cast ht) ?_
    unfold duration boundary
    gcongr
    exact_mod_cast hh'.2

lemma query_length (p : Params) (a : ℕ → Bits) (job : Job) :
    (queryBits p a job).length = 1 + 2 * p.d * width p := by
  cases job with
  | none => simp [queryBits, DistributedQuantization.message_length]; ring
  | some js => rcases js with ⟨j,s⟩; simp [queryBits, DistributedQuantization.message_length]; ring

lemma response_length (p : Params) (bs : Bits) (v : Query p) :
    (encode p bs v).length = p.d * width p := DistributedQuantization.message_length _ _ _ _

lemma slot_price (p : Params) (e : Entry p) (a : ℕ → Bits) (v : Query p) :
    start p e + wire p (queryBits p a e.1) + 2*p.h e.2.1 + wire p (encode p (queryBits p a e.1) v) =
      finish p e := by
  simp only [wire, query_length, response_length, start, finish, clockBits, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  unfold physical
  push_cast
  ring

lemma warm_disjoint (p : Params) (hh : ∀ i, 0 < p.h i) (j s : ℕ) (hj : j ≤ height p) :
    Disjoint (reservations p none) (reservations p (some (j,s))) := by
  apply Finset.disjoint_left.mpr
  intro z h₀ h₁
  have hp := physical_pos p hh
  have hleft := ((available_iff _ hp _ _ z).mp (warm_window p hh h₀)).2
  have hright := ((available_iff _ hp _ _ z).mp (level_window p hh j s hj h₁)).1
  have hx : warmTime p ≤ boundary (warmTime p) (period p) j s := le_add_of_nonneg_right zero_le
  have h := hleft.trans ((NNReal.coe_le_coe.mpr hx).trans hright)
  have hpos : (0 : ℝ) < (physical p).h z.1 := by exact_mod_cast hp z.1
  push_cast at h
  linarith

lemma reserved_disjoint (p : Params) (hh : ∀ i, 0 < p.h i) {a b : Job}
    (ha : a ∈ cells p) (hb : b ∈ cells p) (hne : a ≠ b) :
    Disjoint (reservations p a) (reservations p b) := by
  cases a with
  | none =>
    cases b with
    | none => contradiction
    | some v => exact warm_disjoint p hh v.1 v.2 (in_level hb).1
  | some u =>
    cases b with
    | none => exact (warm_disjoint p hh u.1 u.2 (in_level ha).1).symm
    | some v =>
      rcases u with ⟨j,s⟩
      rcases v with ⟨l,t⟩
      by_cases he : j ≤ l
      · exact cells_disjoint _ (physical_pos p hh) _ _ _ j l s t he (in_level hb).1
          (fun h => hne (congrArg some h))
      · exact (cells_disjoint _ (physical_pos p hh) _ _ _ l j t s (by omega) (in_level ha).1
          (fun h => hne (congrArg some h.symm))).symm

lemma table_nodup (p : Params) : (table p).Nodup := by simp [table, Finset.nodup_toList]

lemma ordered (p : Params) {i j : ℕ} (hij : i ≤ j) (hj : j < (table p).length) :
    start p (entry p i) ≤ start p (entry p j) := by
  rcases lt_or_eq_of_le hij with h | rfl
  · rw [entry_at p (h.trans hj), entry_at p hj]
    exact List.pairwise_iff_getElem.mp (table_order p) i j (h.trans hj) hj h
  · rfl

lemma distinct_slots (p : Params) (hh : ∀ i, 0 < p.h i) {i j : ℕ}
    (hij : i < j) (hj : j < (table p).length) : (entry p i).2 ≠ (entry p j).2 := by
  rw [entry_at p (hij.trans hj), entry_at p hj]
  intro hs
  have hi := mem_table.mp (List.getElem_mem (l := table p) (n := i) (hij.trans hj))
  have hm := mem_table.mp (List.getElem_mem (l := table p) (n := j) hj)
  by_cases he : ((table p)[i]).1 = ((table p)[j]).1
  · have h := (List.pairwise_iff_getElem.mp (table_nodup p)) i j (hij.trans hj) hj hij
    exact h (Prod.ext he hs)
  · exact (Finset.disjoint_left.mp (reserved_disjoint p hh hi.1 hm.1 he)) hi.2 (hs ▸ hm.2)

lemma certified (p : Params) (hh : ∀ i, 0 < p.h i) : Timetable p (script p) (duration p) where
  ordered _ _ := ordered p
  service k _ bits v := (slot_price p (entry p k) bits v).le
  exclusive i j hij hj hw := by
    change j < (table p).length at hj
    have hs := ordered p hij.le hj
    have hn := distinct_slots p hh hij hj
    change (entry p i).2.1 = (entry p j).2.1 at hw
    unfold start at hs
    rw [hw] at hs
    have hp := physical_pos p hh (entry p j).2.1
    have hz : (entry p i).2.2 ≤ (entry p j).2.2 := by
      exact_mod_cast (le_of_mul_le_mul_right hs hp)
    have hne : (entry p i).2.2 ≠ (entry p j).2.2 := fun he => hn (Sigma.ext hw (heq_of_eq he))
    change ((entry p i).2.2+1 : ℕ) * (physical p).h (entry p i).2.1 ≤ _
    rw [hw]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) hp.le
  deadline k hk := member_interval p hh (entry p k) (by rw [entry_at p hk]; exact List.getElem_mem ..)

end LongTails.Proofs.MultilevelTimetable
