import LongTails.Algorithms.MultilevelWorkerSchedule
import LongTails.Proofs.DistributedBatchedSgd

namespace LongTails.Proofs.MultilevelWorkerSchedule

open DistributedTemplate
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelWorkerSchedule

lemma speed_pos (p : Params) (hh : ∀ i, 0 < p.h i) (i : Fin p.n) : 0 < speed p i :=
  DistributedBatchedSgd.throughput_pos hh i

lemma batch_witness (p : Params) (b : ℕ) :
    ∃ i, batchDuration p b = 2 * max (p.h i) ((b : Time) / speed p i) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin p.n)))
    Finset.univ_nonempty (fun i => max (p.h i) ((b : Time) / speed p i))
  exact ⟨i, congrArg (2 * ·) hi⟩

lemma sufficient_samples (p : Params) (hh : ∀ i, 0 < p.h i) (b : ℕ) :
    b ≤ ∑ i, samples p b i := by
  obtain ⟨i, hi⟩ := batch_witness p b
  let workers := Finset.univ.filter fun j => p.h j ≤ p.h i
  have hn (j) (hj : j ∈ workers) : 2 * (p.h j : ℝ) ≤ (batchDuration p b : ℝ) := by
    rw [hi]
    exact_mod_cast mul_le_mul_of_nonneg_left
      (((Finset.mem_filter.mp hj).2 : p.h j ≤ p.h i).trans (le_max_left _ _)) (by positivity : (0 : Time) ≤ 2)
  have hs : (∑ j ∈ workers, (1 : ℝ) / p.h j) = speed p i := by
    simp [workers, speed, Finset.sum_filter, one_div, apply_ite]
  have hb : (b : ℝ) ≤ (batchDuration p b : ℝ) / 2 * ∑ j ∈ workers, 1 / (p.h j : ℝ) := by
    rw [hs, hi]
    have he : (0 : ℝ) < speed p i := by exact_mod_cast speed_pos p hh i
    have hq := (div_le_iff₀ he).mp (le_max_right (p.h i : ℝ) (b / (speed p i : ℝ)))
    push_cast
    linarith
  have h := DistributedBatchedSgd.parallel_batch_capacity (fun j => (p.h j : ℝ))
    (fun j => by exact_mod_cast hh j) workers (batchDuration p b) b hn hb
  exact_mod_cast h

lemma sample_time (p : Params) (hh : ∀ i, 0 < p.h i) (b : ℕ) (i : Fin p.n) :
    samples p b i * p.h i ≤ batchDuration p b := by
  have hpos : (0 : ℝ) < p.h i := by exact_mod_cast hh i
  have h := (le_div_iff₀ hpos).mp (Nat.floor_le
    (show 0 ≤ (batchDuration p b : ℝ) / p.h i by positivity))
  exact_mod_cast h

lemma anchor_le (r k : ℕ) : anchor r k ≤ k :=
  (Nat.mul_le_mul_right r (Nat.sub_le _ 1)).trans (Nat.div_mul_le_self k r)

lemma anchor_age (r k : ℕ) (hr : 0 < r) : k < anchor r k + 2 * r := by
  have hk := Nat.lt_mul_div_succ k hr
  by_cases h : k / r = 0
  · simp [anchor, h] at hk ⊢
    omega
  · have he : k / r + 1 = (k / r - 1) + 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, ← Nat.add_assoc, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)]
    rw [he, Nat.mul_add] at hk
    simpa [anchor, Nat.mul_comm, Nat.add_comm] using hk

lemma parent_at_release (r k : ℕ) (hr : 0 < r) (hk : r ≤ k) :
    parentAtRelease r (k / r - 1) = anchor (2 * r) k := by
  have hq : 1 ≤ k / r := (Nat.le_div_iff_mul_le hr).mpr (by simpa using hk)
  simp only [parentAtRelease, Nat.sub_add_cancel hq, anchor]
  rw [Nat.mul_comm 2 r, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel _ hr]

lemma parent_known (r s : ℕ) (hr : 0 < r) : parentAtRelease r s ≤ s * r := by
  have he : (s + 1) / 2 * 2 ≤ s + 1 := Nat.div_mul_le_self _ _
  have ht : ((s + 1) / 2 - 1) * 2 ≤ s := by omega
  simpa [parentAtRelease, anchor, Nat.mul_comm 2 r, ← Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel _ hr, Nat.mul_assoc] using Nat.mul_le_mul_right r ht

lemma parent_lag (r s : ℕ) (hr : 0 < r) : s * r ≤ parentAtRelease r s + 2 * r := by
  have he := Nat.div_add_mod (s + 1) 2
  have hm := Nat.mod_lt (s + 1) (by decide : 0 < 2)
  have ht : s ≤ ((s + 1) / 2 - 1) * 2 + 2 := by omega
  have hdiv : ((s + 1) * r) / (2 * r) = (s + 1) / 2 := Nat.mul_div_mul_right _ _ hr
  unfold parentAtRelease anchor
  rw [hdiv, ← Nat.mul_assoc, ← Nat.add_mul]
  exact Nat.mul_le_mul_right r ht

lemma physical_slots {a t h : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hh : 0 < h)
    {k : ℕ} (hk : k < ⌊t / (2 * h)⌋₊) :
    a ≤ (⌈a / h⌉₊ + k : ℕ) * h ∧ ((⌈a / h⌉₊ + k + 1 : ℕ) : ℝ) * h ≤ a + t := by
  have hceil := Nat.le_ceil (a / h)
  have hup := Nat.ceil_lt_add_one (div_nonneg ha hh.le)
  have hfloor := Nat.floor_le (div_nonneg ht (by positivity : 0 ≤ 2 * h))
  have hcount : (k : ℝ) + 1 ≤ (⌊t / (2 * h)⌋₊ : ℝ) := by exact_mod_cast hk
  have hwindow := (le_div_iff₀ (by positivity : 0 < 2 * h)).mp (hcount.trans hfloor)
  have hstart := (div_le_iff₀ hh).mp hceil
  have hstart' : ((⌈a / h⌉₊ : ℝ) - 1) * h ≤ a := (le_div_iff₀ hh).mp (by linarith)
  push_cast
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) k, mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh.le]

lemma reserve_spec {α : Type*} (w : Finset α) (b : ℕ) (hb : b ≤ w.card) :
    reserve w b ⊆ w ∧ (reserve w b).card = b := by
  have ex := Finset.exists_subset_card_eq hb
  simpa [reserve, ex] using Classical.choose_spec ex

lemma allocation_spec {α : Type*} [DecidableEq α] (w : ℕ → ℕ → Finset α) (b : ℕ → ℕ)
    (nested : ∀ j s, w j (2*s) ∪ w j (2*s+1) ⊆ w (j+1) s)
    (j : ℕ) (cap : ∀ l ≤ j, ∀ s, demand b l ≤ (w l s).card) (s : ℕ) :
    (allocation w b j s).1 ⊆ w j s ∧
    (allocation w b j s).1.card ≤ demand b j ∧
    (allocation w b j s).2 ⊆ (allocation w b j s).1 ∧
    (allocation w b j s).2.card = b j := by
  induction j generalizing s with
  | zero =>
    have h := reserve_spec (w 0 s) (b 0) (cap 0 le_rfl s)
    exact ⟨h.1, h.2.le, Finset.Subset.rfl, h.2⟩
  | succ j ih =>
    have hcap (l) (hl : l ≤ j) := cap l (Nat.le_succ_of_le hl)
    have hl := ih hcap (2*s)
    have hr := ih hcap (2*s+1)
    let u := (allocation w b j (2*s)).1 ∪ (allocation w b j (2*s+1)).1
    have hu : u ⊆ w (j+1) s := (Finset.union_subset_union hl.1 hr.1).trans (nested j s)
    have hnum : u.card ≤ 2 * demand b j := by
      have h := Finset.card_union_le (allocation w b j (2*s)).1 (allocation w b j (2*s+1)).1
      dsimp [u]
      omega
    have havail : b (j+1) ≤ (w (j+1) s \ u).card := by
      have hc := cap (j+1) le_rfl s
      rw [demand] at hc
      rw [Finset.card_sdiff_of_subset hu]
      omega
    have h := reserve_spec _ _ havail
    let v := reserve (w (j+1) s \ u) (b (j+1))
    change u ∪ v ⊆ _ ∧ (u ∪ v).card ≤ _ ∧ v ⊆ u ∪ v ∧ v.card = _
    refine ⟨Finset.union_subset hu (h.1.trans Finset.sdiff_subset), ?_, Finset.subset_union_right, h.2⟩
    have hc := Finset.card_union_le u v
    have hv : v.card = b (j+1) := h.2
    rw [demand]
    omega

lemma reserved_away_from_children {α : Type*} [DecidableEq α] (w : ℕ → ℕ → Finset α)
    (b : ℕ → ℕ) (j s : ℕ) :
    Disjoint (allocation w b (j+1) s).2
      ((allocation w b j (2*s)).1 ∪ (allocation w b j (2*s+1)).1) := by
  classical
  simp only [allocation]
  unfold reserve
  split
  · rename_i h
    exact Finset.disjoint_of_subset_left (Classical.choose_spec h).1 Finset.sdiff_disjoint
  · simp

lemma geometric_demand (J : ℕ) (j : ℕ) :
    demand (edgeBatch J) j + (J+1) * 2^j = 2 * edgeBatch J j := by
  induction j with
  | zero => simp [edgeBatch, demand, two_mul]
  | succ j ih =>
    simp only [demand, edgeBatch, pow_succ] at *
    linarith

lemma available_iff (p : Params) (hh : ∀ i, 0 < p.h i) (a z : Time) (slot : Slot p) :
    slot ∈ available p a z ↔
      (a : ℝ) ≤ slot.2 * (p.h slot.1 : ℝ) ∧ ((slot.2 + 1 : ℕ) : ℝ) * (p.h slot.1 : ℝ) ≤ z := by
  have hp : (0 : ℝ) < p.h slot.1 := by exact_mod_cast hh slot.1
  simp only [available, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_Ico]
  rw [Nat.ceil_le, Nat.lt_iff_add_one_le, Nat.le_floor_iff (by positivity),
    div_le_iff₀ hp, le_div_iff₀ hp]

lemma available_capacity (p : Params) (hh : ∀ i, 0 < p.h i) (a z : Time) (b : ℕ)
    (ht : a + 2 * batchDuration p b ≤ z) : b ≤ (available p a z).card := by
  rw [available, Finset.card_sigma]
  refine (sufficient_samples p hh b).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Nat.card_Ico]
  by_cases hs : samples p b i = 0
  · simp [hs]
  have hp : (0 : ℝ) < p.h i := by exact_mod_cast hh i
  have hcount : samples p b i - 1 < samples p b i := by omega
  have he : (2 * (batchDuration p b : ℝ)) / (2 * (p.h i : ℝ)) = (batchDuration p b : ℝ) / p.h i := by ring
  have hw := physical_slots (a := (a : ℝ)) (t := 2 * (batchDuration p b : ℝ))
    a.coe_nonneg (by positivity) hp (k := samples p b i - 1) (by rw [he]; exact hcount)
  have hz : (a : ℝ) + 2 * (batchDuration p b : ℝ) ≤ z := by exact_mod_cast ht
  have hend := (Nat.le_floor_iff (by positivity : (0:ℝ) ≤ (z:ℝ) / p.h i)).mpr
    ((le_div_iff₀ hp).mpr (hw.2.trans hz))
  omega

lemma boundary_first (o D : Time) (j s : ℕ) : boundary o D j (2*s) = boundary o D (j+1) s := by
  unfold boundary
  push_cast
  rw [pow_succ]
  ring

lemma boundary_last (o D : Time) (j s : ℕ) : boundary o D j (2*s+2) = boundary o D (j+1) (s+1) := by
  unfold boundary
  push_cast
  rw [pow_succ]
  ring

lemma boundary_succ (o D : Time) (j s : ℕ) :
    boundary o D j (s+1) = boundary o D j s + 2^j * D := by
  simp [boundary]
  ring

lemma window_nested (p : Params) (hh : ∀ i, 0 < p.h i) (o D : Time) (j s : ℕ) :
    window p o D j (2*s) ∪ window p o D j (2*s+1) ⊆ window p o D (j+1) s := by
  intro slot h
  simp only [Finset.mem_union, window, available_iff p hh] at h ⊢
  rw [← boundary_first o D j s, ← boundary_last o D j s]
  have h₁ : boundary o D j (2*s) ≤ boundary o D j (2*s+1) := by rw [boundary_succ]; exact le_add_of_nonneg_right zero_le
  have h₂ : boundary o D j (2*s+1) ≤ boundary o D j (2*s+2) := by rw [show 2*s+2=2*s+1+1 by omega, boundary_succ o D j (2*s+1)]; exact le_add_of_nonneg_right zero_le
  rcases h with h | h
  · exact ⟨h.1, h.2.trans (NNReal.coe_le_coe.mpr h₂)⟩
  · exact ⟨(NNReal.coe_le_coe.mpr h₁).trans h.1, h.2⟩

lemma window_separate (p : Params) (hh : ∀ i, 0 < p.h i) (o D : Time) (j s t : ℕ) (hst : s < t) :
    Disjoint (window p o D j s) (window p o D j t) := by
  apply Finset.disjoint_left.mpr
  intro slot hs ht
  have h₁ := ((available_iff p hh _ _ slot).mp hs).2
  have h₂ := ((available_iff p hh _ _ slot).mp ht).1
  have hst' : boundary o D j (s+1) ≤ boundary o D j t := by
    unfold boundary
    gcongr
    exact_mod_cast hst
  have hr := h₁.trans ((NNReal.coe_le_coe.mpr hst').trans h₂)
  have hp : (0 : ℝ) < p.h slot.1 := by exact_mod_cast hh slot.1
  push_cast at hr
  nlinarith

lemma demand_lower_levels (J S j : ℕ) (h : j < J) :
    demand (multilevelBatch J S) j = demand (edgeBatch J) j := by
  induction j with
  | zero => simp [demand, multilevelBatch, h.ne]
  | succ j ih => simp [demand, multilevelBatch, h.ne, ih (by omega)]

lemma demand_bound (J S j : ℕ) (hj : j ≤ J) :
    demand (multilevelBatch J S) j ≤ 2 * edgeBatch J j + if j = J then S else 0 := by
  by_cases h : j = J
  · subst j
    cases J with
    | zero => simp [demand, multilevelBatch]
    | succ j =>
      rw [demand, demand_lower_levels _ _ _ (Nat.lt_succ_self _)]
      have h := geometric_demand (j+1) j
      simp only [multilevelBatch, ite_true, edgeBatch, pow_succ]
      have hd : demand (edgeBatch (j+1)) j ≤ 2 * edgeBatch (j+1) j := by omega
      change demand (edgeBatch (j+1)) j ≤ 2 * ((j+1+1) * 4^j) at hd
      nlinarith
  · simp only [h, ite_false, add_zero, demand_lower_levels _ _ _ (lt_of_le_of_ne hj h)]
    have := geometric_demand J j
    omega

lemma tick_capacity (p : Params) (hh : ∀ i, 0 < p.h i) (J S : ℕ) (o : Time)
    (j : ℕ) (hj : j ≤ J) (s : ℕ) :
    demand (multilevelBatch J S) j ≤ (window p o (tickDuration p J S) j s).card := by
  refine (demand_bound J S j hj).trans (available_capacity p hh _ _ _ ?_)
  rw [boundary_succ]
  apply add_le_add_right
  rw [mul_comm (2^j : Time), ← div_le_iff₀ (by positivity : (0 : Time) < 2^j)]
  exact Finset.le_sup (f := fun j => 2 * batchDuration p (2 * edgeBatch J j + if j = J then S else 0) / 2^j)
    (Finset.mem_range.mpr (by omega : j < J+1))

lemma job_samples (p : Params) (hh : ∀ i, 0 < p.h i) (J S : ℕ) (o : Time)
    (j : ℕ) (hj : j ≤ J) (s : ℕ) :
    ((allocation (window p o (tickDuration p J S)) (multilevelBatch J S) j s).2).card =
      multilevelBatch J S j :=
  (allocation_spec _ _ (window_nested p hh _ _) j
    (fun l hl => tick_capacity p hh J S o l (hl.trans hj)) s).2.2.2

lemma child_used {α : Type*} [DecidableEq α] (w : ℕ → ℕ → Finset α) (b : ℕ → ℕ) (j s : ℕ) :
    (allocation w b j s).1 ⊆ (allocation w b j (2*(s/2))).1 ∪ (allocation w b j (2*(s/2)+1)).1 := by
  rcases (show s = 2*(s/2) ∨ s = 2*(s/2)+1 by omega) with h | h
  · intro x hx
    exact Finset.mem_union_left _ (congrArg (fun z => x ∈ (allocation w b j z).1) h ▸ hx)
  · intro x hx
    exact Finset.mem_union_right _ (congrArg (fun z => x ∈ (allocation w b j z).1) h ▸ hx)

lemma used_parent {α : Type*} [DecidableEq α] (w : ℕ → ℕ → Finset α) (b : ℕ → ℕ) (j s : ℕ) :
    (allocation w b j s).1 ⊆ (allocation w b (j+1) (s/2)).1 :=
  (child_used w b j s).trans Finset.subset_union_left

lemma ascending_used {α : Type*} [DecidableEq α] (w : ℕ → ℕ → Finset α) (b : ℕ → ℕ) (j s d : ℕ) :
    (allocation w b j s).1 ⊆ (allocation w b (j+d) (s/2^d)).1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    simpa only [Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_succ] using
      ih.trans (used_parent w b (j+d) (s/2^d))

lemma cells_disjoint (p : Params) (hh : ∀ i, 0 < p.h i) (J S : ℕ) (o : Time) (j l s t : ℕ)
    (hj : j ≤ l) (hl : l ≤ J) (hdiff : (j,s) ≠ (l,t)) :
    let w := window p o (tickDuration p J S)
    let b := multilevelBatch J S
    Disjoint (allocation w b j s).2 (allocation w b l t).2 := by
  intro w b
  have spec (k : ℕ) (hk : k ≤ J) (u : ℕ) :=
    allocation_spec w b (window_nested p hh o _) k
      (fun a ha => tick_capacity p hh J S o a (ha.trans hk)) u
  have separate (k a c : ℕ) (hne : a ≠ c) : Disjoint (w k a) (w k c) := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact window_separate p hh _ _ _ _ _ h
    · exact (window_separate p hh _ _ _ _ _ h).symm
  have hsrc := (spec j (hj.trans hl) s).2.2.1
  have htgt := (spec l hl t).2.2.1.trans (spec l hl t).1
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hj
  cases d with
  | zero =>
    exact (separate j s t (by aesop)).mono (hsrc.trans (spec j hl s).1) htgt
  | succ d =>
    let parent := s / 2^d
    have hu := hsrc.trans (ascending_used w b j s d)
    by_cases h : parent/2 = t
    · have hc := hu.trans (child_used w b (j+d) parent)
      rw [h] at hc
      exact (reserved_away_from_children w b (j+d) t).symm.mono_left hc
    · have hc := hu.trans (used_parent w b (j+d) parent)
      exact (separate (j+d+1) _ t h).mono
        (hc.trans (spec _ hl _).1) htgt

end LongTails.Proofs.MultilevelWorkerSchedule
