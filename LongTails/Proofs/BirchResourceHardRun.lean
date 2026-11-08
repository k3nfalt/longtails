import LongTails.Proofs.BirchResourceLowerWindow

namespace LongTails.Proofs.BirchResourceHardRun

open Finset MeasureTheory Set
open LongTails.Proofs.BirchResourceAdaptiveLower

structure Slot (Packet : Type*) where
  packet : Packet
  raw : ℕ
  launch : ℝ
  finish : ℝ
  launchPrefix : ℕ
  source : ℕ

abbrev Scheduler (Packet : Type*) := (n : ℕ) → (Fin n → Bool) → Option (Slot Packet)

def observed {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool) (n : ℕ) :
    Option (Slot Packet) := run n (past n ξ)

def level {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    match observed run ξ n with
    | none => level run ξ n
    | some s => max (level run ξ n) (s.source + if ξ n then 1 else 0)

lemma level_step {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool) (n : ℕ) :
    level run ξ n ≤ level run ξ (n + 1) := by
  rw [level]
  split
  · exact le_rfl
  · exact le_max_left _ _

lemma level_mono {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool) :
    Monotone (level run ξ) :=
  monotone_nat_of_le_succ (level_step run ξ)

structure Causal {Packet : Type*} (run : Scheduler Packet) (N : ℕ) : Prop where
  snapshot : ∀ ξ n s, n < N → observed run ξ n = some s →
    s.launchPrefix ≤ n ∧ s.source ≤ level run ξ s.launchPrefix
  launchNonneg : ∀ ξ n s, n < N → observed run ξ n = some s → 0 ≤ s.launch
  service : ∀ ξ n s, n < N → observed run ξ n = some s → s.launch ≤ s.finish
  delivered : ∀ ξ n s, n < N → observed run ξ n = some s →
    ∀ i t, i < s.launchPrefix → observed run ξ i = some t → t.finish ≤ s.launch
  ordered : ∀ ξ i j s t, i ≤ j → j < N → observed run ξ i = some s →
    observed run ξ j = some t → s.finish ≤ t.finish
  atomic : ∀ ξ i j s t, i < N → j < N → observed run ξ i = some s → observed run ξ j = some t →
    s.packet = t.packet → s.source = t.source

lemma level_jump {Packet : Type*} {run : Scheduler Packet} {N : ℕ} (hc : Causal run N)
    (ξ : ℕ → Bool) (n : ℕ) (hn : n < N) : level run ξ (n + 1) ≤ level run ξ n + 1 := by
  rw [level]
  split
  · omega
  next s hs =>
    have h := hc.snapshot ξ n s hn hs
    have hle := h.2.trans (level_mono run ξ h.1)
    apply max_le (by omega)
    split <;> omega

lemma jump_witness {Packet : Type*} {run : Scheduler Packet} {N : ℕ} (hc : Causal run N)
    (ξ : ℕ → Bool) (n : ℕ) (hn : n < N) (h : level run ξ n < level run ξ (n + 1)) :
    ∃ s, observed run ξ n = some s ∧ s.source = level run ξ n ∧ ξ n = true := by
  rw [level] at h
  split at h
  · omega
  next s hs =>
    have hsrc := hc.snapshot ξ n s hn hs
    have hle := hsrc.2.trans (level_mono run ξ hsrc.1)
    by_cases ht : ξ n
    · refine ⟨s, hs, ?_, ht⟩
      rw [ite_eq_left ht] at h
      omega
    · rw [ite_eq_right ht, Nat.add_zero, max_eq_left hle] at h
      omega

lemma level_congr {Packet : Type*} (run : Scheduler Packet) (ξ ζ : ℕ → Bool)
    (n : ℕ) (h : ∀ j < n, ξ j = ζ j) : level run ξ n = level run ζ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : observed run ξ n = observed run ζ n := by
      unfold observed
      congr 1
      funext i
      exact h i (i.isLt.trans (Nat.lt_succ_self _))
    rw [level, level, he, ih (fun j hj => h j (hj.trans (Nat.lt_succ_self _))),
      h n (Nat.lt_succ_self _)]

lemma reach_exists {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool) (N k : ℕ)
    (hk : 0 < k) (h : k ≤ level run ξ N) :
    ∃ i, i < N ∧ k ≤ level run ξ (i + 1) := by
  cases N with
  | zero =>
    rw [level] at h
    omega
  | succ n => exact ⟨n, Nat.lt_succ_self _, h⟩

noncomputable def witness {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool)
    (N k : ℕ) (hk : 0 < k) (h : k ≤ level run ξ N) : ℕ :=
  Nat.find (reach_exists run ξ N k hk h)

lemma witness_spec {Packet : Type*} {run : Scheduler Packet} {N k : ℕ} (hc : Causal run N)
    (ξ : ℕ → Bool) (hk : 0 < k) (h : k ≤ level run ξ N) :
    let i := witness run ξ N k hk h
    i < N ∧ level run ξ i + 1 = k ∧ ∃ s, observed run ξ i = some s ∧
      s.source + 1 = k ∧ ξ i = true := by
  let i := witness run ξ N k hk h
  have hi : i < N ∧ k ≤ level run ξ (i + 1) := Nat.find_spec (reach_exists run ξ N k hk h)
  have hprev : level run ξ i < k := by
    by_contra! hh
    by_cases he : i = 0
    · rw [he, level] at hh
      omega
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero he
      change i = j + 1 at hj
      have hj' : j < i := by omega
      have hmin := Nat.find_min (reach_exists run ξ N k hk h) hj'
      exact hmin ⟨hj'.trans hi.1, by rwa [← hj]⟩
  have hjump := level_jump hc ξ i hi.1
  have he : level run ξ i + 1 = k := by omega
  obtain ⟨s, hs, hsource, hbit⟩ := jump_witness hc ξ i hi.1 (by omega)
  exact ⟨hi.1, he, s, hs, by rw [hsource, he], hbit⟩

lemma witness_before_prefix {Packet : Type*} {run : Scheduler Packet} {N k : ℕ}
    (ξ : ℕ → Bool) (hk : 0 < k) (h : k ≤ level run ξ N) (r : ℕ) (hr : r ≤ N)
    (hlevel : k ≤ level run ξ r) : witness run ξ N k hk h < r := by
  have hpos : 0 < r := by
    by_contra! he
    have he' : r = 0 := by omega
    rw [he', level] at hlevel
    omega
  have h : witness run ξ N k hk h ≤ r - 1 :=
    Nat.find_min' (reach_exists run ξ N k hk h) (show r - 1 < N ∧ k ≤ level run ξ (r - 1 + 1) from
      ⟨by omega, by simpa only [show r - 1 + 1 = r by omega] using hlevel⟩)
  omega

lemma witness_strict {Packet : Type*} {run : Scheduler Packet} {N k l : ℕ}
    (hc : Causal run N) (ξ : ℕ → Bool) (hk : 0 < k) (hkl : k < l)
    (hr : l ≤ level run ξ N) :
    witness run ξ N k hk (hkl.le.trans hr) < witness run ξ N l (hk.trans hkl) hr := by
  have hl := witness_spec hc ξ (hk.trans hkl) hr
  have hlevel : k ≤ level run ξ (witness run ξ N l (hk.trans hkl) hr) := by
    dsimp only at hl
    omega
  exact witness_before_prefix ξ hk _ _ (Nat.le_of_lt hl.1) hlevel

noncomputable def reachSlot {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool)
    (N k : ℕ) : Option (Slot Packet) :=
  if h : 0 < k ∧ k ≤ level run ξ N then observed run ξ (witness run ξ N k h.1 h.2) else none

noncomputable def reachTime {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool)
    (N k : ℕ) : ℝ := ((reachSlot run ξ N k).map Slot.finish).getD 0

lemma reachTime_zero {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool) (N : ℕ) :
    reachTime run ξ N 0 = 0 := by simp [reachTime, reachSlot]

lemma reached_slot {Packet : Type*} {run : Scheduler Packet} {N k : ℕ}
    (hc : Causal run N) (ξ : ℕ → Bool) (hk : 0 < k) (h : k ≤ level run ξ N) :
    ∃ s, observed run ξ (witness run ξ N k hk h) = some s ∧
      s.source + 1 = k ∧ ξ (witness run ξ N k hk h) = true ∧ reachTime run ξ N k = s.finish := by
  obtain ⟨_, _, s, hobs, hsrc, hbit⟩ := witness_spec hc ξ hk h
  refine ⟨s, hobs, hsrc, hbit, ?_⟩
  unfold reachTime reachSlot
  rw [dite_eq_left (And.intro hk h), hobs]
  rfl

lemma reach_before_launch {Packet : Type*} {run : Scheduler Packet} {N n : ℕ}
    (hc : Causal run N) (ξ : ℕ → Bool) (hn : n < N) (s : Slot Packet)
    (hs : observed run ξ n = some s) :
    reachTime run ξ N s.source ≤ s.launch := by
  by_cases hz : s.source = 0
  · rw [hz, reachTime_zero]
    exact hc.launchNonneg ξ n s hn hs
  have hpos := Nat.pos_of_ne_zero hz
  have h := hc.snapshot ξ n s hn hs
  have hN : s.launchPrefix ≤ N := h.1.trans hn.le
  have hreach := h.2.trans (level_mono run ξ hN)
  have hj := witness_before_prefix ξ hpos hreach s.launchPrefix hN h.2
  obtain ⟨t, ht, _, _, htime⟩ := reached_slot hc ξ hpos hreach
  rw [htime]
  exact hc.delivered ξ n s hn hs _ t hj ht

lemma reach_ordered {Packet : Type*} {run : Scheduler Packet} {N k l : ℕ}
    (hc : Causal run N) (ξ : ℕ → Bool) (hkl : k ≤ l) (hl : l ≤ level run ξ N) :
    reachTime run ξ N k ≤ reachTime run ξ N l := by
  by_cases he : k = l
  · rw [he]
  have hlt : k < l := lt_of_le_of_ne hkl he
  have hpos : 0 < l := Nat.zero_lt_of_lt hlt
  obtain ⟨b, hb, _, _, hbt⟩ := reached_slot hc ξ hpos hl
  have hbi := (witness_spec hc ξ hpos hl).1
  by_cases hz : k = 0
  · rw [hz, reachTime_zero, hbt]
    exact (hc.launchNonneg ξ _ b hbi hb).trans (hc.service ξ _ b hbi hb)
  have hkp := Nat.pos_of_ne_zero hz
  obtain ⟨a, ha, _, _, hat⟩ := reached_slot hc ξ hkp (hkl.trans hl)
  rw [hat, hbt]
  exact hc.ordered ξ _ _ a b (witness_strict hc ξ hkp hlt hl).le hbi ha hb

def extend {n : ℕ} (ξ : Fin n → Bool) (j : ℕ) : Bool :=
  if h : j < n then ξ ⟨j, h⟩ else false

lemma extend_past (ξ : ℕ → Bool) {n j : ℕ} (hj : j < n) :
    extend (past n ξ) j = ξ j := by simp [extend, hj, past]

lemma observed_prefix {Packet : Type*} (run : Scheduler Packet) (ξ ζ : ℕ → Bool)
    (j : ℕ) (h : ∀ i < j, ξ i = ζ i) :
    observed run ξ j = observed run ζ j := by
  unfold observed
  congr 1
  funext i
  exact h i i.isLt

lemma reach_slot_stable {Packet : Type*} (run : Scheduler Packet) (ξ ζ : ℕ → Bool) (k n N : ℕ)
    (hn : n ≤ N) (he : ∀ j < n, ξ j = ζ j) (hk : k ≤ level run ξ n) :
    reachSlot run ξ N k = reachSlot run ζ n k := by
  by_cases hz : k = 0
  · subst k
    simp [reachSlot]
  have hpos := Nat.pos_of_ne_zero hz
  have hζ : k ≤ level run ζ n := (level_congr run ξ ζ n he) ▸ hk
  have hξ := hk.trans (level_mono run ξ hn)
  let i := witness run ξ N k hpos hξ
  let j := witness run ζ n k hpos hζ
  have hi : i < n := witness_before_prefix ξ hpos hξ n hn hk
  have hj : j < n ∧ k ≤ level run ζ (j + 1) := Nat.find_spec (reach_exists run ζ n k hpos hζ)
  have hx : i < N ∧ k ≤ level run ξ (i + 1) := Nat.find_spec (reach_exists run ξ N k hpos hξ)
  have hji : j ≤ i := Nat.find_min' (reach_exists run ζ n k hpos hζ)
    ⟨hi, (level_congr run ξ ζ (i + 1) (fun a ha => he a (by omega))) ▸ hx.2⟩
  have hij : i ≤ j := Nat.find_min' (reach_exists run ξ N k hpos hξ)
    ⟨hj.1.trans_le hn, (level_congr run ξ ζ (j + 1) (fun a ha => he a (by omega))).symm ▸ hj.2⟩
  have heq : i = j := le_antisymm hij hji
  unfold reachSlot
  rw [dite_eq_left (And.intro hpos hξ), dite_eq_left (And.intro hpos hζ)]
  change observed run ξ i = observed run ζ j
  rw [heq, observed_prefix run ξ ζ j (fun a ha => he a (ha.trans hj.1))]

lemma reach_stable {Packet : Type*} (run : Scheduler Packet) (ξ ζ : ℕ → Bool) (k n N : ℕ)
    (hn : n ≤ N) (he : ∀ j < n, ξ j = ζ j) (hk : k ≤ level run ξ n) :
    reachTime run ξ N k = reachTime run ζ n k :=
  congrArg (fun z : Option (Slot Packet) => (z.map Slot.finish).getD 0)
    (reach_slot_stable run ξ ζ k n N hn he hk)

lemma level_measurable {Packet : Type*} (run : Scheduler Packet) (N : ℕ) :
    Measurable (fun ξ => level run ξ N) := by
  have h : (fun ξ => level run ξ N) = (fun η : Fin N → Bool => level run (extend η) N) ∘ past N :=
    funext (fun ξ => level_congr run ξ (extend (past N ξ)) N (fun _ hi => (extend_past ξ hi).symm))
  rw [h]
  exact (measurable_of_countable _).comp (measurable_past N)

lemma reach_eq_extend {Packet : Type*} (run : Scheduler Packet) (ξ : ℕ → Bool) (N k : ℕ) :
    reachSlot run ξ N k = reachSlot run (extend (past N ξ)) N k := by
  have hp : ∀ i < N, ξ i = extend (past N ξ) i := fun _ hi => (extend_past ξ hi).symm
  by_cases hk : k ≤ level run ξ N
  · exact reach_slot_stable run ξ (extend (past N ξ)) k N N le_rfl hp hk
  · have hk' : ¬ k ≤ level run (extend (past N ξ)) N := by
      rw [← level_congr run ξ (extend (past N ξ)) N hp]
      exact hk
    simp [reachSlot, hk, hk']

lemma reach_observable {Packet : Type*} {X : Type*} [MeasurableSpace X]
    (run : Scheduler Packet) (N k : ℕ) (f : Option (Slot Packet) → X) :
    Measurable (fun ξ => f (reachSlot run ξ N k)) := by
  have h : (fun ξ => f (reachSlot run ξ N k)) =
      (fun η : Fin N → Bool => f (reachSlot run (extend η) N k)) ∘ past N :=
    funext (fun ξ => congrArg f (reach_eq_extend run ξ N k))
  rw [h]
  exact (measurable_of_countable _).comp (measurable_past N)

def eligibility {Packet : Type*} (run : Scheduler Packet) (keep : Slot Packet → Prop)
    (m : ℕ) (ℓ : ℝ) (n : ℕ) : Set (Fin n → Bool) :=
  {η | ∃ s, run n η = some s ∧ level run (extend η) n = m ∧ s.source = m ∧
    keep s ∧ s.finish ≤ reachTime run (extend η) n m + ℓ}

lemma eligible_iff {Packet : Type*} (run : Scheduler Packet) (keep : Slot Packet → Prop)
    (ξ : ℕ → Bool) (m : ℕ) (ℓ : ℝ) {n N : ℕ} (hn : n ≤ N) :
    past n ξ ∈ eligibility run keep m ℓ n ↔
    ∃ s, observed run ξ n = some s ∧ level run ξ n = m ∧ s.source = m ∧
      keep s ∧ s.finish ≤ reachTime run ξ N m + ℓ := by
  have hcon : ∀ j < n, ξ j = extend (past n ξ) j := fun _ hj => (extend_past ξ hj).symm
  have hl := level_congr run ξ (extend (past n ξ)) n hcon
  constructor
  · rintro ⟨s, hs, hlevel, hsource, hkeep, ht⟩
    have he : level run ξ n = m := hl.trans hlevel
    exact ⟨s, hs, he, hsource, hkeep,
      (reach_stable run ξ (extend (past n ξ)) m n N hn hcon he.ge).symm ▸ ht⟩
  · rintro ⟨s, hs, hlevel, hsource, hkeep, ht⟩
    exact ⟨s, hs, hl.symm.trans hlevel, hsource, hkeep,
      (reach_stable run ξ (extend (past n ξ)) m n N hn hcon hlevel.ge) ▸ ht⟩

lemma witness_eligible {Packet : Type*} {run : Scheduler Packet} {N m : ℕ} (hc : Causal run N)
    (ξ : ℕ → Bool) (hr : m + 1 ≤ level run ξ N) (keep : Slot Packet → Prop) (ℓ : ℝ)
    (ht : reachTime run ξ N (m + 1) - reachTime run ξ N m ≤ ℓ)
    (hkeep : ∀ s, observed run ξ (witness run ξ N (m + 1) (Nat.succ_pos _) hr) = some s → keep s) :
    ∃ n < N, past n ξ ∈ eligibility run keep m ℓ n ∧ ξ n = true := by
  let n := witness run ξ N (m + 1) (Nat.succ_pos _) hr
  obtain ⟨hn, hlevel, _⟩ := witness_spec hc ξ (Nat.succ_pos _) hr
  obtain ⟨s, hs, hsrc, hbit, htime⟩ := reached_slot hc ξ (Nat.succ_pos _) hr
  refine ⟨n, hn, (eligible_iff run keep ξ m ℓ hn.le).2 ⟨s, hs, ?_, by omega, hkeep s hs, ?_⟩, hbit⟩
  · omega
  · rw [htime] at ht
    linarith

end LongTails.Proofs.BirchResourceHardRun
