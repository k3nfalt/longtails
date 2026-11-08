import LongTails.Setups.BirchPowerTime
import LongTails.Proofs.BirchResourceWindow

namespace LongTails.Proofs.BirchPowerTime

open Finset Set LongTails.Setups.BirchPowerTime
open LongTails.Proofs.BirchResourceWindow (interval_capacity)

lemma rate_le_envelope {Mode Device : Type*} [Fintype Mode] (p : Profile Mode Device)
    (t : ℝ) (u : ℕ) (s : Finset Mode) (hs : Admitted p t u s) :
    rate p s ≤ envelope p t u := by
  classical
  exact Finset.le_sup' (f := rate p) (mem_insert_of_mem (by simp [hs]))

lemma window_capacity {Mode Device J : Type*} [Fintype Mode] (p : Profile Mode Device)
    (hp : p.Valid) (jobs : J → Job Mode) (s : Finset J) (T : ℝ) (u : ℕ) (hT : 0 ≤ T)
    (hl : Legal p jobs s)
    (htime : ∀ j ∈ s, 0 ≤ (jobs j).launch ∧ (jobs j).launch + p.duration (jobs j).mode ≤ T)
    (hsize : ∀ j ∈ s, p.samples (jobs j).mode ≤ u) :
    (∑ j ∈ s, (p.samples (jobs j).mode : ℝ)) ≤ T * envelope p T u := by
  classical
  let m := fun j => (jobs j).mode
  let a := fun j => (jobs j).launch
  let b := fun j => a j + p.duration (m j)
  let v := fun j => (p.samples (m j) : ℝ) / p.duration (m j)
  have ht (j : J) (hj : j ∈ s) : 0 ≤ a j ∧ a j ≤ b j ∧ b j ≤ T :=
    ⟨(htime j hj).1, le_add_of_nonneg_right (hp.1 _).1.le, (htime j hj).2⟩
  have hc (t : ℝ) (_ : t ∈ Ico (0 : ℝ) T) :
      (∑ j ∈ s, (Ico (a j) (b j)).indicator (fun _ => v j) t) ≤ envelope p T u := by
    let active := s.filter (fun j => (jobs j).active p t)
    let modes := active.image m
    have hd (j : J) (hj : j ∈ active) (k : J) (hk : k ∈ active)
        (he : p.device (m j) = p.device (m k)) : j = k :=
      (hl t).1 j (mem_filter.mp hj).1 k (mem_filter.mp hk).1
        (mem_filter.mp hj).2 (mem_filter.mp hk).2 he
    have hi : Set.InjOn m (active : Set J) := fun j hj k hk h =>
      hd j hj k hk (congrArg p.device h)
    have had : Admitted p T u modes := by
      refine ⟨?_, ?_, ?_⟩
      · intro i hi' k hk' he
        obtain ⟨j, hj, rfl⟩ := mem_image.mp (show i ∈ modes from hi')
        obtain ⟨l, hl', rfl⟩ := mem_image.mp (show k ∈ modes from hk')
        rw [hd j hj l hl' he]
      · dsimp only [modes]
        rw [sum_image (fun _ hj _ hk he => hi hj hk he)]
        change (∑ j ∈ s.filter (fun j => (jobs j).active p t), p.power (m j)) ≤ _
        rw [sum_filter]
        exact (hl t).2
      · intro i hi'
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hi'
        have hj' := (mem_filter.mp hj).1
        exact ⟨by have := htime j hj'; dsimp only [m]; linarith [this.1, this.2], hsize j hj'⟩
    apply le_trans _ (rate_le_envelope p T u modes had)
    unfold rate
    dsimp only [modes]
    rw [sum_image (fun _ hj _ hk he => hi hj hk he)]
    change _ ≤ ∑ j ∈ s.filter (fun j => (jobs j).active p t), v j
    rw [sum_filter]
    apply le_of_eq
    apply sum_congr rfl
    intro j _
    by_cases hj : (jobs j).active p t
    · have h' : t ∈ Ico (a j) (b j) := hj
      rw [indicator_of_mem h', ite_eq_left hj]
    · have h' : t ∉ Ico (a j) (b j) := hj
      rw [indicator_of_notMem h', ite_eq_right hj]
  have hh := interval_capacity s a b v T (envelope p T u) hT ht hc
  convert hh using 1
  apply sum_congr rfl
  intro j _
  dsimp only [b, v, m]
  rw [add_sub_cancel_left]
  field_simp [(hp.1 (jobs j).mode).1.ne']

noncomputable def batchCapacity {Mode Device : Type*} (p : Profile Mode Device)
    (s : Finset Mode) (T : ℝ) : ℕ :=
  ∑ i ∈ s, p.samples i * ⌊T / p.duration i⌋₊

lemma repeated_configuration {Mode Device : Type*} (p : Profile Mode Device) (hp : p.Valid)
    (s : Finset Mode) (t : ℝ) (u B : ℕ) (hs : Admitted p t u s) (hr : 0 < rate p s) :
    B ≤ batchCapacity p s (t + (B : ℝ) / rate p s) := by
  let T := t + (B : ℝ) / rate p s
  have he : (∑ i ∈ s, (T - t) * ((p.samples i : ℝ) / p.duration i)) = B := by
    rw [← mul_sum]
    change (T - t) * rate p s = _
    dsimp only [T]
    rw [add_sub_cancel_left, div_mul_cancel₀ _ hr.ne']
  have hh : (∑ i ∈ s, (T - t) * ((p.samples i : ℝ) / p.duration i)) ≤
      ∑ i ∈ s, (p.samples i : ℝ) * (⌊T / p.duration i⌋₊ : ℝ) := by
    apply sum_le_sum
    intro i hi
    have hd := (hp.1 i).1
    have ht := (hs.2.2 i hi).1
    have h₁ := Nat.lt_floor_add_one (T / p.duration i)
    have h₂ : 1 ≤ t / p.duration i := (le_div_iff₀ hd).2 (by simpa using ht)
    have h₃ : (T - t) / p.duration i ≤ (⌊T / p.duration i⌋₊ : ℝ) := by
      rw [sub_div]
      linarith only [h₁, h₂]
    have h₄ := mul_le_mul_of_nonneg_left h₃ (Nat.cast_nonneg (p.samples i) : (0 : ℝ) ≤ p.samples i)
    calc
      _ = (p.samples i : ℝ) * ((T - t) / p.duration i) := by ring
      _ ≤ _ := h₄
  rw [he] at hh
  unfold batchCapacity
  exact_mod_cast hh

noncomputable def planned {Mode Device : Type*} (p : Profile Mode Device)
    (s : Finset Mode) (T : ℝ) : Finset (Σ _ : Mode, ℕ) :=
  s.sigma (fun i => range ⌊T / p.duration i⌋₊)

def scheduled {Mode Device : Type*} (p : Profile Mode Device) (j : Σ _ : Mode, ℕ) : Job Mode :=
  ⟨j.1, (j.2 : ℝ) * p.duration j.1⟩

lemma planned_capacity {Mode Device : Type*} (p : Profile Mode Device)
    (s : Finset Mode) (T : ℝ) :
    (∑ j ∈ planned p s T, p.samples (scheduled p j).mode) = batchCapacity p s T := by
  simp [planned, scheduled, batchCapacity, sum_sigma, Nat.mul_comm]

lemma choose_quota {J : Type*} (s : Finset J) (weight : J → ℕ) (B u : ℕ)
    (hw : ∀ j ∈ s, weight j ≤ u) (hB : B ≤ ∑ j ∈ s, weight j) :
    ∃ cut ⊆ s, B ≤ (∑ j ∈ cut, weight j) ∧ (∑ j ∈ cut, weight j) ≤ B + u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨∅, Finset.Subset.rfl, hB, by simp⟩
  | @insert j s hj ih =>
    by_cases hs : B ≤ ∑ k ∈ s, weight k
    · obtain ⟨cut, hc, hlow, hhigh⟩ := ih (fun k hk => hw k (mem_insert_of_mem hk)) hs
      exact ⟨cut, hc.trans (subset_insert _ _), hlow, hhigh⟩
    · refine ⟨insert j s, Finset.Subset.rfl, hB, ?_⟩
      have hj' := hw j (mem_insert_self _ _)
      rw [sum_insert hj]
      omega

lemma scheduled_valid {Mode Device : Type*} (p : Profile Mode Device) (hp : p.Valid)
    (modes : Finset Mode) (t : ℝ) (u : ℕ) (hm : Admitted p t u modes)
    (T : ℝ) (hT : 0 ≤ T) (s : Finset (Σ _ : Mode, ℕ)) (hs : s ⊆ planned p modes T) :
    Legal p (scheduled p) s ∧
      ∀ j ∈ s, 0 ≤ (scheduled p j).launch ∧
        (scheduled p j).launch + p.duration (scheduled p j).mode ≤ T := by
  classical
  have hm' (j) (hj : j ∈ s) : j.1 ∈ modes ∧ j.2 < ⌊T / p.duration j.1⌋₊ := by
    simpa only [planned, mem_sigma, Finset.mem_range] using hs hj
  have htime (j) (hj : j ∈ s) : 0 ≤ (scheduled p j).launch ∧
      (scheduled p j).launch + p.duration (scheduled p j).mode ≤ T := by
    have hd := (hp.1 j.1).1
    have hh : j.2 + 1 ≤ ⌊T / p.duration j.1⌋₊ := (hm' j hj).2
    have h₁ : (j.2 : ℝ) + 1 ≤ (⌊T / p.duration j.1⌋₊ : ℝ) := by exact_mod_cast hh
    have h₂ := Nat.floor_le (div_nonneg hT hd.le)
    have h₃ := (le_div_iff₀ hd).mp (h₁.trans h₂)
    exact ⟨mul_nonneg (Nat.cast_nonneg _) hd.le, by
      change (j.2 : ℝ) * p.duration j.1 + p.duration j.1 ≤ T
      linarith only [h₃]⟩
  refine ⟨?_, htime⟩
  intro v
  have huniq (j) (hj : j ∈ s) (k) (hk : k ∈ s)
      (hja : (scheduled p j).active p v) (hka : (scheduled p k).active p v)
      (he : p.device j.1 = p.device k.1) : j = k := by
    rcases j with ⟨i, j⟩
    rcases k with ⟨i', k⟩
    have hii := hm.1 (show i ∈ (modes : Set Mode) from (hm' _ hj).1)
      (show i' ∈ (modes : Set Mode) from (hm' _ hk).1) he
    subst i'
    change v ∈ Ico ((j : ℝ) * p.duration i) ((j : ℝ) * p.duration i + p.duration i) at hja
    change v ∈ Ico ((k : ℝ) * p.duration i) ((k : ℝ) * p.duration i + p.duration i) at hka
    have hd := (hp.1 i).1.le
    have hne (n m : ℕ) (hnm : n < m) :
        (n : ℝ) * p.duration i + p.duration i ≤ (m : ℝ) * p.duration i := by
      have hh : n + 1 ≤ m := hnm
      have hh' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hh
      simpa only [add_mul, one_mul] using mul_le_mul_of_nonneg_right hh' hd
    rcases lt_trichotomy j k with h | rfl | h
    · exact False.elim ((not_lt_of_ge ((hne j k h).trans hka.1)) hja.2)
    · rfl
    · exact False.elim ((not_lt_of_ge ((hne k j h).trans hja.1)) hka.2)
  refine ⟨huniq, ?_⟩
  let active := s.filter (fun j => (scheduled p j).active p v)
  have hsub : active.image Sigma.fst ⊆ modes := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    exact (hm' j (mem_filter.mp hj).1).1
  have hinj : Set.InjOn (Sigma.fst : (Σ _ : Mode, ℕ) → Mode) (active : Set _) := by
    intro j hj k hk he
    exact huniq j (mem_filter.mp hj).1 k (mem_filter.mp hk).1
      (mem_filter.mp hj).2 (mem_filter.mp hk).2 (congrArg p.device he)
  change (∑ j ∈ s, if (scheduled p j).active p v then p.power j.1 else 0) ≤ p.cap
  rw [← sum_filter]
  change (∑ j ∈ active, p.power j.1) ≤ _
  rw [← sum_image (fun _ hj _ hk he => hinj hj hk he)]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (hp.1 i).2.2)).trans hm.2.1

lemma exists_power_phase {Mode Device : Type*} (p : Profile Mode Device) (hp : p.Valid)
    (modes : Finset Mode) (t : ℝ) (u B : ℕ) (hm : Admitted p t u modes) (hr : 0 < rate p modes) :
    let T := t + (B : ℝ) / rate p modes
    ∃ s : Finset (Σ _ : Mode, ℕ), Legal p (scheduled p) s ∧
      (∀ j ∈ s, 0 ≤ (scheduled p j).launch ∧
        (scheduled p j).launch + p.duration (scheduled p j).mode ≤ T) ∧
      B ≤ (∑ j ∈ s, p.samples (scheduled p j).mode) ∧
      (∑ j ∈ s, p.samples (scheduled p j).mode) ≤ B + u := by
  let T := t + (B : ℝ) / rate p modes
  have ht : 0 ≤ t := by
    by_contra! h
    have he : modes = ∅ := Finset.eq_empty_iff_forall_notMem.2 (fun i hi =>
      (not_le_of_gt ((hp.1 i).1.trans' h)) (hm.2.2 i hi).1)
    simp [he, rate] at hr
  have hT : 0 ≤ T := add_nonneg ht (div_nonneg (Nat.cast_nonneg _) hr.le)
  have hcount := repeated_configuration p hp modes t u B hm hr
  have hwork (j) (hj : j ∈ planned p modes T) : p.samples (scheduled p j).mode ≤ u :=
    (hm.2.2 j.1 (mem_sigma.mp hj).1).2
  obtain ⟨s, hs, hlo, hhi⟩ := choose_quota (planned p modes T)
    (fun j => p.samples (scheduled p j).mode) B u hwork
    (by rw [planned_capacity]; exact hcount)
  have h := scheduled_valid p hp modes t u hm T hT s hs
  exact ⟨s, h.1, h.2, hlo, hhi⟩

lemma exact_quota {Job : Type*} (s : Finset Job) (weight : Job → ℕ) (B u : ℕ)
    (hw : ∀ j ∈ s, 0 < weight j ∧ weight j ≤ u) (hB : B ≤ ∑ j ∈ s, weight j) :
    ∃ (cut : Finset Job) (accepted : Job → ℕ), cut ⊆ s ∧
      (∀ j ∈ cut, 0 < accepted j ∧ accepted j ≤ weight j) ∧
      (∑ j ∈ cut, accepted j) = B ∧ (∑ j ∈ cut, weight j) ≤ B + u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨∅, fun _ => 0, Finset.Subset.rfl, by simp, by simpa using (Nat.eq_zero_of_le_zero hB).symm, by simp⟩
  | @insert j s hj ih =>
    by_cases hs : B ≤ ∑ k ∈ s, weight k
    · obtain ⟨cut, accept, hc, hpos, hsum, hpaid⟩ :=
        ih (fun k hk => hw k (mem_insert_of_mem hk)) hs
      exact ⟨cut, accept, hc.trans (subset_insert _ _), hpos, hsum, hpaid⟩
    · let S := ∑ k ∈ s, weight k
      let accept := Function.update weight j (B - S)
      have hj' := (hw j (mem_insert_self _ _)).2
      have hsum : ∑ k ∈ s, accept k = S :=
        sum_congr rfl (fun k hk => Function.update_of_ne (show k ≠ j from fun he => hj (he ▸ hk)) _ _)
      have hB' : B ≤ weight j + S := by rwa [sum_insert hj] at hB
      refine ⟨insert j s, accept, Finset.Subset.rfl, ?_, ?_, ?_⟩
      · intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · dsimp [accept]
          rw [Function.update_self]
          omega
        · change 0 < Function.update weight j (B - S) k ∧
            Function.update weight j (B - S) k ≤ weight k
          rw [Function.update_of_ne (show k ≠ j from fun he => hj (he ▸ hk))]
          exact ⟨(hw k (mem_insert_of_mem hk)).1, le_rfl⟩
      · rw [sum_insert hj, hsum]
        change Function.update weight j (B - S) j + S = B
        rw [Function.update_self]
        omega
      · rw [sum_insert hj]
        change weight j + S ≤ B + u
        omega

lemma envelope_attained {Mode Device : Type*} [Fintype Mode] (p : Profile Mode Device)
    (hp : p.Valid) (t : ℝ) (u : ℕ) :
    ∃ modes, Admitted p t u modes ∧ rate p modes = envelope p t u := by
  classical
  let configs := insert (∅ : Finset Mode) (univ.powerset.filter (Admitted p t u))
  have hn : configs.Nonempty := ⟨∅, mem_insert_self _ _⟩
  obtain ⟨modes, hm, he⟩ := Finset.exists_mem_eq_sup' hn (rate p)
  refine ⟨modes, ?_, he.symm⟩
  rcases mem_insert.mp hm with rfl | hm
  · refine ⟨?_, ?_, ?_⟩ <;> simp [hp.2]
  · exact (mem_filter.mp hm).2

lemma exists_power_envelope_phase {Mode Device : Type*} [Fintype Mode]
    (p : Profile Mode Device) (hp : p.Valid) (t : ℝ) (u B : ℕ) (hr : 0 < envelope p t u) :
    let T := t + (B : ℝ) / envelope p t u
    ∃ s : Finset (Σ _ : Mode, ℕ), Legal p (scheduled p) s ∧
      (∀ j ∈ s, 0 ≤ (scheduled p j).launch ∧
        (scheduled p j).launch + p.duration (scheduled p j).mode ≤ T) ∧
      B ≤ (∑ j ∈ s, p.samples (scheduled p j).mode) ∧
      (∑ j ∈ s, p.samples (scheduled p j).mode) ≤ B + u := by
  obtain ⟨modes, hm, he⟩ := envelope_attained p hp t u
  have h := exists_power_phase p hp modes t u B hm (he ▸ hr)
  simpa only [he] using h

lemma benchmark_phase {Mode Device J : Type*} [Fintype Mode] (p : Profile Mode Device)
    (hp : p.Valid) (jobs : J → Job Mode) (s : Finset J) (T : ℝ) (u B : ℕ)
    (hB : 0 < B) (hT : 0 < T) (hl : Legal p jobs s)
    (htime : ∀ j ∈ s, 0 ≤ (jobs j).launch ∧ (jobs j).launch + p.duration (jobs j).mode ≤ T)
    (hsize : ∀ j ∈ s, p.samples (jobs j).mode ≤ u)
    (hwork : B ≤ ∑ j ∈ s, p.samples (jobs j).mode) :
    ∃ selected : Finset (Σ _ : Mode, ℕ), Legal p (scheduled p) selected ∧
      (∀ j ∈ selected, 0 ≤ (scheduled p j).launch ∧
        (scheduled p j).launch + p.duration (scheduled p j).mode ≤ 2 * T) ∧
      B ≤ (∑ j ∈ selected, p.samples (scheduled p j).mode) ∧
      (∑ j ∈ selected, p.samples (scheduled p j).mode) ≤ B + u := by
  have hb : (B : ℝ) ≤ T * envelope p T u := by
    refine le_trans ?_ (window_capacity p hp jobs s T u hT.le hl htime hsize)
    exact_mod_cast hwork
  have hr : 0 < envelope p T u :=
    pos_of_mul_pos_right ((Nat.cast_pos.mpr hB).trans_le hb) hT.le
  obtain ⟨ss, hlegal, htime', hlo, hhi⟩ := exists_power_envelope_phase p hp T u B hr
  have hdiv : (B : ℝ) / envelope p T u ≤ T := (div_le_iff₀ hr).2 hb
  exact ⟨ss, hlegal, fun j hj => ⟨(htime' j hj).1, (htime' j hj).2.trans (by linarith)⟩,
    hlo, hhi⟩

end LongTails.Proofs.BirchPowerTime
