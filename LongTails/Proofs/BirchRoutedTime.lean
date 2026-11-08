import LongTails.Setups.BirchRoutedTime
import LongTails.Proofs.BirchResourceWindow

namespace LongTails.Proofs.BirchRoutedTime

open Finset Set LongTails.Setups.BirchRoutedTime
open LongTails.Proofs.BirchResourceWindow (interval_capacity)

lemma offset_bounds {Route Device : Type*} [DecidableEq Device] (p : Profile Route Device)
    (hp : ∀ i, 0 ≤ p.duration i) (r : Route) (i : Device) (hi : i ∈ p.path r) :
    0 ≤ offset p r i ∧ offset p r i + p.duration i ≤ latency p r := by
  have hidx := List.idxOf_lt_length_of_mem hi
  have hnonneg (l : List Device) : 0 ≤ (l.map p.duration).sum := by
    exact List.sum_nonneg (fun _ hx => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact hp j)
  refine ⟨hnonneg _, ?_⟩
  have he : (((p.path r).take ((p.path r).idxOf i + 1)).map p.duration).sum =
      offset p r i + p.duration i := by
    rw [List.take_succ_eq_append_getElem hidx, List.getElem_idxOf, List.map_append, List.sum_append]
    simp [offset]
  rw [← he]
  have hh := congrArg (fun l : List Device => (l.map p.duration).sum)
    (List.take_append_drop ((p.path r).idxOf i + 1) (p.path r))
  rw [List.map_append, List.sum_append] at hh
  unfold latency
  linarith only [hh, hnonneg ((p.path r).drop ((p.path r).idxOf i + 1))]

lemma device_load {Route Device J : Type*} [DecidableEq Device] (p : Profile Route Device)
    (hd : ∀ i, 0 ≤ p.duration i) (jobs : J → Job Route) (s : Finset J) (T : ℝ) (hT : 0 ≤ T)
    (hl : Legal p jobs s)
    (htime : ∀ j ∈ s, 0 ≤ (jobs j).launch ∧ (jobs j).launch + latency p (jobs j).route ≤ T)
    (i : Device) :
    ((s.filter (fun j => i ∈ p.path (jobs j).route)).card : ℝ) * p.duration i ≤ T := by
  classical
  let uses := s.filter (fun j => i ∈ p.path (jobs j).route)
  let a := fun j => (jobs j).launch + offset p (jobs j).route i
  let b := fun j => a j + p.duration i
  have ht (j : J) (hj : j ∈ uses) : 0 ≤ a j ∧ a j ≤ b j ∧ b j ≤ T := by
    have h := offset_bounds p hd (jobs j).route i (mem_filter.mp hj).2
    have hs := htime j (mem_filter.mp hj).1
    dsimp only [a, b]
    exact ⟨add_nonneg hs.1 h.1, le_add_of_nonneg_right (hd i), by linarith only [hs.2, h.2]⟩
  have hcap (t : ℝ) (_ : t ∈ Ico (0 : ℝ) T) :
      (∑ j ∈ uses, (Ico (a j) (b j)).indicator (fun _ => (1 : ℝ)) t) ≤ 1 := by
    by_cases h : ∃ j ∈ uses, t ∈ Ico (a j) (b j)
    · obtain ⟨j, hj, hjt⟩ := h
      rw [sum_eq_single_of_mem j hj]
      · simp [indicator_of_mem hjt]
      · intro k hk hkj
        apply indicator_of_notMem
        intro hkt
        exact hkj (hl i t k (mem_filter.mp hk).1 j (mem_filter.mp hj).1
          ⟨(mem_filter.mp hk).2, hkt⟩ ⟨(mem_filter.mp hj).2, hjt⟩)
    · rw [sum_eq_zero (fun j hj => indicator_of_notMem (fun hjt => h ⟨j, hj, hjt⟩) _)]
      norm_num
  simpa [b, uses, nsmul_eq_mul] using
    interval_capacity uses a b (fun _ => 1) T 1 hT ht hcap

noncomputable def windowRate {Route J : Type*} [DecidableEq Route]
    (jobs : J → Job Route) (s : Finset J) (T : ℝ) (r : Route) : ℝ :=
  ((s.filter (fun j => (jobs j).route = r)).card : ℝ) / T

lemma route_load_identity {Route Device J : Type*} [Fintype Route] [DecidableEq Route]
    [DecidableEq Device] (p : Profile Route Device) (jobs : J → Job Route) (s : Finset J)
    (i : Device) (T : ℝ) :
    (∑ r, if i ∈ p.path r then windowRate jobs s T r else 0) =
      ((s.filter (fun j => i ∈ p.path (jobs j).route)).card : ℝ) / T := by
  classical
  let uses := s.filter (fun j => i ∈ p.path (jobs j).route)
  have hc : (∑ r : Route, (↑((uses.filter (fun j => (jobs j).route = r)).card) : ℝ)) =
      (uses.card : ℝ) := by
    simpa [nsmul_eq_mul] using (sum_fiberwise_of_maps_to (s := uses) (t := (univ : Finset Route))
      (g := fun j => (jobs j).route) (fun _ _ => mem_univ _) (fun _ => (1 : ℝ)))
  rw [← hc, sum_div]
  apply sum_congr rfl
  intro r _
  by_cases hr : i ∈ p.path r
  · have he : s.filter (fun j => (jobs j).route = r) =
        uses.filter (fun j => (jobs j).route = r) := by
      ext j
      simp only [uses, mem_filter]
      constructor
      · rintro ⟨hj, h⟩
        exact ⟨⟨hj, h ▸ hr⟩, h⟩
      · rintro ⟨⟨hj, _⟩, h⟩
        exact ⟨hj, h⟩
    rw [ite_eq_left hr, windowRate, he]
  · rw [ite_eq_right hr]
    have hz : uses.filter (fun j => (jobs j).route = r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro j hj
      obtain ⟨hs, he⟩ := mem_filter.mp hj
      exact hr (he ▸ (mem_filter.mp hs).2)
    rw [hz, Finset.card_empty, Nat.cast_zero, zero_div]

lemma window_rate_feasible {Route Device J : Type*} [Fintype Route] [DecidableEq Route]
    [DecidableEq Device] (p : Profile Route Device) (hd : ∀ i, 0 ≤ p.duration i)
    (jobs : J → Job Route) (s : Finset J) (T : ℝ) (hT : 0 < T) (hl : Legal p jobs s)
    (htime : ∀ j ∈ s, 0 ≤ (jobs j).launch ∧ (jobs j).launch + latency p (jobs j).route ≤ T) :
    FeasibleRate p T (windowRate jobs s T) := by
  refine ⟨fun _ => by unfold windowRate; positivity, ?_, ?_⟩
  · intro r hr
    have hz : s.filter (fun j => (jobs j).route = r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro j hj
      obtain ⟨hs, he⟩ := mem_filter.mp hj
      obtain ⟨h₁, h₂⟩ := htime j hs
      rw [he] at h₂
      linarith only [hr, h₁, h₂]
    simp [windowRate, hz]
  · intro i
    rw [route_load_identity, ← mul_div_assoc]
    apply (div_le_iff₀ hT).2
    rw [one_mul, mul_comm]
    exact device_load p hd jobs s T hT.le hl htime i

lemma window_rate_sum {Route J : Type*} [Fintype Route] [DecidableEq Route]
    (jobs : J → Job Route) (s : Finset J) (T : ℝ) :
    (∑ r, windowRate jobs s T r) = (s.card : ℝ) / T := by
  unfold windowRate
  rw [← sum_div]
  congr 1
  simpa [nsmul_eq_mul] using (sum_fiberwise_of_maps_to (s := s) (t := (univ : Finset Route))
    (g := fun j => (jobs j).route) (fun _ _ => mem_univ _) (fun _ => (1 : ℝ)))

lemma pack_no_wait {Route Device J : Type*} [DecidableEq Device] (p : Profile Route Device)
    (hd : ∀ i, 0 ≤ p.duration i) (routes : J → Route) (s : Finset J)
    (cap : Device → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hcap : ∀ i, ((s.filter (fun j => i ∈ p.path (routes j))).card : ℝ) * p.duration i ≤ cap i)
    (hroom : ∀ j ∈ s, 2 * (∑ i ∈ (p.path (routes j)).toFinset, cap i) < H) :
    ∃ start : J → ℝ, Legal p (fun j => ⟨routes j, start j⟩) s ∧
      ∀ j ∈ s, start j ∈ Ico (0 : ℝ) H := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp [Legal], by simp⟩
  | @insert j s hj ih =>
    have hcap' (i : Device) :
        ((s.filter (fun j => i ∈ p.path (routes j))).card : ℝ) * p.duration i ≤ cap i := by
      apply (mul_le_mul_of_nonneg_right _ (hd i)).trans (hcap i)
      exact_mod_cast Finset.card_le_card (filter_subset_filter _ (subset_insert j s))
    obtain ⟨old, hold, holdtime⟩ := ih hcap'
      (fun k hk => hroom k (mem_insert_of_mem hk))
    let v := (p.path (routes j)).toFinset
    let blocking : Finset (Σ _ : Device, J) :=
      v.sigma (fun i => s.filter (fun k => i ∈ p.path (routes k)))
    let shift := fun q : Σ _ : Device, J =>
      old q.2 + offset p (routes q.2) q.1 - offset p (routes j) q.1
    let a := fun q : Σ _ : Device, J => shift q - p.duration q.1
    let b := fun q : Σ _ : Device, J => shift q + p.duration q.1
    have hl : (∑ q ∈ blocking, (b q - a q)) < H := by
      calc
        _ = ∑ i ∈ v, 2 * (((s.filter (fun k => i ∈ p.path (routes k))).card : ℝ) *
              p.duration i) := by
          rw [show (fun q => b q - a q) = fun q => 2 * p.duration q.1 from
            funext (fun q => by dsimp only [a, b]; ring)]
          simp only [blocking, sum_sigma, sum_const, nsmul_eq_mul]
          apply sum_congr rfl
          intro i _
          ring
        _ ≤ 2 * ∑ i ∈ v, cap i := by
          rw [mul_sum]
          exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcap' i) (by norm_num))
        _ < H := hroom j (mem_insert_self _ _)
    obtain ⟨z, hz, hfree⟩ := LongTails.Proofs.BirchResourceWindow.exists_unoccupied
      blocking a b hH (fun q _ => by dsimp only [a, b]; linarith [hd q.1]) hl
    let start := Function.update old j z
    have hnew : start j = z := Function.update_self ..
    have hkeep (k : J) (hk : k ∈ s) : start k = old k :=
      Function.update_of_ne (by rintro rfl; exact hj hk) ..
    have hdisjoint (i : Device) (t : ℝ) (k : J) (hk : k ∈ s)
        (hj' : (⟨routes j, start j⟩ : Job Route).active p i t)
        (hk' : (⟨routes k, start k⟩ : Job Route).active p i t) : False := by
      have hq : (⟨i, k⟩ : Σ _ : Device, J) ∈ blocking := by
        exact mem_sigma.mpr ⟨List.mem_toFinset.mpr hj'.1, mem_filter.mpr ⟨hk, hk'.1⟩⟩
      apply hfree ⟨i, k⟩ hq
      have hn := hj'.2
      have ho := hk'.2
      change t ∈ Ico (start j + offset p (routes j) i)
        (start j + offset p (routes j) i + p.duration i) at hn
      change t ∈ Ico (start k + offset p (routes k) i)
        (start k + offset p (routes k) i + p.duration i) at ho
      rw [hnew] at hn
      rw [hkeep k hk] at ho
      dsimp only [a, b, shift]
      exact ⟨by linarith only [hn.2, ho.1], by linarith only [hn.1, ho.2]⟩
    refine ⟨start, ?_, ?_⟩
    · intro i t k hk l hl hka hla
      by_cases hkj : k = j
      · subst k
        by_cases hlj : l = j
        · exact hlj.symm
        · exact (hdisjoint i t l (mem_of_mem_insert_of_ne hl hlj) hka hla).elim
      · have hk' := mem_of_mem_insert_of_ne hk hkj
        by_cases hlj : l = j
        · subst l
          exact (hdisjoint i t k hk' hla hka).elim
        · have hl' := mem_of_mem_insert_of_ne hl hlj
          exact hold i t k hk' l hl' (by simpa only [Job.active, hkeep k hk'] using hka)
            (by simpa only [Job.active, hkeep l hl'] using hla)
    · intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · rwa [hnew]
      · rw [hkeep k hk]
        exact holdtime k hk

lemma routed_phase_of_rounded_load {Route Device J : Type*} [DecidableEq Device]
    (p : Profile Route Device) (depth : ℕ) (hp : p.Valid depth)
    (routes : J → Route) (s : Finset J) (A t : ℝ) (hA : 0 ≤ A) (ht : 0 < t)
    (hlat : ∀ j ∈ s, latency p (routes j) ≤ t)
    (hload : ∀ i, ((s.filter (fun j => i ∈ p.path (routes j))).card : ℝ) * p.duration i ≤
      A + 2 * depth * p.duration i) :
    ∃ start : J → ℝ, Legal p (fun j => ⟨routes j, start j⟩) s ∧
      ∀ j ∈ s, 0 ≤ start j ∧ start j + latency p (routes j) ≤
        2 * depth * A + (4 * depth + 2) * t := by
  let cap := fun i => A + 2 * (depth : ℝ) * p.duration i
  let H := 2 * (depth : ℝ) * A + (4 * depth + 1) * t
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hroom (j : J) (hj : j ∈ s) :
      2 * ∑ i ∈ (p.path (routes j)).toFinset, cap i < H := by
    have hn := (hp.2 (routes j)).1
    have hlen : ((p.path (routes j)).toFinset.card : ℝ) ≤ depth := by
      rw [List.toFinset_card_of_nodup hn]
      exact_mod_cast (hp.2 (routes j)).2.2
    have hsum : (∑ i ∈ (p.path (routes j)).toFinset, p.duration i) ≤ t := by
      rw [List.sum_toFinset _ hn]
      exact hlat j hj
    have h₁ := mul_le_mul_of_nonneg_right hlen hA
    have h₂ := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (2 : ℝ) * depth)
    simp only [cap, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    dsimp only [H]
    linarith only [h₁, h₂, ht]
  obtain ⟨start, hl, hstart⟩ :=
    pack_no_wait p (fun i => (hp.1 i).le) routes s cap H hH hload hroom
  refine ⟨start, hl, fun j hj => ⟨(hstart j hj).1, ?_⟩⟩
  have he := (hstart j hj).2
  dsimp only [H] at he
  linarith only [he, hlat j hj]

end LongTails.Proofs.BirchRoutedTime
