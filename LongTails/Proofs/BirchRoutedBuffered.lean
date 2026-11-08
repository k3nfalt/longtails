import LongTails.Proofs.BirchRoutedAssignment

namespace LongTails.Proofs.BirchRoutedTime

open Finset Set LongTails.Setups.BirchRoutedTime
open LongTails.Proofs.BirchResourceWindow (interval_capacity)

lemma buffered_latency {Route Device : Type*}
    (p : Profile Route Device)
    (job : BufferedJob Route Device) (T : ℝ) (hT : 0 ≤ T)
    (horder : (p.path job.route).Pairwise (fun i k => job.start i + p.duration i ≤ job.start k))
    (hwindow : ∀ i ∈ p.path job.route, 0 ≤ job.start i ∧ job.start i + p.duration i ≤ T) :
    latency p job.route ≤ T := by
  have aux (l : List Device) (a : ℝ)
      (ho : l.Pairwise (fun i k => job.start i + p.duration i ≤ job.start k))
      (hw : ∀ i ∈ l, a ≤ job.start i ∧ job.start i + p.duration i ≤ T)
      (ha : a ≤ T) : (l.map p.duration).sum ≤ T - a := by
    induction l generalizing a with
    | nil => simpa using sub_nonneg.mpr ha
    | cons i l ih =>
      obtain ⟨ha', hfinish⟩ := hw i (by simp)
      have hpair := List.pairwise_cons.mp ho
      have htail : ∀ k ∈ l, job.start i + p.duration i ≤ job.start k ∧
          job.start k + p.duration k ≤ T :=
        fun k hk => ⟨hpair.1 k hk, (hw k (List.mem_cons_of_mem _ hk)).2⟩
      have he := ih (job.start i + p.duration i) hpair.2 htail hfinish
      simp only [List.map_cons, List.sum_cons]
      linarith only [ha', he]
  simpa only [latency, sub_zero] using aux (p.path job.route) 0 horder hwindow hT

lemma buffered_window_rate {Route Device J : Type*} [Fintype Route] [DecidableEq Route]
    [DecidableEq Device] (p : Profile Route Device) (depth : ℕ) (hp : p.Valid depth)
    (jobs : J → BufferedJob Route Device) (s : Finset J) (T : ℝ) (hT : 0 < T)
    (hl : BufferedLegal p jobs s)
    (htime : ∀ j ∈ s, ∀ i ∈ p.path (jobs j).route,
      0 ≤ (jobs j).start i ∧ (jobs j).start i + p.duration i ≤ T) :
    let nominal := fun j => Job.mk (jobs j).route 0
    FeasibleRate p T (windowRate nominal s T) ∧
      ∑ r, windowRate nominal s T r = (s.card : ℝ) / T := by
  classical
  dsimp only
  let nominal := fun j => Job.mk (jobs j).route 0
  refine ⟨⟨fun _ => by unfold windowRate; positivity, ?_, ?_⟩, window_rate_sum nominal s T⟩
  · intro r hr
    have hz : s.filter (fun j => (nominal j).route = r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro j hj
      obtain ⟨hjs, he⟩ := mem_filter.mp hj
      have ha := buffered_latency p (jobs j) T hT.le (hl.1 j hjs) (htime j hjs)
      change (jobs j).route = r at he
      exact (not_lt_of_ge (he ▸ ha)) hr
    change windowRate nominal s T r = 0
    unfold windowRate
    rw [hz]
    simp
  · intro i
    let use := s.filter (fun j => i ∈ p.path (jobs j).route)
    let a := fun j => (jobs j).start i
    let b := fun j => a j + p.duration i
    have ht (j : J) (hj : j ∈ use) : 0 ≤ a j ∧ a j ≤ b j ∧ b j ≤ T := by
      obtain ⟨hjs, hi⟩ := mem_filter.mp hj
      exact ⟨(htime j hjs i hi).1, le_add_of_nonneg_right (hp.1 i).le, (htime j hjs i hi).2⟩
    have hcap (t : ℝ) (_ : t ∈ Ico (0 : ℝ) T) :
        (∑ j ∈ use, (Ico (a j) (b j)).indicator (fun _ => (1 : ℝ)) t) ≤ 1 := by
      let active := use.filter (fun j => t ∈ Ico (a j) (b j))
      have hu : active.card ≤ 1 := Finset.card_le_one.mpr fun j hj k hk => by
        obtain ⟨hj', hja⟩ := mem_filter.mp hj
        obtain ⟨hk', hka⟩ := mem_filter.mp hk
        obtain ⟨hjs, hji⟩ := mem_filter.mp hj'
        obtain ⟨hks, hki⟩ := mem_filter.mp hk'
        exact hl.2 i t j hjs k hks ⟨hji, hja⟩ ⟨hki, hka⟩
      have hs : (∑ j ∈ use, (Ico (a j) (b j)).indicator (fun _ => (1 : ℝ)) t) =
          (active.card : ℝ) := by
        simp only [active, indicator_apply, sum_boole]
      rw [hs]
      exact_mod_cast hu
    have hload := interval_capacity use a b (fun _ => (1 : ℝ)) T 1 hT.le ht hcap
    simp only [b, add_sub_cancel_left, mul_one, sum_const, nsmul_eq_mul] at hload
    rw [route_load_identity, ← mul_div_assoc]
    apply (div_le_iff₀ hT).2
    rw [one_mul, mul_comm]
    exact hload

lemma buffered_benchmark_phase {Route Device J : Type*} [Fintype Route] [DecidableEq Route]
    [Fintype Device] [DecidableEq Device] (p : Profile Route Device)
    (depth B : ℕ) (hdepth : 0 < depth) (hB : 0 < B) (hp : p.Valid depth)
    (jobs : J → BufferedJob Route Device) (s : Finset J) (T : ℝ) (hT : 0 < T)
    (hl : BufferedLegal p jobs s)
    (htime : ∀ j ∈ s, ∀ i ∈ p.path (jobs j).route,
      0 ≤ (jobs j).start i ∧ (jobs j).start i + p.duration i ≤ T)
    (hquota : B ≤ s.card) :
    ∃ plan : ℕ → Job Route, Legal p plan (range B) ∧ ∀ j < B,
      0 ≤ (plan j).launch ∧ (plan j).launch + latency p (plan j).route ≤
        (2 * (depth : ℝ)^2 + 4 * depth + 2) * T := by
  let nominal := fun j => Job.mk (jobs j).route 0
  let x := windowRate nominal s T
  obtain ⟨hx, hsum⟩ := buffered_window_rate p depth hp jobs s T hT hl htime
  have hs : (0 : ℝ) < s.card := Nat.cast_pos.mpr (hB.trans_le hquota)
  have hr : 0 < ∑ r, x r := by rw [hsum]; positivity
  have hc : (B : ℝ) ≤ s.card := Nat.cast_le.mpr hquota
  have hb : (B : ℝ) / (∑ r, x r) ≤ T := by
    apply (div_le_iff₀ hr).2
    rw [hsum]
    calc
      _ ≤ (s.card : ℝ) := hc
      _ = _ := by field_simp
  obtain ⟨plan, hlegal, hplan⟩ := exists_routed_phase p depth B hdepth hp T hT x hx hr
  refine ⟨plan, hlegal, fun j hj => ⟨(hplan j hj).1, (hplan j hj).2.trans ?_⟩⟩
  have hd := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2 : ℝ) * (depth : ℝ)^2 by positivity)
  convert add_le_add hd (le_refl ((4 * (depth : ℝ) + 2) * T)) using 1 <;> ring

end LongTails.Proofs.BirchRoutedTime
