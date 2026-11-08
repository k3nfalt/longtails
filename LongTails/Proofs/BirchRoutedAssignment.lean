import LongTails.Proofs.BirchRoutedTime

namespace LongTails.Proofs.BirchRoutedTime

open Finset LongTails.Setups.BirchRoutedTime

noncomputable def uses {Route Device : Type*} [DecidableEq Device] (p : Profile Route Device)
    (routes : ℕ → Route) (k : ℕ) (i : Device) : ℝ :=
  ((range k).filter (fun j => i ∈ p.path (routes j))).card

lemma total_uses {Route Device : Type*} [Fintype Device] [DecidableEq Device]
    (p : Profile Route Device) (depth : ℕ) (hp : p.Valid depth) (routes : ℕ → Route) (k : ℕ) :
    ∑ i, uses p routes k i ≤ (depth : ℝ) * k := by
  classical
  have he (i : Device) :
      uses p routes k i = ∑ j ∈ range k, (if i ∈ p.path (routes j) then 1 else 0 : ℝ) := by
    simp [uses, sum_boole]
  simp_rw [he]
  rw [sum_comm]
  calc
    _ ≤ ∑ _j ∈ range k, (depth : ℝ) := by
      apply sum_le_sum
      intro j _
      rw [sum_boole]
      have hset : univ.filter (fun i => i ∈ p.path (routes j)) = (p.path (routes j)).toFinset := by
        ext i
        simp
      rw [hset, List.toFinset_card_of_nodup (hp.2 _).1]
      exact_mod_cast (hp.2 (routes j)).2.2
    _ = _ := by simp [mul_comm]

lemma feasible_extension {Route Device : Type*} [Fintype Route] [Fintype Device]
    [DecidableEq Device] (p : Profile Route Device) (depth B k : ℕ) (hdepth : 0 < depth)
    (hp : p.Valid depth) (t : ℝ) (x : Route → ℝ) (hx : FeasibleRate p t x)
    (hR : 0 < ∑ r, x r) (hk : k < B) (routes : ℕ → Route) :
    let A := (depth : ℝ) * B / (∑ r, x r)
    ∃ r, 0 < x r ∧ ∀ i ∈ p.path r, uses p routes k i * p.duration i < A := by
  classical
  dsimp only
  let R := ∑ r, x r
  let A := (depth : ℝ) * B / R
  let saturated := univ.filter (fun i => A ≤ uses p routes k i * p.duration i)
  have hB : 0 < B := Nat.zero_lt_of_lt hk
  have hA : 0 < A := by dsimp only [A]; positivity
  by_contra! h
  have hnonneg (r : Route) (i : Device) : 0 ≤ (if i ∈ p.path r then x r else 0) := by
    split
    · exact hx.1 r
    · exact le_rfl
  have hcover (r : Route) (hr : r ∈ (univ : Finset Route)) :
      x r ≤ ∑ i ∈ saturated, (if i ∈ p.path r then x r else 0) := by
    by_cases hpos : 0 < x r
    · obtain ⟨i, hi, hs⟩ := h r hpos
      have hs' : i ∈ saturated := mem_filter.mpr ⟨mem_univ _, hs⟩
      simpa only [ite_eq_left hi] using
        (single_le_sum (f := fun i => if i ∈ p.path r then x r else 0)
          (fun j _ => hnonneg r j) hs')
    · exact (le_of_not_gt hpos).trans (sum_nonneg fun i _ => hnonneg r i)
  have hc : R ≤ ∑ i ∈ saturated, ∑ r, (if i ∈ p.path r then x r else 0) := by
    rw [sum_comm]
    exact sum_le_sum hcover
  have hsumb : (∑ i ∈ saturated, uses p routes k i) ≤ (depth : ℝ) * k :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => by unfold uses; positivity)).trans
      (total_uses p depth hp routes k)
  have hterm (i : Device) (hi : i ∈ saturated) :
      A * (∑ r, if i ∈ p.path r then x r else 0) ≤ uses p routes k i := by
    have hz : A ≤ uses p routes k i * p.duration i := (mem_filter.mp hi).2
    have hmass : 0 ≤ ∑ r, if i ∈ p.path r then x r else 0 :=
      sum_nonneg fun r _ => hnonneg r i
    calc
      _ ≤ (uses p routes k i * p.duration i) * (∑ r, if i ∈ p.path r then x r else 0) :=
        mul_le_mul_of_nonneg_right hz hmass
      _ = uses p routes k i * (p.duration i * (∑ r, if i ∈ p.path r then x r else 0)) := by ring
      _ ≤ uses p routes k i * 1 := mul_le_mul_of_nonneg_left (hx.2.2 i) (by unfold uses; positivity)
      _ = _ := mul_one _
  have hh : A * R ≤ ∑ i ∈ saturated, A * (∑ r, if i ∈ p.path r then x r else 0) := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hc hA.le
  have hfin := hh.trans ((sum_le_sum hterm).trans hsumb)
  have hprod : A * R = (depth : ℝ) * B := div_mul_cancel₀ _ (ne_of_gt hR)
  rw [hprod] at hfin
  exact (not_le_of_gt (mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hk) (by positivity : 0 < (depth : ℝ)))) hfin

lemma greedy_assignment {Route Device : Type*} [Fintype Route] [Fintype Device]
    [DecidableEq Device] (p : Profile Route Device) (depth B : ℕ) (hdepth : 0 < depth)
    (hp : p.Valid depth) (t : ℝ) (x : Route → ℝ) (hx : FeasibleRate p t x) (hR : 0 < ∑ r, x r) :
    let A := (depth : ℝ) * B / (∑ r, x r)
    ∃ routes : ℕ → Route, (∀ j < B, latency p (routes j) ≤ t) ∧
      ∀ i, uses p routes B i * p.duration i ≤ A + p.duration i := by
  classical
  let A := (depth : ℝ) * B / (∑ r, x r)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨r₀, hr₀⟩ : ∃ r, 0 < x r := by
    by_contra! hn
    exact (not_le_of_gt hR) (sum_nonpos fun r _ => hn r)
  suffices ∀ k ≤ B, ∃ routes : ℕ → Route, (∀ j < k, latency p (routes j) ≤ t) ∧
      ∀ i, uses p routes k i * p.duration i ≤ A + p.duration i by
    exact this B le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun _ => r₀, fun _ h => (Nat.not_lt_zero _ h).elim, fun i => by
      simp [uses, add_nonneg hA (hp.1 i).le]⟩
  | succ k ih =>
    intro hk
    obtain ⟨routes, hlat, hload⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨r, hr, hrroom⟩ := feasible_extension p depth B k hdepth hp t x hx hR
      (Nat.lt_of_succ_le hk) routes
    refine ⟨Function.update routes k r, ?_, ?_⟩
    · intro j hj
      by_cases he : j = k
      · subst j
        rw [Function.update_self]
        exact le_of_not_gt fun hh => (ne_of_gt hr) (hx.2.1 r hh)
      · rw [Function.update_of_ne he]
        exact hlat j (by omega)
    · intro i
      have hfilter : (range k).filter (fun j => i ∈ p.path (Function.update routes k r j)) =
          (range k).filter (fun j => i ∈ p.path (routes j)) := by
        apply filter_congr
        intro j hj
        rw [Function.update_of_ne (ne_of_lt (mem_range.mp hj))]
      unfold uses
      have hrange : range (k + 1) = insert k (range k) := by
        ext j
        simp only [mem_range, mem_insert]
        omega
      rw [hrange, filter_insert]
      by_cases hi : i ∈ p.path r
      · simp only [Function.update_self, hi, ite_true]
        rw [hfilter, card_insert_of_notMem (fun h => (Nat.lt_irrefl k) (mem_range.mp (filter_subset _ _ h))),
          Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        exact add_le_add (hrroom i hi).le (le_refl _)
      · simp only [Function.update_self, hi, ite_false, hfilter]
        exact hload i

lemma exists_routed_phase {Route Device : Type*} [Fintype Route] [Fintype Device]
    [DecidableEq Device] (p : Profile Route Device) (depth B : ℕ) (hdepth : 0 < depth)
    (hp : p.Valid depth) (t : ℝ) (ht : 0 < t) (x : Route → ℝ) (hx : FeasibleRate p t x)
    (hR : 0 < ∑ r, x r) :
    let A := (depth : ℝ) * B / (∑ r, x r)
    ∃ jobs : ℕ → Job Route, Legal p jobs (range B) ∧ ∀ j < B,
      0 ≤ (jobs j).launch ∧ (jobs j).launch + latency p (jobs j).route ≤
        2 * depth * A + (4 * depth + 2) * t := by
  let A := (depth : ℝ) * B / (∑ r, x r)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨routes, hlat, hload⟩ := greedy_assignment p depth B hdepth hp t x hx hR
  have hdepth' : (1 : ℝ) ≤ depth := by exact_mod_cast hdepth
  have hload' (i : Device) : uses p routes B i * p.duration i ≤
      A + 2 * depth * p.duration i := by
    refine (hload i).trans (add_le_add (le_refl A) ?_)
    have hi := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * depth by linarith) (hp.1 i).le
    simpa only [one_mul] using hi
  obtain ⟨start, hlegal, hstart⟩ := routed_phase_of_rounded_load p depth hp routes (range B)
    A t hA ht (fun j hj => hlat j (mem_range.mp hj)) hload'
  exact ⟨fun j => ⟨routes j, start j⟩, hlegal, fun j hj => hstart j (mem_range.mpr hj)⟩

lemma benchmark_phase {Route Device J : Type*} [Fintype Route] [DecidableEq Route]
    [Fintype Device] [DecidableEq Device] (p : Profile Route Device)
    (depth B : ℕ) (hdepth : 0 < depth) (hB : 0 < B) (hp : p.Valid depth)
    (jobs : J → Job Route) (s : Finset J) (T : ℝ) (hT : 0 < T)
    (hl : Legal p jobs s) (htime : ∀ j ∈ s,
      0 ≤ (jobs j).launch ∧ (jobs j).launch + latency p (jobs j).route ≤ T) (hquota : B ≤ s.card) :
    ∃ plan : ℕ → Job Route, Legal p plan (range B) ∧ ∀ j < B,
      0 ≤ (plan j).launch ∧ (plan j).launch + latency p (plan j).route ≤
        (2 * (depth : ℝ)^2 + 4 * depth + 2) * T := by
  let x := windowRate jobs s T
  have hx := window_rate_feasible p (fun i => (hp.1 i).le) jobs s T hT hl htime
  have hs : (0 : ℝ) < s.card := Nat.cast_pos.mpr (hB.trans_le hquota)
  have hsum : ∑ r, x r = (s.card : ℝ) / T := window_rate_sum jobs s T
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
