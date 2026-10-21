import LongTails.Proofs.RennalaAllocation
import LongTails.Proofs.SgdExecution

open scoped BigOperators

namespace OracleTemplate.Rennala

noncomputable def workerState (p : Public) (tau : Fin p.n → ℝ) {Ω : Type}
    (g : Point p.d → Ω → Point p.d) (j : Fin (p.horizon + 1)) (seeds : ℕ → Ω) : ℕ → State p
  | 0 => initialState p j
  | r + 1 =>
      let s := workerState p tau g j seeds r
      updateCore p s (eventAnswer p tau g (some s.jobs) (seeds r))

lemma schedule_invariants (p : Public) (hn : 0 < p.n) (tau : Fin p.n → ℝ)
    (htau : ∀ i, 0 < tau i) {Ω : Type} (g : Point p.d → Ω → Point p.d)
    (j : Fin (p.horizon + 1)) (seeds : ℕ → Ω) (r : ℕ) :
    let s := workerState p tau g j seeds r
    0 ≤ s.clock ∧ s.count < batchSize p.v p.eps ∧
    (∀ i, (s.jobs i).tag ≤ s.iteration ∧ (s.jobs i).started ≤ s.clock ∧
      s.clock ≤ (s.jobs i).started + tau i ∧
      ((s.jobs i).tag = s.iteration → (s.jobs i).point = s.point)) ∧
    ((workerState p tau g j seeds r).clock ≤ (workerState p tau g j seeds (r + 1)).clock) ∧
    ∃ i : Fin p.n,
      nextWorker tau (fun a => (s.jobs a).started) (List.finRange p.n) = some i ∧
      ∀ a : Fin p.n, (s.jobs i).started + tau i ≤ (s.jobs a).started + tau a := by
  classical
  have hS : 0 < batchSize p.v p.eps := by
    dsimp only [batchSize]
    omega
  have hsel : ∀ (starts : Fin p.n → ℝ) (l : List (Fin p.n)), l ≠ [] →
      ∃ i, nextWorker tau starts l = some i ∧
        ∀ a ∈ l, starts i + tau i ≤ starts a + tau a := by
    intro starts l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro _
      by_cases hl : l = []
      · subst l
        exact ⟨i, by rfl, by simp⟩
      · obtain ⟨k, hk, hmin⟩ := ih hl
        by_cases hik : starts i + tau i ≤ starts k + tau k
        · refine ⟨i, by dsimp only [nextWorker]; rw [hk]; simp only [hik, ite_true], ?_⟩
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact le_rfl
          · exact hik.trans (hmin a ha)
        · refine ⟨k, by dsimp only [nextWorker]; rw [hk]; simp only [hik, ite_false], ?_⟩
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact le_of_lt (lt_of_not_ge hik)
          · exact hmin a ha
  have hchoose : ∀ s : State p, ∃ i,
      nextWorker tau (fun a => (s.jobs a).started) (List.finRange p.n) = some i ∧
      ∀ a, (s.jobs i).started + tau i ≤ (s.jobs a).started + tau a := by
    intro s
    have hne : List.finRange p.n ≠ [] := by
      intro h
      have hm := List.mem_finRange (⟨0, hn⟩ : Fin p.n)
      rw [h] at hm
      exact List.not_mem_nil hm
    obtain ⟨i, hi, hmin⟩ := hsel (fun a => (s.jobs a).started) _ hne
    exact ⟨i, hi, fun a => hmin a (List.mem_finRange a)⟩
  let Inv := fun s : State p => 0 ≤ s.clock ∧ s.count < batchSize p.v p.eps ∧
    ∀ i, (s.jobs i).tag ≤ s.iteration ∧ (s.jobs i).started ≤ s.clock ∧
      s.clock ≤ (s.jobs i).started + tau i ∧
      ((s.jobs i).tag = s.iteration → (s.jobs i).point = s.point)
  have hstep : ∀ (s : State p) (seed : Ω), Inv s →
      Inv (updateCore p s (eventAnswer p tau g (some s.jobs) seed)) ∧
      s.clock ≤ (updateCore p s (eventAnswer p tau g (some s.jobs) seed)).clock := by
    intro s seed hs
    obtain ⟨i, hi, hmin⟩ := hchoose s
    rcases hs with ⟨hc, hcount, hjobs⟩
    have ht := (hjobs i).2.2.1
    have hnonneg : 0 ≤ (s.jobs i).started + tau i := hc.trans ht
    dsimp only [eventAnswer]
    rw [hi]
    dsimp only [updateCore]
    by_cases htag : (s.jobs i).tag = s.iteration
    · simp only [htag, ite_true]
      by_cases hfull : s.count + 1 = batchSize p.v p.eps
      · simp only [hfull, ite_true]
        refine ⟨⟨hnonneg, hS, ?_⟩, ht⟩
        intro a
        by_cases hai : a = i
        · subst a
          simp only [Function.update, dite_true]
          exact ⟨by omega, le_rfl, by linarith [htau i], by omega⟩
        · simp only [Function.update, dite_eq_right hai]
          exact ⟨by have := (hjobs a).1; omega,
            (hjobs a).2.1.trans ht, hmin a, by have := (hjobs a).1; omega⟩
      · simp only [hfull, ite_false]
        refine ⟨⟨hnonneg, by change s.count + 1 < batchSize p.v p.eps; omega, ?_⟩, ht⟩
        intro a
        by_cases hai : a = i
        · subst a
          simp only [Function.update, dite_true]
          exact ⟨le_rfl, le_rfl, by linarith [htau i], fun _ => by trivial⟩
        · simp only [Function.update, dite_eq_right hai]
          exact ⟨(hjobs a).1, (hjobs a).2.1.trans ht, hmin a, (hjobs a).2.2.2⟩
    · simp only [htag, ite_false]
      have hfull : s.count ≠ batchSize p.v p.eps := Nat.ne_of_lt hcount
      simp only [hfull, ite_false]
      refine ⟨⟨hnonneg, hcount, ?_⟩, ht⟩
      intro a
      by_cases hai : a = i
      · subst a
        simp only [Function.update, dite_true]
        exact ⟨le_rfl, le_rfl, by linarith [htau i], fun _ => by trivial⟩
      · simp only [Function.update, dite_eq_right hai]
        exact ⟨(hjobs a).1, (hjobs a).2.1.trans ht, hmin a, (hjobs a).2.2.2⟩
  have hinv : ∀ k, Inv (workerState p tau g j seeds k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨le_rfl, hS, ?_⟩
      intro i
      exact ⟨le_rfl, le_rfl, by change (0 : ℝ) ≤ 0 + tau i; simpa only [zero_add] using le_of_lt (htau i), fun _ => by trivial⟩
    | succ k ih => exact (hstep _ _ ih).1
  exact ⟨(hinv r).1, (hinv r).2.1, (hinv r).2.2,
    (hstep _ _ (hinv r)).2, hchoose _⟩


lemma batch_event_bound (p : Public) (hn : 0 < p.n) (tau : Fin p.n → ℝ)
    (htau : ∀ i, 0 < tau i) {Ω : Type} (g : Point p.d → Ω → Point p.d)
    (j : Fin (p.horizon + 1)) (seeds : ℕ → Ω) (r : ℕ) :
    ∃ q, r < q ∧ q ≤ r + (batchSize p.v p.eps + p.n) ∧
      (workerState p tau g j seeds q).iteration = (workerState p tau g j seeds r).iteration + 1 ∧
      (∀ t, r ≤ t → t < q →
        (workerState p tau g j seeds t).iteration = (workerState p tau g j seeds r).iteration) := by
  classical
  let st := workerState p tau g j seeds
  let stale := fun s : State p => Finset.univ.filter (fun i => (s.jobs i).tag ≠ s.iteration)
  let rank := fun k => batchSize p.v p.eps - (st k).count + (stale (st k)).card
  have htrans : ∀ k, (st (k + 1)).iteration = (st k).iteration + 1 ∨
      (st (k + 1)).iteration = (st k).iteration ∧ rank (k + 1) < rank k := by
    intro k
    have hs := schedule_invariants p hn tau htau g j seeds k
    obtain ⟨i, hi, hmin⟩ := hs.2.2.2.2
    have hcount := hs.2.1
    have heq : st (k + 1) = updateCore p (st k)
        (some (i, ((st k).jobs i).started + tau i, ((st k).jobs i).tag,
          g ((st k).jobs i).point (seeds k))) := by
      dsimp only [st, workerState, eventAnswer]
      rw [hi]
    by_cases htag : ((st k).jobs i).tag = (st k).iteration
    · by_cases hfull : (st k).count + 1 = batchSize p.v p.eps
      · left
        rw [heq]
        dsimp only [updateCore]
        simp only [htag, ite_true, hfull]
      · right
        have heq' := heq
        dsimp only [updateCore] at heq'
        simp only [htag, ite_true, hfull, ite_false] at heq'
        have hstale : stale (st (k + 1)) = stale (st k) := by
          ext a
          by_cases ha : a = i
          · subst a
            simp [stale, heq', htag]
          · simp [stale, heq', Function.update, ha]
        refine ⟨by rw [heq'], ?_⟩
        dsimp only [rank]
        rw [hstale]
        have hc : (st (k + 1)).count = (st k).count + 1 := by rw [heq']
        rw [hc]
        change (st k).count < batchSize p.v p.eps at hcount
        omega
    · right
      have hfull : (st k).count ≠ batchSize p.v p.eps := Nat.ne_of_lt hcount
      have heq' := heq
      dsimp only [updateCore] at heq'
      simp only [htag, ite_false, hfull] at heq'
      have hstale : stale (st (k + 1)) = (stale (st k)).erase i := by
        ext a
        by_cases ha : a = i
        · subst a
          simp [stale, heq']
        · simp [stale, heq', Function.update, ha]
      have himem : i ∈ stale (st k) := by simp [stale, htag]
      have hcard := Finset.card_erase_add_one himem
      refine ⟨by rw [heq'], ?_⟩
      dsimp only [rank]
      rw [hstale]
      have hc : (st (k + 1)).count = (st k).count := by rw [heq']
      rw [hc]
      omega
  have hfind : ∀ k, ∃ q, k < q ∧ q ≤ k + rank k ∧
      (st q).iteration = (st k).iteration + 1 ∧
      (∀ t, k ≤ t → t < q → (st t).iteration = (st k).iteration) := by
    have haux : ∀ R k, rank k = R → ∃ q, k < q ∧ q ≤ k + rank k ∧
        (st q).iteration = (st k).iteration + 1 ∧
        (∀ t, k ≤ t → t < q → (st t).iteration = (st k).iteration) := by
      intro R
      induction R using Nat.strong_induction_on with
      | h R ih =>
        intro k hk
        rcases htrans k with hdone | ⟨hsame, hless⟩
        · refine ⟨k + 1, by omega, ?_, hdone, ?_⟩
          · have hc := (schedule_invariants p hn tau htau g j seeds k).2.1
            change (st k).count < batchSize p.v p.eps at hc
            dsimp only [rank]
            omega
          · intro t hkt htq
            have : t = k := by omega
            subst t
            rfl
        · obtain ⟨q, hkq, hq, hiter, hprefix⟩ :=
            ih (rank (k + 1)) (by omega) (k + 1) rfl
          refine ⟨q, by omega, by omega, ?_, ?_⟩
          · simpa only [hsame] using hiter
          · intro t hkt htq
            by_cases htk : t = k
            · subst t
              rfl
            · exact (hprefix t (by omega) htq).trans hsame
    intro k
    exact haux (rank k) k rfl
  obtain ⟨q, hrq, hq, hiter, hprefix⟩ := hfind r
  refine ⟨q, hrq, ?_, hiter, hprefix⟩
  have hcard : (stale (st r)).card ≤ p.n := by
    calc
      _ ≤ (Finset.univ : Finset (Fin p.n)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = p.n := by simp
  dsimp only [rank] at hq
  omega


lemma batch_time_bound (p : Public) (hn : 0 < p.n) (tau : Fin p.n → ℝ)
    (htau : ∀ i, 0 < tau i) (horder : Monotone tau) {Ω : Type}
    (g : Point p.d → Ω → Point p.d) (j : Fin (p.horizon + 1)) (seeds : ℕ → Ω) (r : ℕ) :
    ∃ q, r < q ∧ q ≤ r + (batchSize p.v p.eps + p.n) ∧
      (workerState p tau g j seeds q).iteration = (workerState p tau g j seeds r).iteration + 1 ∧
      (∀ t, r ≤ t → t < q →
        (workerState p tau g j seeds t).iteration = (workerState p tau g j seeds r).iteration) ∧
      (∀ m : Fin p.n, (workerState p tau g j seeds q).clock ≤
        (workerState p tau g j seeds r).clock + 2 * allocationTime tau (batchSize p.v p.eps) m) := by
  classical
  let st := workerState p tau g j seeds
  obtain ⟨q, hrq, hq, hiter, hprefix⟩ := batch_event_bound p hn tau htau g j seeds r
  refine ⟨q, hrq, hq, hiter, hprefix, ?_⟩
  have htrack : ∀ t, r ≤ t → t < q → ∃ C : Fin p.n → ℕ,
      (st t).count = (st r).count + ∑ i, C i ∧
      ∀ i, ((st t).jobs i).started ≤ (st r).clock +
        ((C i : ℝ) + if ((st t).jobs i).tag = (st t).iteration then 1 else 0) * tau i := by
    intro t hrt
    induction t, hrt using Nat.le_induction with
    | base =>
      intro _
      refine ⟨fun _ => 0, by simp, ?_⟩
      intro i
      have hs := (schedule_invariants p hn tau htau g j seeds r).2.2.1 i
      have hsr : ((st r).jobs i).started ≤ (st r).clock := hs.2.1
      by_cases htag : ((st r).jobs i).tag = (st r).iteration
      · simp only [Nat.cast_zero, htag, ite_true, zero_add, one_mul]
        linarith [hsr, htau i]
      · simpa only [Nat.cast_zero, htag, ite_false, zero_add, zero_mul, add_zero] using hsr
    | succ t hrt ih =>
      intro htq
      obtain ⟨C, hC, hstart⟩ := ih (by omega)
      have hs := schedule_invariants p hn tau htau g j seeds t
      obtain ⟨i, hi, hmin⟩ := hs.2.2.2.2
      have heq : st (t + 1) = updateCore p (st t)
          (some (i, ((st t).jobs i).started + tau i, ((st t).jobs i).tag,
            g ((st t).jobs i).point (seeds t))) := by
        dsimp only [st, workerState, eventAnswer]
        rw [hi]
      have hsame : (st (t + 1)).iteration = (st t).iteration :=
        (hprefix (t + 1) (by omega) htq).trans (hprefix t hrt (by omega)).symm
      by_cases htag : ((st t).jobs i).tag = (st t).iteration
      · have hfull : (st t).count + 1 ≠ batchSize p.v p.eps := by
          intro hf
          have hh : (st (t + 1)).iteration = (st t).iteration + 1 := by
            rw [heq]
            dsimp only [updateCore]
            simp only [htag, ite_true, hf]
          omega
        dsimp only [updateCore] at heq
        simp only [htag, ite_true, hfull, ite_false] at heq
        refine ⟨fun a => C a + if a = i then 1 else 0, ?_, ?_⟩
        · simp only [Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          rw [heq]
          dsimp only
          omega
        · intro a
          by_cases ha : a = i
          · subst a
            have hb := hstart i
            simp only [htag, ite_true] at hb
            simp [heq, Function.update]
            linarith
          · simpa [heq, Function.update, ha] using hstart a
      · have hfull : (st t).count ≠ batchSize p.v p.eps := Nat.ne_of_lt hs.2.1
        dsimp only [updateCore] at heq
        simp only [htag, ite_false, hfull] at heq
        refine ⟨C, ?_, ?_⟩
        · rw [heq]
          exact hC
        · intro a
          by_cases ha : a = i
          · subst a
            have hb := hstart i
            simp only [htag, ite_false, add_zero] at hb
            simp [heq, Function.update]
            linarith
          · simpa [heq, Function.update, ha] using hstart a
  have hS : 0 < batchSize p.v p.eps := by dsimp only [batchSize]; omega
  obtain ⟨m₀, hmin, hsmall, hpos, hB, hBpos, hBsum, hBtime⟩ :=
    optimal_allocation hn tau htau horder (batchSize p.v p.eps) hS
  let B := fun i : Fin p.n => if i ≤ m₀ then allocationTime tau (batchSize p.v p.eps) m₀ / tau i - 1 else 0
  have hround := rounded_allocation tau htau (batchSize p.v p.eps) B
    (allocationTime tau (batchSize p.v p.eps) m₀) hB (le_of_eq hBsum.symm) hBtime
  obtain ⟨C, hC, hstart⟩ := htrack (q - 1) (by omega) (by omega)
  have hc := (schedule_invariants p hn tau htau g j seeds (q - 1)).2.1
  have hClt : ∑ i, C i < batchSize p.v p.eps := by
    change (st (q - 1)).count < batchSize p.v p.eps at hc
    omega
  have hex : ∃ i, C i < ⌈B i⌉₊ := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin p.n))) => h i)
    have hh := hround.1
    omega
  obtain ⟨i, hi⟩ := hex
  have hbpos : 0 < ⌈B i⌉₊ := by omega
  have htime := hround.2 i hbpos
  have hnat : C i + 2 ≤ ⌈B i⌉₊ + 1 := by omega
  have hreal : (C i : ℝ) + 2 ≤ (⌈B i⌉₊ : ℝ) + 1 := by exact_mod_cast hnat
  have hstarted : ((st (q - 1)).jobs i).started + tau i ≤
      (st r).clock + ((C i : ℝ) + 2) * tau i := by
    have hb := hstart i
    split_ifs at hb <;> nlinarith [htau i]
  have hfinish : ((st (q - 1)).jobs i).started + tau i ≤
      (st r).clock + 2 * allocationTime tau (batchSize p.v p.eps) m₀ := by
    have hmul := mul_le_mul_of_nonneg_right hreal (le_of_lt (htau i))
    nlinarith
  have hs := schedule_invariants p hn tau htau g j seeds (q - 1)
  obtain ⟨a, ha, hamin⟩ := hs.2.2.2.2
  have hclock : (st q).clock = ((st (q - 1)).jobs a).started + tau a := by
    have hqeq : q = q - 1 + 1 := by omega
    rw [hqeq]
    dsimp only [st, workerState, eventAnswer]
    rw [ha]
    dsimp only [updateCore]
    split_ifs <;> rfl
  intro m
  change (st q).clock ≤ (st r).clock + 2 * allocationTime tau (batchSize p.v p.eps) m
  rw [hclock]
  have hm := hmin m
  have hle := (hamin i).trans hfinish
  linarith


end OracleTemplate.Rennala
