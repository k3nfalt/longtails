import LongTails.Proofs.RingmasterStochastic
import LongTails.Setups.RingmasterIterations
import LongTails.Setups.RingmasterUniversalTime
import LongTails.Proofs.MaleniaUniformTiming
import LongTails.Proofs.RennalaConvergence

open MeasureTheory

namespace OracleTemplate.RingmasterAsgd

open Rennala

theorem advance_add {St : Type} (F : ℕ → St → St) (a b call : ℕ) (x : St) :
    StochasticGradient.advance F (a + b) call x =
      StochasticGradient.advance F b (call + a) (StochasticGradient.advance F a call x) := by
  induction a generalizing call x with
  | zero => rw [Nat.zero_add, Nat.add_zero]; rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show StochasticGradient.advance F (a + b) (call + 1) (F call x) = _
    rw [ih, show call + 1 + a = call + (a + 1) by omega]
    rfl

theorem timing_invariant {n : ℕ} (R : ℕ) (hR : 1 ≤ R) (event : ℕ → (Fin n → ℝ) → Option (Fin n × ℝ))
    (k : ℕ) :
    (timing R event k).count ≤ k ∧
      ∀ i, (timing R event k).iters i ≤ (timing R event k).count ∧
        (timing R event k).count < (timing R event k).iters i + R := by
  induction k with
  | zero => exact ⟨le_rfl, fun i => ⟨le_rfl, by show 0 < 0 + R; omega⟩⟩
  | succ k ih =>
    obtain ⟨hc, hi⟩ := ih
    rcases he : event k (timing R event k).starts with _ | r
    · have ht : timing R event (k + 1) = timing R event k := by
        show Option.elim (event k (timing R event k).starts) _ _ = _
        rw [he]
        rfl
      rw [ht]
      exact ⟨by omega, hi⟩
    · have ht : timing R event (k + 1) = timingStep R (timing R event k) r := by
        show Option.elim (event k (timing R event k).starts) _ _ = _
        rw [he]
        rfl
      rw [ht]
      refine ⟨by show (timing R event k).count + 1 ≤ k + 1; omega, fun i => ?_⟩
      show (if i = r.1 ∨ R ≤ (timing R event k).count + 1 - (timing R event k).iters i then
          (timing R event k).count + 1 else (timing R event k).iters i) ≤ (timing R event k).count + 1 ∧
        (timing R event k).count + 1 < (if i = r.1 ∨ R ≤ (timing R event k).count + 1 -
          (timing R event k).iters i then (timing R event k).count + 1 else (timing R event k).iters i) + R
      have h := hi i
      split_ifs with hh
      · omega
      · push Not at hh
        omega

theorem timing_count {n : ℕ} (R : ℕ) (event : ℕ → (Fin n → ℝ) → Option (Fin n × ℝ)) (k : ℕ)
    (hev : ∀ k' < k, event k' (timing R event k').starts ≠ none) :
    (timing R event k).count = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hev k (Nat.lt_succ_self k))
    have ht : timing R event (k + 1) = timingStep R (timing R event k) r := by
      show Option.elim (event k (timing R event k).starts) _ _ = _
      rw [hr]
      rfl
    rw [ht]
    show (timing R event k).count + 1 = k + 1
    rw [ih (fun k' hk' => hev k' (Nat.lt_succ_of_lt hk'))]

theorem delays_bound {n : ℕ} (R : ℕ) (hR : 1 ≤ R) (event : ℕ → (Fin n → ℝ) → Option (Fin n × ℝ))
    (K : ℕ) (hev : ∀ k < K, event k (timing R event k).starts ≠ none) (k : ℕ) :
    (fun m => if m < K then delays R event m else m) k ≤ k ∧
      k < (fun m => if m < K then delays R event m else m) k + R := by
  show (if k < K then delays R event k else k) ≤ k ∧ k < (if k < K then delays R event k else k) + R
  split_ifs with hk
  · have hc := timing_count R event k (fun k' hk' => hev k' (lt_trans hk' hk))
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hev k hk)
    have hd : delays R event k = (timing R event k).iters r.1 := by
      show Option.elim (event k (timing R event k).starts) k _ = _
      rw [hr]
      rfl
    have hi := (timing_invariant R hR event k).2 r.1
    rw [hd]
    omega
  · omega

theorem advance_ringmaster (q : Public) (hR : 1 ≤ q.R) {Ω : Type} (g : Point q.d → Ω → Point q.d)
    (event : ℕ → (Fin q.n → ℝ) → Option (Fin q.n × ℝ)) (ans : ℕ → Query q → Ω → Reply q)
    (hans : ∀ k pts sts b, ans k (some (pts, sts)) b =
      Option.elim (event k sts) none (fun r => some (r.1, r.2, g (pts r.1) b)))
    (hev : ∀ k < q.K, event k (timing q.R event k).starts ≠ none)
    (j : Fin (q.K + 1)) (ω : ℕ → Ω) (k : ℕ) (hk : k ≤ q.K) :
    StochasticGradient.advance (fun c s => (ringmaster q).update s (ans c ((ringmaster q).query s).2 (ω c)))
        k 0 ((ringmaster q).initial j) =
      (⟨k, delayedIterate g q.gamma (fun m => if m < q.K then delays q.R event m else m) q.x0 ω k,
        fun i => delayedIterate g q.gamma (fun m => if m < q.K then delays q.R event m else m) q.x0 ω
          ((timing q.R event k).iters i),
        (timing q.R event k).starts, (timing q.R event k).iters, (timing q.R event k).clock, j.val,
        if j.val ≤ k then delayedIterate g q.gamma (fun m => if m < q.K then delays q.R event m else m)
          q.x0 ω j.val else q.x0⟩ : State q) := by
  set a : ℕ → ℕ := fun m => if m < q.K then delays q.R event m else m with ha
  induction k with
  | zero =>
    show (⟨0, q.x0, fun _ => q.x0, fun _ => 0, fun _ => 0, 0, j.val, q.x0⟩ : State q) = _
    by_cases hj : j.val = 0
    · rw [ite_eq_left (by omega), hj]
      rfl
    · rw [ite_eq_right (by omega)]
      rfl
  | succ k ih =>
    have hkK : k < q.K := by omega
    rw [advance_add, ih (by omega)]
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hev k hkK)
    have hc := timing_count q.R event k (fun k' hk' => hev k' (lt_trans hk' hkK))
    have ht : timing q.R event (k + 1) = timingStep q.R (timing q.R event k) r := by
      show Option.elim (event k (timing q.R event k).starts) _ _ = _
      rw [hr]
      rfl
    have hd : a k = (timing q.R event k).iters r.1 := by
      show (if k < q.K then delays q.R event k else k) = _
      rw [ite_eq_left hkK]
      show Option.elim (event k (timing q.R event k).starts) k _ = _
      rw [hr]
      rfl
    have hak : a k ≤ k := (delays_bound q.R hR event q.K hev k).1
    have hX : delayedIterate g q.gamma a q.x0 ω (k + 1) =
        delayedIterate g q.gamma a q.x0 ω k -
          q.gamma • g (delayedIterate g q.gamma a q.x0 ω ((timing q.R event k).iters r.1)) (ω k) := by
      rw [delayedIterate_succ g q.gamma a q.x0 ω k hak, hd]
    show (if q.K ≤ k then _ else step q _ (ans (0 + k) (if q.K ≤ k then none else
      some ((fun i => delayedIterate g q.gamma a q.x0 ω ((timing q.R event k).iters i)),
        (timing q.R event k).starts)) (ω (0 + k)))) = _
    have hnK : ¬ q.K ≤ k := by omega
    rw [ite_eq_right hnK, ite_eq_right hnK, Nat.zero_add, hans, hr, ht]
    set X := delayedIterate g q.gamma a q.x0 ω with hXdef
    set T := timing q.R event k with hT
    change (⟨k + 1, X k - q.gamma • g (X (T.iters r.1)) (ω k),
        fun i => if i = r.1 ∨ q.R ≤ k + 1 - T.iters i then X k - q.gamma • g (X (T.iters r.1)) (ω k)
          else X (T.iters i),
        fun i => if i = r.1 ∨ q.R ≤ k + 1 - T.iters i then r.2 else T.starts i,
        fun i => if i = r.1 ∨ q.R ≤ k + 1 - T.iters i then k + 1 else T.iters i,
        r.2, j.val, if j.val = k + 1 then X k - q.gamma • g (X (T.iters r.1)) (ω k)
          else (if j.val ≤ k then X j.val else q.x0)⟩ : State q) =
      ⟨k + 1, X (k + 1),
        fun i => X (if i = r.1 ∨ q.R ≤ T.count + 1 - T.iters i then T.count + 1 else T.iters i),
        fun i => if i = r.1 ∨ q.R ≤ T.count + 1 - T.iters i then r.2 else T.starts i,
        fun i => if i = r.1 ∨ q.R ≤ T.count + 1 - T.iters i then T.count + 1 else T.iters i,
        r.2, j.val, if j.val ≤ k + 1 then X j.val else q.x0⟩
    rw [hc, ← hX]
    congr 1
    · funext i
      split_ifs <;> rfl
    · by_cases hj : j.val = k + 1
      · rw [ite_eq_left hj, ite_eq_left (by omega), hj]
      · rw [ite_eq_right hj]
        by_cases hjr : j.val ≤ k
        · rw [ite_eq_left hjr, ite_eq_left (by omega)]
        · rw [ite_eq_right hjr, ite_eq_right (by omega)]

theorem timing_some {n : ℕ} (R : ℕ) (event : ℕ → (Fin n → ℝ) → Option (Fin n × ℝ)) (k : ℕ)
    (r : Fin n × ℝ) (h : event k (timing R event k).starts = some r) :
    timing R event (k + 1) = timingStep R (timing R event k) r := by
  show Option.elim (event k (timing R event k).starts) _ _ = _
  rw [h]
  rfl

theorem completion_clock {n : ℕ} (R : ℕ) (V : Fin n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0)) (k : ℕ) :
    0 ≤ (timing R (completionEvent V) k).clock ∧
      ∀ i, 0 ≤ (timing R (completionEvent V) k).starts i ∧
        (timing R (completionEvent V) k).starts i ≤ (timing R (completionEvent V) k).clock ∧
        ∀ a, RennalaUniform.completion (V i) ((timing R (completionEvent V) k).starts i) = some a →
          (timing R (completionEvent V) k).clock ≤ a := by
  induction k with
  | zero =>
    refine ⟨le_rfl, fun i => ⟨le_rfl, le_rfl, fun a ha => ?_⟩⟩
    exact (RennalaUniform.completion_spec (V i) (hV i).1 0 le_rfl a ha).1
  | succ k ih =>
    obtain ⟨hc0, hst⟩ := ih
    rcases he : completionEvent V k (timing R (completionEvent V) k).starts with _ | r
    · have ht : timing R (completionEvent V) (k + 1) = timing R (completionEvent V) k := by
        show Option.elim (completionEvent V k (timing R (completionEvent V) k).starts) _ _ = _
        rw [he]
        rfl
      rw [ht]
      exact ⟨hc0, hst⟩
    · rw [timing_some R (completionEvent V) k r he]
      obtain ⟨h1, h2⟩ := (RennalaUniform.earliest_spec
        (fun i => RennalaUniform.completion (V i) ((timing R (completionEvent V) k).starts i))
        (List.finRange n)).1 r.1 r.2 he
      have hct : (timing R (completionEvent V) k).clock ≤ r.2 := (hst r.1).2.2 r.2 h1
      refine ⟨hc0.trans hct, fun i => ?_⟩
      show 0 ≤ (if i = r.1 ∨ R ≤ (timing R (completionEvent V) k).count + 1 -
          (timing R (completionEvent V) k).iters i then r.2 else (timing R (completionEvent V) k).starts i) ∧
        (if i = r.1 ∨ R ≤ (timing R (completionEvent V) k).count + 1 -
          (timing R (completionEvent V) k).iters i then r.2 else (timing R (completionEvent V) k).starts i) ≤ r.2 ∧
        ∀ a, RennalaUniform.completion (V i) (if i = r.1 ∨ R ≤ (timing R (completionEvent V) k).count + 1 -
          (timing R (completionEvent V) k).iters i then r.2 else (timing R (completionEvent V) k).starts i) =
            some a → r.2 ≤ a
      split_ifs
      · exact ⟨hc0.trans hct, le_rfl, fun a ha =>
          (RennalaUniform.completion_spec (V i) (hV i).1 r.2 (hc0.trans hct) a ha).1⟩
      · exact ⟨(hst i).1, (hst i).2.1.trans hct, fun a ha => h2 i (List.mem_finRange i) a ha⟩

theorem floor_quarter_le (w : ℝ) (c : ℕ) (h : w < (2 + c) / 4) : ((⌊w⌋ : ℤ) : ℝ) ≤ c := by
  have hf : ((⌊w⌋ : ℤ) : ℝ) ≤ w := Int.floor_le w
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have h1 : ⌊w⌋ < 1 := by
      rw [Int.floor_lt]
      push_cast at h ⊢
      linarith
    have : ⌊w⌋ ≤ 0 := by omega
    push_cast
    exact_mod_cast this
  · have : (1 : ℝ) ≤ c := by exact_mod_cast hc
    linarith

theorem window_updates {n : ℕ} (R : ℕ) (hR : 1 ≤ R) (V : Fin n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0)) (m : ℕ)
    (hm : ∀ k < m, completionEvent V k (timing R (completionEvent V) k).starts ≠ none)
    (T : ℝ) (hT0 : 0 ≤ T)
    (hT : (R : ℝ) ≤ ∑ i, ((⌊V i T / 4 - V i (timing R (completionEvent V) m).clock / 4⌋ : ℤ) : ℝ)) :
    (∀ k < m + R, completionEvent V k (timing R (completionEvent V) k).starts ≠ none) ∧
      (timing R (completionEvent V) (m + R)).clock ≤ T := by
  classical
  set ev := completionEvent V with hev
  set σ := timing R ev with hσ
  set c := (σ m).clock with hc
  have hm0 := completion_clock R V hV m
  have hcount_m := timing_count R ev m hm
  have hcT : c ≤ T := by
    by_contra hlt
    push Not at hlt
    have hle : ∑ i, ((⌊V i T / 4 - V i c / 4⌋ : ℤ) : ℝ) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      have hVT : V i T ≤ V i c := (hV i).2 (Set.mem_Ici.mpr hT0) (Set.mem_Ici.mpr hm0.1) hlt.le
      have h1 : ⌊V i T / 4 - V i c / 4⌋ ≤ 0 := by
        rw [Int.floor_le_iff]
        push_cast
        linarith
      exact_mod_cast h1
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have main : ∀ l, l ≤ R → (∀ k < m + l, ev k (σ k).starts ≠ none) ∧ (σ (m + l)).clock ≤ T ∧
      ∃ cnt : Fin n → ℕ, ∑ i, cnt i = l ∧ ∀ i,
        ((σ (m + l)).iters i ≤ m ∧ (σ (m + l)).starts i = (σ m).starts i ∧ cnt i = 0) ∨
          (m + 1 ≤ (σ (m + l)).iters i ∧ V i ((σ (m + l)).starts i) ≤ V i c + 1 + cnt i) := by
    intro l
    induction l with
    | zero =>
      intro _
      refine ⟨hm, hcT, fun _ => 0, by simp, fun i => Or.inl ⟨?_, rfl, rfl⟩⟩
      have := ((timing_invariant R hR ev m).2 i).1
      rw [hcount_m] at this
      exact this
    | succ l ih =>
      intro hl
      obtain ⟨hevl, hclk, cnt, hsum, hJ⟩ := ih (by omega)
      set S := σ (m + l) with hS
      have hcnt : S.count = m + l := timing_count R ev (m + l) hevl
      have hinv := completion_clock R V hV (m + l)
      have hex : ∃ r, ev (m + l) S.starts = some r ∧ r.2 ≤ T := by
        by_contra hne
        push Not at hne
        have hlt : ∀ i, V i T < V i (S.starts i) + 1 := by
          intro i
          by_contra hge
          push Not at hge
          obtain ⟨a, ha, -, haT, -⟩ := RennalaUniform.completion_attained (V i) (hV i).1 (S.starts i)
            (hinv.2 i).1 T ((hinv.2 i).2.1.trans hclk) hge
          obtain ⟨j, b, hjb⟩ := (RennalaUniform.earliest_spec
            (fun i => RennalaUniform.completion (V i) (S.starts i)) (List.finRange n)).2
            ⟨i, List.mem_finRange i, a, ha⟩
          have hb := ((RennalaUniform.earliest_spec
            (fun i => RennalaUniform.completion (V i) (S.starts i)) (List.finRange n)).1 j b hjb).2 i
            (List.mem_finRange i) a ha
          have := hne (j, b) hjb
          linarith
        have hfl : ∀ i, ((⌊V i T / 4 - V i c / 4⌋ : ℤ) : ℝ) ≤ cnt i := by
          intro i
          apply floor_quarter_le
          have hci : (0 : ℝ) ≤ cnt i := Nat.cast_nonneg _
          rcases hJ i with ⟨-, hs, -⟩ | ⟨-, hb⟩
          · have h0 := hm0.2 i
            have hVs : V i (S.starts i) ≤ V i c := by
              rw [hs]
              exact (hV i).2 (Set.mem_Ici.mpr h0.1) (Set.mem_Ici.mpr hm0.1) h0.2.1
            have := hlt i
            linarith
          · have := hlt i
            linarith
        have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfl i)
        have h2 : ∑ i, ((cnt i : ℕ) : ℝ) = (l : ℝ) := by exact_mod_cast hsum
        have h3 : (l : ℝ) + 1 ≤ R := by exact_mod_cast hl
        linarith
      obtain ⟨r, hr, hrT⟩ := hex
      have hstep : σ (m + (l + 1)) = timingStep R S r := timing_some R ev (m + l) r hr
      obtain ⟨hr1, hr2⟩ := (RennalaUniform.earliest_spec
        (fun i => RennalaUniform.completion (V i) (S.starts i)) (List.finRange n)).1 r.1 r.2 hr
      have hclkr : S.clock ≤ r.2 := (hinv.2 r.1).2.2 r.2 hr1
      have hr0 : 0 ≤ r.2 := hinv.1.trans hclkr
      refine ⟨fun k hk => ?_, ?_, fun i => cnt i + if i = r.1 then 1 else 0, ?_, fun i => ?_⟩
      · rcases Nat.lt_or_ge k (m + l) with hk' | hk'
        · exact hevl k hk'
        · obtain rfl : k = m + l := by omega
          rw [hr]
          exact Option.some_ne_none r
      · rw [hstep]
        exact hrT
      · rw [Finset.sum_add_distrib, hsum, Finset.sum_ite_eq']
        simp
      · have hit : (σ (m + (l + 1))).iters i = if i = r.1 ∨ R ≤ S.count + 1 - S.iters i then
            S.count + 1 else S.iters i := by rw [hstep]; rfl
        have hst : (σ (m + (l + 1))).starts i = if i = r.1 ∨ R ≤ S.count + 1 - S.iters i then
            r.2 else S.starts i := by rw [hstep]; rfl
        rw [hit, hst, hcnt]
        beta_reduce
        by_cases hi : i = r.1
        · subst hi
          rw [ite_eq_left (Or.inl rfl), ite_eq_left (Or.inl rfl), ite_eq_left rfl]
          right
          refine ⟨by omega, ?_⟩
          have hex := (MaleniaUniform.completion_exact (V r.1) (hV r.1).1 (S.starts r.1)
            (hinv.2 r.1).1 r.2 hr1).2
          rw [hex]
          push_cast
          rcases hJ r.1 with ⟨-, hs, -⟩ | ⟨-, hb⟩
          · have h0 := hm0.2 r.1
            have hVs : V r.1 (S.starts r.1) ≤ V r.1 c := by
              rw [hs]
              exact (hV r.1).2 (Set.mem_Ici.mpr h0.1) (Set.mem_Ici.mpr hm0.1) h0.2.1
            have : (0 : ℝ) ≤ cnt r.1 := Nat.cast_nonneg _
            linarith
          · linarith
        · rw [ite_eq_right hi]
          by_cases hres : R ≤ m + l + 1 - S.iters i
          · rw [ite_eq_left (Or.inr hres), ite_eq_left (Or.inr hres)]
            rcases hJ i with ⟨-, hs, hc0⟩ | ⟨hi1, -⟩
            · right
              refine ⟨by omega, ?_⟩
              rw [hc0]
              have hsr : V i r.2 ≤ V i (S.starts i) + 1 := by
                rcases hci : RennalaUniform.completion (V i) (S.starts i) with _ | b
                · by_contra hgt
                  push Not at hgt
                  obtain ⟨a, ha, -⟩ := RennalaUniform.completion_attained (V i) (hV i).1 (S.starts i)
                    (hinv.2 i).1 r.2 ((hinv.2 i).2.1.trans hclkr) hgt.le
                  rw [hci] at ha
                  cases ha
                · have hb := hr2 i (List.mem_finRange i) b hci
                  have hspec := RennalaUniform.completion_spec (V i) (hV i).1 (S.starts i) (hinv.2 i).1 b hci
                  have hmono := (hV i).2 (Set.mem_Ici.mpr hr0) (Set.mem_Ici.mpr (hr0.trans hb)) hb
                  linarith [hspec.2]
              have h0 := hm0.2 i
              have hVs : V i (S.starts i) ≤ V i c := by
                rw [hs]
                exact (hV i).2 (Set.mem_Ici.mpr h0.1) (Set.mem_Ici.mpr hm0.1) h0.2.1
              push_cast
              linarith
            · exfalso
              omega
          · rw [ite_eq_right (by push Not; exact ⟨hi, by omega⟩),
              ite_eq_right (by push Not; exact ⟨hi, by omega⟩)]
            rw [add_zero]
            exact hJ i
  obtain ⟨h1, h2, -⟩ := main R le_rfl
  exact ⟨h1, h2⟩

theorem deadline_updates {n : ℕ} (R : ℕ) (hR : 1 ≤ R) (V : Fin n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0)) (j : ℕ)
    (hfin : RennalaUniform.deadline (fun i t => V i t / 4) R j < ⊤) :
    (∀ k < j * R, completionEvent V k (timing R (completionEvent V) k).starts ≠ none) ∧
      ENNReal.ofReal (timing R (completionEvent V) (j * R)).clock ≤
        RennalaUniform.deadline (fun i t => V i t / 4) R j := by
  classical
  have hV4 : ∀ i, ContinuousOn (fun t => V i t / 4) (Set.Ici 0) ∧
      MonotoneOn (fun t => V i t / 4) (Set.Ici 0) := fun i =>
    ⟨(hV i).1.div_const 4, fun a ha b hb hab => by
      have := (hV i).2 ha hb hab
      show V i a / 4 ≤ V i b / 4
      linarith⟩
  induction j with
  | zero =>
    refine ⟨fun k hk => by omega, ?_⟩
    rw [Nat.zero_mul]
    show ENNReal.ofReal 0 ≤ 0
    simp
  | succ j ih =>
    have hdj : RennalaUniform.deadline (fun i t => V i t / 4) R j ≠ ⊤ := by
      intro h
      apply (ne_of_lt hfin)
      show (if RennalaUniform.deadline (fun i t => V i t / 4) R j = ⊤ then ⊤ else _) = ⊤
      rw [ite_eq_left h]
    obtain ⟨hev, hclk⟩ := ih (lt_of_le_of_ne le_top hdj)
    set τ := (RennalaUniform.deadline (fun i t => V i t / 4) R j).toReal with hτ
    have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
    have hc0 := (completion_clock R V hV (j * R)).1
    have hcτ : (timing R (completionEvent V) (j * R)).clock ≤ τ := by
      rw [← ENNReal.ofReal_toReal hdj] at hclk
      exact (ENNReal.ofReal_le_ofReal_iff hτ0).mp hclk
    have hd1 : RennalaUniform.deadline (fun i t => V i t / 4) R (j + 1) =
        RennalaUniform.roundTime (fun i t => V i t / 4) R τ := by
      show (if RennalaUniform.deadline (fun i t => V i t / 4) R j = ⊤ then ⊤ else _) = _
      rw [ite_eq_right hdj]
    have hex : ∃ t, 0 ≤ t ∧ (R : ℝ) ≤ ∑ i, ((⌊V i t / 4 - V i τ / 4⌋ : ℤ) : ℝ) := by
      by_contra hne
      apply (ne_of_lt hfin)
      rw [hd1]
      show (if ∃ t, 0 ≤ t ∧ (R : ℝ) ≤ ∑ i, ((⌊V i t / 4 - V i τ / 4⌋ : ℤ) : ℝ) then _ else ⊤) = ⊤
      rw [ite_eq_right hne]
    obtain ⟨ht0, htc⟩ := RennalaUniform.min_attained (fun i t => V i t / 4) hV4
      (fun i => V i τ / 4) (R : ℝ) hex
    set tstar := sInf {t | 0 ≤ t ∧ (R : ℝ) ≤ ∑ i, ((⌊V i t / 4 - V i τ / 4⌋ : ℤ) : ℝ)} with htstar
    have hd1' : RennalaUniform.deadline (fun i t => V i t / 4) R (j + 1) = ENNReal.ofReal tstar := by
      rw [hd1]
      show (if ∃ t, 0 ≤ t ∧ (R : ℝ) ≤ ∑ i, ((⌊V i t / 4 - V i τ / 4⌋ : ℤ) : ℝ) then _ else ⊤) = _
      rw [ite_eq_left hex]
    have hcond : (R : ℝ) ≤ ∑ i, ((⌊V i tstar / 4 -
        V i (timing R (completionEvent V) (j * R)).clock / 4⌋ : ℤ) : ℝ) := by
      refine htc.trans (Finset.sum_le_sum fun i _ => ?_)
      have : V i (timing R (completionEvent V) (j * R)).clock ≤ V i τ :=
        (hV i).2 (Set.mem_Ici.mpr hc0) (Set.mem_Ici.mpr hτ0) hcτ
      have h2 : V i tstar / 4 - V i τ / 4 ≤ V i tstar / 4 -
          V i (timing R (completionEvent V) (j * R)).clock / 4 := by linarith
      exact_mod_cast Int.floor_mono h2
    obtain ⟨hw1, hw2⟩ := window_updates R hR V hV (j * R) hev tstar ht0 hcond
    rw [show (j + 1) * R = j * R + R by ring]
    refine ⟨hw1, ?_⟩
    rw [hd1']
    exact ENNReal.ofReal_le_ofReal hw2

theorem roundTime_mono {n : ℕ} (V : Fin n → ℝ → ℝ)
    (hV : ∀ i, MonotoneOn (V i) (Set.Ici 0)) (S : ℕ) (s s' : ℝ) (hs : 0 ≤ s) (hss : s ≤ s') :
    RennalaUniform.roundTime V S s ≤ RennalaUniform.roundTime V S s' := by
  classical
  by_cases h' : ∃ t, 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, ((⌊V i t - V i s'⌋ : ℤ) : ℝ)
  · have hsub : {t | 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, ((⌊V i t - V i s'⌋ : ℤ) : ℝ)} ⊆
        {t | 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, ((⌊V i t - V i s⌋ : ℤ) : ℝ)} := by
      intro t ht
      refine ⟨ht.1, ht.2.trans (Finset.sum_le_sum fun i _ => ?_)⟩
      have hm := (hV i) (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr (hs.trans hss)) hss
      exact_mod_cast Int.floor_mono (by linarith)
    obtain ⟨t, ht⟩ := h'
    have h : ∃ t, 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, ((⌊V i t - V i s⌋ : ℤ) : ℝ) := ⟨t, hsub ht⟩
    show (if ∃ t, 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, ((⌊V i t - V i s⌋ : ℤ) : ℝ) then _ else ⊤) ≤
      (if ∃ t, 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, ((⌊V i t - V i s'⌋ : ℤ) : ℝ) then _ else ⊤)
    rw [ite_eq_left h, ite_eq_left ⟨t, ht⟩]
    exact ENNReal.ofReal_le_ofReal (csInf_le_csInf ⟨0, fun u hu => hu.1⟩ ⟨t, ht⟩ hsub)
  · show _ ≤ (if ∃ t, 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, ((⌊V i t - V i s'⌋ : ℤ) : ℝ) then _ else ⊤)
    rw [ite_eq_right h']
    exact le_top

theorem stepSize_pos (L σ ε : ℝ) (R : ℕ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (hε : 0 < ε) (hR : 1 ≤ R) : 0 < stepSize L σ ε R := by
  have hR' : 0 < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  unfold OracleTemplate.RingmasterAsgd.stepSize
  split_ifs with hz
  · positivity
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
    exact lt_min (by positivity) (by positivity)

theorem iteration_horizon_sufficient (p : LongTails.Setups.RingmasterIterations.Params) :
    8 * p.R * p.L * p.Δ / p.ε + 16 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2 ≤
      (iterationHorizon p.L p.σ p.ε p.Δ p.R : ℝ) := by
  exact Nat.le_ceil _

theorem time_horizon_sufficient (p : LongTails.Setups.RingmasterUniversalTime.Params)
    (hL : 0 < p.L) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ) :
    8 * threshold p.σ p.ε * p.L * p.Δ / p.ε + 16 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2 ≤
      (timeHorizon p.L p.σ p.ε p.Δ : ℝ) := by
  let R := threshold p.σ p.ε
  let K := timeBlocks p.L p.ε p.Δ
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRs : p.σ ^ 2 / p.ε ≤ (R : ℝ) := by
    have h1 := Nat.le_ceil (p.σ ^ 2 / p.ε)
    have h2 : (⌈p.σ ^ 2 / p.ε⌉₊ : ℝ) ≤ (R : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  have hK : 48 * p.L * p.Δ / p.ε ≤ (K : ℝ) := Nat.le_ceil _
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hLD : 0 ≤ p.L * p.Δ / p.ε := by positivity
  have e1 : 8 * (R : ℝ) * p.L * p.Δ / p.ε = 8 * R * (p.L * p.Δ / p.ε) := by ring
  have e2 : 16 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2 =
      16 * (p.σ ^ 2 / p.ε) * (p.L * p.Δ / p.ε) := by field_simp
  have e3 : 48 * p.L * p.Δ / p.ε = 48 * (p.L * p.Δ / p.ε) := by ring
  change 8 * (R : ℝ) * p.L * p.Δ / p.ε +
    16 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2 ≤ ((R * K : ℕ) : ℝ)
  push_cast
  rw [e1, e2]
  rw [e3] at hK
  nlinarith [mul_le_mul_of_nonneg_right hRs hLD,
    mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ R)]

theorem arrival_accuracy (p : LongTails.Setups.RingmasterIterations.Params) (K : ℕ)
    (hp : LongTails.Setups.RingmasterIterations.spec.valid p)
    (hK : 8 * p.R * p.L * p.Δ / p.ε + 16 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2 ≤ (K : ℝ))
    (I : Instance p.d) (O : Oracle (Query (LongTails.Setups.RingmasterIterations.publicInput p))
      (Reply (LongTails.Setups.RingmasterIterations.publicInput p)))
    (hO : LongTails.Setups.RingmasterIterations.spec.admissible p I O) :
    let q := { LongTails.Setups.RingmasterIterations.publicInput p with K := K }
    LongTails.Setups.RingmasterIterations.spec.successful p I
      (fun z : (ringmasterPoint q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (ringmasterPoint q) (fun _ => K) z.1 z.2)
      ⟨((ringmasterPoint q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  obtain ⟨hg, hlip, hlower, hgap, Ω, m, μ, P, g, arrive, hiid, ho, rfl⟩ := hO
  let := m
  have hlower' (x : Point p.d) : I.f p.x0 - p.Δ ≤ I.f x := by
    linarith [hlower x]
  have hgap' : I.f p.x0 - (I.f p.x0 - p.Δ) = p.Δ := by ring
  obtain ⟨hL, hsig, heps, hΔ0, hR1⟩ := hp
  let q := { LongTails.Setups.RingmasterIterations.publicInput p with K := K }
  let event : ℕ → (Fin q.n → ℝ) → Option (Fin q.n × ℝ) := fun k _ => some (arrive k, 0)
  let ans : ℕ → Query q → Ω → Reply q := fun k qq b =>
    Option.elim qq none (fun r => some (arrive k, 0, g (r.1 (arrive k)) b))
  have hev : ∀ k < q.K, event k (timing q.R event k).starts ≠ none := fun k _ => Option.some_ne_none _
  let a : ℕ → ℕ := fun k => if k < q.K then delays q.R event k else k
  have hab := delays_bound q.R hR1 event q.K hev
  have hexe (j : Fin (q.K + 1)) (ω : ℕ → Ω) :
      execute (arrivalOracle q arrive P g) (ringmasterPoint q) (fun _ => K) j ω =
        delayedIterate g q.gamma a q.x0 ω j.val := by
    have hadv := advance_ringmaster q hR1 g event ans (fun _ _ _ _ => rfl) hev j ω q.K le_rfl
    erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
      (fun c query => ans c query.2 (ω c)) (fun _ _ => rfl)]
    change ((ringmaster q).output (StochasticGradient.advance (fun c s => (ringmaster q).update s
      (ans c ((ringmaster q).query s).2 (ω c))) q.K 0 ((ringmaster q).initial j))).1 = _
    rw [hadv]
    exact ite_eq_left (show j.val ≤ q.K by omega)
  let x : Fin (q.K + 1) → (ℕ → Ω) → Point p.d := fun j ω => delayedIterate g q.gamma a q.x0 ω j.val
  have hm (j : Fin (q.K + 1)) : Measurable (x j) :=
    (iterate_moments I.f g μ P (fun k ω => ω k) p.L p.σ q.gamma q.x0 a hL hg
      hlip ho hiid (fun k => (hab k).1) j.val).1
  have hi (j : Fin (q.K + 1)) : Integrable (fun ω => ‖gradient I.f (x j ω)‖ ^ 2) (P : Measure _) :=
    (iterate_moments I.f g μ P (fun k ω => ω k) p.L p.σ q.gamma q.x0 a hL hg
      hlip ho hiid (fun k => (hab k).1) j.val).2.2.1
  have hacc := iteration_accuracy I.f g μ P (fun k ω => ω k) p.L p.σ p.ε (I.f p.x0 - p.Δ) p.x0 a p.R K
    hL hsig heps hg hlip hlower' ho hiid (fun k => (hab k).1) (fun k => (hab k).2)
    (by rw [hgap']; exact hK)
  have ha : (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1),
      (∫ ω, ‖gradient I.f (x j ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε := by
    have hs := Fin.sum_univ_eq_sum_range (fun k => ∫ ω, ‖gradient I.f (delayedIterate g q.gamma a q.x0 ω k)‖ ^ 2
      ∂(P : Measure (ℕ → Ω))) (q.K + 1)
    show (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1), (fun k => ∫ ω, ‖gradient I.f
      (delayedIterate g q.gamma a q.x0 ω k)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) (j : ℕ) ≤ p.ε
    rw [hs]
    push_cast
    exact hacc
  have hu := uniform_prefix_accuracy P I.f q.K x p.ε hm hi ha
  have hfun : (fun z : Fin (q.K + 1) × (ℕ → Ω) =>
      execute (arrivalOracle q arrive P g) (ringmasterPoint q) (fun _ => K) z.1 z.2) =
      fun z => x z.1 z.2 := by
    funext z
    exact hexe z.1 z.2
  change LongTails.Setups.RingmasterIterations.spec.successful p I
    (fun z : Fin (q.K + 1) × (ℕ → Ω) => execute (arrivalOracle q arrive P g) (ringmasterPoint q) (fun _ => K) z.1 z.2)
    ⟨((PMF.uniformOfFintype (Fin (q.K + 1))).toMeasure).prod (P : Measure (ℕ → Ω)), inferInstance⟩
  rw [hfun]
  exact ⟨hu.1, hu.2.1, hu.2.2.2⟩

theorem iterations_success (p : LongTails.Setups.RingmasterIterations.Params)
    (hp : LongTails.Setups.RingmasterIterations.spec.valid p)
    (I : Instance p.d) (O : Oracle (Query (LongTails.Setups.RingmasterIterations.publicInput p))
      (Reply (LongTails.Setups.RingmasterIterations.publicInput p)))
    (hO : LongTails.Setups.RingmasterIterations.spec.admissible p I O) :
    let q := LongTails.Setups.RingmasterIterations.publicInput p
    LongTails.Setups.RingmasterIterations.spec.successful p I
      (fun z : (ringmasterPoint q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (ringmasterPoint q) (fun _ => iterationHorizon p.L p.σ p.ε p.Δ p.R) z.1 z.2)
      ⟨((ringmasterPoint q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  exact arrival_accuracy p (iterationHorizon p.L p.σ p.ε p.Δ p.R) hp
    (iteration_horizon_sufficient p) I O hO

theorem universal_accuracy (p : LongTails.Setups.RingmasterUniversalTime.Params)
    (hp : 0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧
      ∀ i, RennalaUniform.PowerAssumption (p.power i))
    (I : Instance p.d) (O : Oracle (Query (LongTails.Setups.RingmasterUniversalTime.publicInput p))
      (Reply (LongTails.Setups.RingmasterUniversalTime.publicInput p)))
    (hO : LongTails.Setups.RingmasterUniversalTime.spec.admissible p I O) :
    RennalaUniform.deadline (fun i t => RennalaUniform.work (p.power i) t / 4)
      (max 1 ⌈p.σ ^ 2 / p.ε⌉₊) ⌈48 * p.L * p.Δ / p.ε⌉₊ < ⊤ →
    let q := LongTails.Setups.RingmasterUniversalTime.publicInput p
    LongTails.Setups.RingmasterUniversalTime.spec.successful p I
      (fun z : (ringmaster q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (ringmaster q) (fun _ => timeHorizon p.L p.σ p.ε p.Δ) z.1 z.2)
      ⟨((ringmaster q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  intro hfin
  obtain ⟨hg, hlip, hlower, hgap, Ω, m, μ, P, g, hiid, ho, rfl⟩ := hO
  let := m
  have hlower' (x : Point p.d) : I.f p.x0 - p.Δ ≤ I.f x := by
    linarith [hlower x]
  have hgap' : I.f p.x0 - (I.f p.x0 - p.Δ) = p.Δ := by ring
  obtain ⟨hL, hsig, heps, hΔ0, hpow⟩ := hp
  let q := LongTails.Setups.RingmasterUniversalTime.publicInput p
  let R := threshold p.σ p.ε
  let K := ⌈48 * p.L * p.Δ / p.ε⌉₊
  have hR1 : 1 ≤ R := le_max_left _ _
  let V : Fin p.n → ℝ → ℝ := fun i => RennalaUniform.work (p.power i)
  have hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0) := fun i =>
    RennalaUniform.work_properties (p.power i) (hpow i)
  let event : ℕ → (Fin q.n → ℝ) → Option (Fin q.n × ℝ) := completionEvent V
  let ans : ℕ → Query q → Ω → Reply q := fun _ qq b => eventAnswer q V g qq b
  change LongTails.Setups.RingmasterUniversalTime.spec.successful p I
    (fun z : Fin (q.K + 1) × (ℕ → Ω) =>
      execute (eventOracle q V P g) (ringmaster q) (fun _ => timeHorizon p.L p.σ p.ε p.Δ) z.1 z.2)
    ⟨((PMF.uniformOfFintype (Fin (q.K + 1))).toMeasure).prod (P : Measure (ℕ → Ω)), inferInstance⟩
  obtain ⟨hev0, hclk⟩ := deadline_updates R hR1 V hV K hfin
  have hKq : q.K = K * R := Nat.mul_comm _ _
  have hev : ∀ k < q.K, event k (timing q.R event k).starts ≠ none := fun k hk =>
    hev0 k (by rw [← hKq]; exact hk)
  let a : ℕ → ℕ := fun k => if k < q.K then delays q.R event k else k
  have hab := delays_bound q.R hR1 event q.K hev
  have hexe (j : Fin (q.K + 1)) (ω : ℕ → Ω) :
      execute (eventOracle q V P g) (ringmaster q) (fun _ => timeHorizon p.L p.σ p.ε p.Δ) j ω =
        (delayedIterate g q.gamma a q.x0 ω j.val, (timing q.R event q.K).clock) := by
    have hadv := advance_ringmaster q hR1 g event ans (fun _ _ _ _ => rfl) hev j ω q.K le_rfl
    erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
      (fun c query => ans c query.2 (ω c)) (fun _ _ => rfl)]
    change (ringmaster q).output (StochasticGradient.advance (fun c s => (ringmaster q).update s
      (ans c ((ringmaster q).query s).2 (ω c))) q.K 0 ((ringmaster q).initial j)) = _
    rw [hadv]
    exact Prod.ext (ite_eq_left (show j.val ≤ q.K by omega)) rfl
  let x : Fin (q.K + 1) → (ℕ → Ω) → Point p.d := fun j ω => delayedIterate g q.gamma a q.x0 ω j.val
  have hm (j : Fin (q.K + 1)) : Measurable (x j) :=
    (iterate_moments I.f g μ P (fun k ω => ω k) p.L p.σ q.gamma q.x0 a hL hg
      hlip ho hiid (fun k => (hab k).1) j.val).1
  have hi (j : Fin (q.K + 1)) : Integrable (fun ω => ‖gradient I.f (x j ω)‖ ^ 2) (P : Measure _) :=
    (iterate_moments I.f g μ P (fun k ω => ω k) p.L p.σ q.gamma q.x0 a hL hg
      hlip ho hiid (fun k => (hab k).1) j.val).2.2.1
  have hK : 8 * R * p.L * (I.f p.x0 - (I.f p.x0 - p.Δ)) / p.ε +
      16 * p.σ ^ 2 * p.L * (I.f p.x0 - (I.f p.x0 - p.Δ)) / p.ε ^ 2 ≤ (q.K : ℝ) := by
    rw [hgap']
    exact time_horizon_sufficient p hL heps hΔ0
  have hacc := iteration_accuracy I.f g μ P (fun k ω => ω k) p.L p.σ p.ε (I.f p.x0 - p.Δ) p.x0 a R q.K
    hL hsig heps hg hlip hlower' ho hiid (fun k => (hab k).1) (fun k => (hab k).2) hK
  have ha : (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1),
      (∫ ω, ‖gradient I.f (x j ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε := by
    have hs := Fin.sum_univ_eq_sum_range (fun k => ∫ ω, ‖gradient I.f (delayedIterate g q.gamma a q.x0 ω k)‖ ^ 2
      ∂(P : Measure (ℕ → Ω))) (q.K + 1)
    show (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1), (fun k => ∫ ω, ‖gradient I.f
      (delayedIterate g q.gamma a q.x0 ω k)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) (j : ℕ) ≤ p.ε
    rw [hs]
    push_cast
    exact hacc
  have hu := uniform_prefix_accuracy P I.f q.K x p.ε hm hi ha
  have hfun : (fun z : Fin (q.K + 1) × (ℕ → Ω) =>
      execute (eventOracle q V P g) (ringmaster q) (fun _ => timeHorizon p.L p.σ p.ε p.Δ) z.1 z.2) =
      fun z => (x z.1 z.2, (timing q.R event q.K).clock) := by
    funext z
    exact hexe z.1 z.2
  rw [hfun]
  have hclk' : ENNReal.ofReal (timing q.R event q.K).clock ≤ RennalaUniform.deadline
      (fun i t => RennalaUniform.work (p.power i) t / 4) (threshold p.σ p.ε)
        ⌈48 * p.L * p.Δ / p.ε⌉₊ := by
    have e : (timing q.R event q.K).clock = (timing R (completionEvent V) (K * R)).clock :=
      congrArg (fun k => (timing R (completionEvent V) k).clock) hKq
    rw [e]
    exact hclk
  exact ⟨hu.1.prodMk measurable_const, hu.2.1, hu.2.2.2, Filter.Eventually.of_forall (fun _ => hclk')⟩

theorem universal_success (p : LongTails.Setups.RingmasterUniversalTime.Params)
    (hp : LongTails.Setups.RingmasterUniversalTime.spec.valid p)
    (I : Instance p.d) (O : Oracle (Query (LongTails.Setups.RingmasterUniversalTime.publicInput p))
      (Reply (LongTails.Setups.RingmasterUniversalTime.publicInput p)))
    (hO : LongTails.Setups.RingmasterUniversalTime.spec.admissible p I O) :
    let q := LongTails.Setups.RingmasterUniversalTime.publicInput p
    LongTails.Setups.RingmasterUniversalTime.spec.successful p I
      (fun z : (ringmaster q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (ringmaster q) (fun _ => timeHorizon p.L p.σ p.ε p.Δ) z.1 z.2)
      ⟨((ringmaster q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  exact universal_accuracy p hp.1 I O hO hp.2

theorem finite_domain_iff (p : LongTails.Setups.RingmasterUniversalTime.Params) (Q : Prop) :
    (LongTails.Setups.RingmasterUniversalTime.spec.valid p → Q) ↔
      ((0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧
      ∀ i, RennalaUniform.PowerAssumption (p.power i)) →
        RennalaUniform.deadline (fun i t => RennalaUniform.work (p.power i) t / 4)
      (max 1 ⌈p.σ ^ 2 / p.ε⌉₊) ⌈48 * p.L * p.Δ / p.ε⌉₊ < ⊤ → Q) := by
  exact and_imp

end OracleTemplate.RingmasterAsgd
