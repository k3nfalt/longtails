import outputs.Proofs.RingmasterStochastic
import outputs.Setups.RingmasterUniversalTime
import LongTails.Proofs.MaleniaUniformTiming

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

end OracleTemplate.RingmasterAsgd
