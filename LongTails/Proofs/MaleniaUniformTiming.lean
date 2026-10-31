import LongTails.Proofs.SingleOracleCounted
import LongTails.Setups.MaleniaUniformTime
import LongTails.Proofs.RennalaUniformTiming
import LongTails.Proofs.MaleniaStochastic

open MeasureTheory Filter Topology

namespace OracleTemplate.MaleniaUniform

open Rennala

theorem floor_min_attained {n : ℕ} (V : Fin n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0))
    (b : Fin n → ℝ) (Φ : (Fin n → ℤ) → Prop)
    (hne : ∃ t, 0 ≤ t ∧ Φ (fun i => ⌊V i t - b i⌋)) :
    0 ≤ sInf {t | 0 ≤ t ∧ Φ (fun i => ⌊V i t - b i⌋)} ∧
      Φ (fun i => ⌊V i (sInf {t | 0 ≤ t ∧ Φ (fun i => ⌊V i t - b i⌋)}) - b i⌋) := by
  set A := {t | 0 ≤ t ∧ Φ (fun i => ⌊V i t - b i⌋)}
  have hA : A.Nonempty := hne
  have hbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
  set t0 := sInf A
  have ht0 : 0 ≤ t0 := le_csInf hA (fun t ht => ht.1)
  refine ⟨ht0, ?_⟩
  have hev : ∀ᶠ t in 𝓝[Set.Ici t0] t0, ∀ i, V i t - b i < ⌊V i t0 - b i⌋ + 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousWithinAt (V i) (Set.Ici t0) t0 :=
      ((hV i).1 t0 ht0).mono (fun x hx => le_trans ht0 hx)
    have hlt' : V i t0 - b i < ⌊V i t0 - b i⌋ + 1 := Int.lt_floor_add_one _
    exact (hc.sub continuousWithinAt_const).eventually (gt_mem_nhds hlt')
  rcases (mem_nhdsGE_iff_exists_Ico_subset).mp hev with ⟨u, hu, hsub⟩
  by_cases hin : t0 ∈ A
  · exact hin.2
  · have hlt : sInf A < u := hu
    obtain ⟨a, haA, hau⟩ := exists_lt_of_csInf_lt hA hlt
    have hta : t0 ≤ a := csInf_le hbdd haA
    have hprop := hsub ⟨hta, hau⟩
    have heq : (fun i => ⌊V i a - b i⌋) = (fun i => ⌊V i t0 - b i⌋) := by
      funext i
      apply le_antisymm
      · rw [Int.floor_le_iff]
        exact_mod_cast hprop i
      · apply Int.floor_mono
        have := (hV i).2 (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr (ht0.trans hta)) hta
        linarith
    have := haA.2
    rw [heq] at this
    exact this


theorem completion_exact (V : ℝ → ℝ) (hV : ContinuousOn V (Set.Ici 0)) (st : ℝ) (hst : 0 ≤ st)
    (a : ℝ) (h : RennalaUniform.completion V st = some a) : st ≤ a ∧ V a = V st + 1 := by
  classical
  obtain ⟨h1, h2⟩ := RennalaUniform.completion_spec V hV st hst a h
  refine ⟨h1, le_antisymm h2 ?_⟩
  by_cases hex : ∃ t, st ≤ t ∧ V st + 1 ≤ V t
  · have ha : a = sInf {t | st ≤ t ∧ V st + 1 ≤ V t} := by
      have hc : RennalaUniform.completion V st = some (sInf {t | st ≤ t ∧ V st + 1 ≤ V t}) := by
        show (if ∃ u, st ≤ u ∧ V st + 1 ≤ V u then some (sInf {u | st ≤ u ∧ V st + 1 ≤ V u}) else none) = _
        rw [ite_eq_left hex]
      rw [hc] at h
      exact (Option.some.inj h).symm
    set A := {t | st ≤ t ∧ V st + 1 ≤ V t}
    have hA : A.Nonempty := hex
    have hbdd : BddBelow A := ⟨st, fun t ht => ht.1⟩
    by_contra hlt
    push Not at hlt
    have ha0 : 0 ≤ a := hst.trans h1
    have hev : ∀ᶠ t in 𝓝[Set.Ici a] a, V t < V st + 1 := by
      have hc : ContinuousWithinAt V (Set.Ici a) a := (hV a ha0).mono (fun x hx => le_trans ha0 hx)
      exact hc.eventually (gt_mem_nhds hlt)
    rcases (mem_nhdsGE_iff_exists_Ico_subset).mp hev with ⟨u, hu, hsub⟩
    have hlt' : sInf A < u := by rw [← ha]; exact hu
    obtain ⟨t, htA, htu⟩ := exists_lt_of_csInf_lt hA hlt'
    have hat : a ≤ t := by rw [ha]; exact csInf_le hbdd htA
    have hh : V t < V st + 1 := hsub ⟨hat, htu⟩
    have hh2 : V st + 1 ≤ V t := htA.2
    linarith
  · have hn : RennalaUniform.completion V st = none := by
      show (if ∃ u, st ≤ u ∧ V st + 1 ≤ V u then some (sInf {u | st ≤ u ∧ V st + 1 ≤ V u}) else none) = _
      rw [ite_eq_right hex]
    rw [hn] at h
    cases h


theorem harmonic_mono {n S : ℕ} (B B' : Fin n → ℕ) (hle : ∀ i, B i ≤ B' i)
    (h : harmonicReady n S B) : harmonicReady n S B' := by
  refine ⟨fun i => (h.1 i).trans (hle i), ?_⟩
  have hpos (i : Fin n) : (0 : ℝ) < B i := by exact_mod_cast h.1 i
  have hsum : ∑ i, 1 / (B' i : ℝ) ≤ ∑ i, 1 / (B i : ℝ) :=
    Finset.sum_le_sum (fun i _ => one_div_le_one_div_of_le (hpos i) (by exact_mod_cast hle i))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos' : 0 < ∑ i, 1 / (B' i : ℝ) := Finset.sum_pos
    (fun i _ => one_div_pos.mpr (lt_of_lt_of_le (hpos i) (by exact_mod_cast hle i)))
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine h.2.trans ?_
  apply inv_anti₀ (by positivity)
  exact mul_le_mul_of_nonneg_left hsum (by positivity)


theorem round_step_h (q : Public) (V : Fin q.n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0)) (hn : 0 < q.n)
    {Ω : Type} (g : Fin q.n → Point q.d → Ω → Point q.d)
    (r : ℕ) (hr : r < q.K) (s : ℝ) (hs : 0 ≤ s) (tstar : ℝ) (htstar : 0 ≤ tstar)
    (hready : harmonicReady q.n q.S (fun i => (⌊V i tstar - V i s⌋).toNat)) (call0 : ℕ) :
    ∃ (E : ℕ) (c : ℝ) (Bf : Fin q.n → ℕ) (mm : ℕ → ℕ),
      s ≤ c ∧ c ≤ tstar ∧ harmonicReady q.n q.S Bf ∧ (∀ i, (Bf i : ℝ) ≤ V i c - V i s) ∧
      E = ∑ i, Bf i ∧
      ∀ (X sel : Point q.d) (jv : ℕ) (z : ℕ → ℕ → ℕ → Ω),
        StochasticGradient.advance (fun k state => (malenia q).update state
            ((eventAnswer q V g ((malenia q).query state).2 (z k)))) E call0
          (⟨r, fun _ => 0, fun _ => 0, X, fun _ => s, s, jv, sel⟩ : State q) =
        ⟨r + 1, fun _ => 0, fun _ => 0, X - q.gamma • estimator Bf g X (fun c' => z (mm c') r c'),
          fun _ => c, c, jv,
          if jv = r + 1 then X - q.gamma • estimator Bf g X (fun c' => z (mm c') r c') else sel⟩ := by
  classical
  let fl : Fin q.n → ℕ := fun i => (⌊V i tstar - V i s⌋).toNat
  have hfl0 (i : Fin q.n) : 0 ≤ ⌊V i tstar - V i s⌋ := by
    by_contra h
    push Not at h
    have h1 := hready.1 i
    have h2 : (⌊V i tstar - V i s⌋).toNat = 0 := Int.toNat_of_nonpos h.le
    change 1 ≤ (⌊V i tstar - V i s⌋).toNat at h1
    omega
  have hflc (i : Fin q.n) : ((fl i : ℕ) : ℤ) = ⌊V i tstar - V i s⌋ := Int.toNat_of_nonneg (hfl0 i)
  have hfl (i : Fin q.n) : (fl i : ℝ) ≤ V i tstar - V i s := by
    have h := Int.floor_le (V i tstar - V i s)
    rw [← hflc i] at h
    exact_mod_cast h
  have hmono (i : Fin q.n) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : V i a ≤ V i b :=
    (hV i).2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab
  have step_eq : ∀ (st0 : State q) (i : Fin q.n) (t : ℝ) (gr : Point q.d),
      step q st0 (some (i, t, gr)) =
        if harmonicReady q.n q.S (Function.update st0.counts i (st0.counts i + 1)) then
          (⟨st0.round + 1, fun _ => 0, fun _ => 0,
            st0.point - q.gamma • ((1 / (q.n : ℝ)) • ∑ j,
              (1 / ((Function.update st0.counts i (st0.counts i + 1)) j : ℝ)) •
                (Function.update st0.sums i (st0.sums i + gr)) j),
            fun _ => t, t, st0.chosen,
            if st0.chosen = st0.round + 1 then
              st0.point - q.gamma • ((1 / (q.n : ℝ)) • ∑ j,
                (1 / ((Function.update st0.counts i (st0.counts i + 1)) j : ℝ)) •
                  (Function.update st0.sums i (st0.sums i + gr)) j)
            else st0.selected⟩ : State q)
        else ⟨st0.round, Function.update st0.counts i (st0.counts i + 1),
          Function.update st0.sums i (st0.sums i + gr), st0.point,
          Function.update st0.starts i t, t, st0.chosen, st0.selected⟩ := fun _ _ _ _ => rfl
  have hcode (e i : Fin q.n) (j k : ℕ) (h : code q.n i j = code q.n e k) : i = e ∧ j = k := by
    have h2 := code_injective q.n (a₁ := ⟨i, j⟩) (a₂ := ⟨e, k⟩) h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h2
    exact h2
  have main : ∀ (fuel : ℕ) (cnt : Fin q.n → ℕ) (st : Fin q.n → ℝ) (clk : ℝ) (call : ℕ),
      (∀ i, s ≤ st i ∧ st i ≤ clk ∧ V i (st i) = V i s + cnt i ∧ cnt i ≤ fl i) →
      clk ≤ tstar →
      (∀ i b, RennalaUniform.completion (V i) (st i) = some b → clk ≤ b) →
      ¬ harmonicReady q.n q.S cnt →
      ∑ i, (fl i - cnt i) ≤ fuel →
      ∃ (E : ℕ) (c : ℝ) (Bf : Fin q.n → ℕ) (mm : ℕ → ℕ),
        s ≤ c ∧ c ≤ tstar ∧ harmonicReady q.n q.S Bf ∧ (∀ i, cnt i ≤ Bf i) ∧
        (∀ i, (Bf i : ℝ) ≤ V i c - V i s) ∧ E + ∑ i, cnt i = ∑ i, Bf i ∧
        ∀ (X sel : Point q.d) (jv : ℕ) (z : ℕ → ℕ → ℕ → Ω) (sums : Fin q.n → Point q.d),
          StochasticGradient.advance (fun k state => (malenia q).update state
              ((eventAnswer q V g ((malenia q).query state).2 (z k)))) E call
            (⟨r, cnt, sums, X, st, clk, jv, sel⟩ : State q) =
          ⟨r + 1, fun _ => 0, fun _ => 0,
            X - q.gamma • ((1 / (q.n : ℝ)) • ∑ i, (1 / (Bf i : ℝ)) •
              (sums i + ∑ j ∈ Finset.Ico (cnt i) (Bf i), g i X (z (mm (code q.n i j)) r (code q.n i j)))),
            fun _ => c, c, jv,
            if jv = r + 1 then X - q.gamma • ((1 / (q.n : ℝ)) • ∑ i, (1 / (Bf i : ℝ)) •
              (sums i + ∑ j ∈ Finset.Ico (cnt i) (Bf i), g i X (z (mm (code q.n i j)) r (code q.n i j))))
            else sel⟩ := by
    intro fuel
    induction fuel with
    | zero =>
      intro cnt st clk call hinv hclk hH hnr hfuel
      exfalso
      obtain ⟨i0, hi0⟩ : ∃ i, cnt i < fl i := by
        by_contra hall
        push Not at hall
        exact hnr (harmonic_mono fl cnt hall hready)
      have := Finset.single_le_sum (f := fun i => fl i - cnt i) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ i0)
      omega
    | succ fuel ih =>
      intro cnt st clk call hinv hclk hH hnr hfuel
      obtain ⟨i0, hi0⟩ : ∃ i, cnt i < fl i := by
        by_contra hall
        push Not at hall
        exact hnr (harmonic_mono fl cnt hall hready)
      have hst0 (i : Fin q.n) : 0 ≤ st i := hs.trans (hinv i).1
      obtain ⟨a0, ha0, -, ha0t, -⟩ := RennalaUniform.completion_attained (V i0) (hV i0).1 (st i0)
        (hst0 i0) tstar ((hinv i0).2.1.trans hclk) (by
          have h1 := hfl i0
          have h2 := (hinv i0).2.2.1
          have h3 : (cnt i0 : ℝ) + 1 ≤ fl i0 := by exact_mod_cast hi0
          linarith)
      have hspec := RennalaUniform.earliest_spec (fun i => RennalaUniform.completion (V i) (st i))
        (List.finRange q.n)
      obtain ⟨e, a, hea⟩ := hspec.2 ⟨i0, List.mem_finRange i0, a0, ha0⟩
      obtain ⟨hce, hmin⟩ := hspec.1 e a hea
      have hae : a ≤ a0 := hmin i0 (List.mem_finRange i0) a0 ha0
      obtain ⟨hsta, hVa⟩ := completion_exact (V e) (hV e).1 (st e) (hst0 e) a hce
      have hclka : clk ≤ a := hH e a hce
      have hat : a ≤ tstar := hae.trans ha0t
      have ha0' : 0 ≤ a := (hst0 e).trans hsta
      have hcnte : cnt e + 1 ≤ fl e := by
        have h1 : V e a ≤ V e tstar := hmono e ha0' hat
        have h3 : ((cnt e + 1 : ℕ) : ℤ) ≤ ⌊V e tstar - V e s⌋ := Int.le_floor.mpr (by
          push_cast
          linarith [(hinv e).2.2.1])
        have := hflc e
        omega
      have hstep : ∀ (X sel : Point q.d) (jv : ℕ) (z : ℕ → ℕ → ℕ → Ω) (sums : Fin q.n → Point q.d),
          (malenia q).update (⟨r, cnt, sums, X, st, clk, jv, sel⟩ : State q)
            ((eventAnswer q V g ((malenia q).query (⟨r, cnt, sums, X, st, clk, jv, sel⟩ : State q)).2 (z call))) =
          step q ⟨r, cnt, sums, X, st, clk, jv, sel⟩
            (some (e, a, g e X (z call r (code q.n e (cnt e))))) := by
        intro X sel jv z sums
        have hq : (malenia q).query (⟨r, cnt, sums, X, st, clk, jv, sel⟩ : State q) =
            (0, some (X, st, r, cnt)) := by
          show (0, if q.K ≤ r then none else some (X, st, r, cnt)) = _
          rw [ite_eq_right (by omega)]
        rw [hq]
        have hans : (eventAnswer q V g (0, some (X, st, r, cnt)).2 (z call)) =
            some (e, a, g e X (z call r (code q.n e (cnt e)))) := by
          show Option.elim (RennalaUniform.earliest (fun i => RennalaUniform.completion (V i) (st i))
            (List.finRange q.n)) none
              (fun p => some (p.1, p.2, g p.1 X (z call r (code q.n p.1 (cnt p.1))))) = _
          rw [hea]
          rfl
        rw [hans]
        show (if q.K ≤ r then _ else step q _ _) = _
        rw [ite_eq_right (by omega)]
      have hcB (i : Fin q.n) : cnt i ≤ Function.update cnt e (cnt e + 1) i := by
        by_cases hi : i = e
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      have hsumB : ∑ i, Function.update cnt e (cnt e + 1) i = 1 + ∑ i, cnt i := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ e), Finset.sdiff_singleton_eq_erase,
          ← Finset.add_sum_erase _ cnt (Finset.mem_univ e)]
        ring
      have hBV (i : Fin q.n) : (Function.update cnt e (cnt e + 1) i : ℝ) ≤ V i a - V i s := by
        by_cases hi : i = e
        · subst hi
          simp only [Function.update_self]
          push_cast
          linarith [(hinv i).2.2.1]
        · simp only [Function.update_of_ne hi]
          have h1 := hmono i (hst0 i) ((hinv i).2.1.trans hclka)
          linarith [(hinv i).2.2.1]
      by_cases hR : harmonicReady q.n q.S (Function.update cnt e (cnt e + 1))
      · refine ⟨1, a, Function.update cnt e (cnt e + 1), fun _ => call, (hinv e).1.trans hsta, hat, hR,
          hcB, hBV, by rw [hsumB], ?_⟩
        intro X sel jv z sums
        show (malenia q).update _ _ = _
        rw [hstep X sel jv z sums, step_eq]
        dsimp only
        rw [ite_eq_left hR]
        have hG (i : Fin q.n) : Function.update sums e (sums e + g e X (z call r (code q.n e (cnt e)))) i =
            sums i + ∑ j ∈ Finset.Ico (cnt i) (Function.update cnt e (cnt e + 1) i),
              g i X (z call r (code q.n i j)) := by
          by_cases hi : i = e
          · subst hi
            simp [Nat.Ico_succ_singleton]
          · simp [Function.update_of_ne hi]
        simp_rw [hG]
        rfl
      · have hinv' : ∀ i, s ≤ Function.update st e a i ∧ Function.update st e a i ≤ a ∧
            V i (Function.update st e a i) = V i s + Function.update cnt e (cnt e + 1) i ∧
            Function.update cnt e (cnt e + 1) i ≤ fl i := by
          intro i
          by_cases hi : i = e
          · subst hi
            simp only [Function.update_self]
            refine ⟨(hinv i).1.trans hsta, le_rfl, ?_, hcnte⟩
            push_cast
            linarith [(hinv i).2.2.1]
          · simp only [Function.update_of_ne hi]
            exact ⟨(hinv i).1, (hinv i).2.1.trans hclka, (hinv i).2.2.1, (hinv i).2.2.2⟩
        have hH' : ∀ i b, RennalaUniform.completion (V i) (Function.update st e a i) = some b → a ≤ b := by
          intro i b hb
          by_cases hi : i = e
          · subst hi
            simp only [Function.update_self] at hb
            exact (RennalaUniform.completion_spec (V i) (hV i).1 a ha0' b hb).1
          · simp only [Function.update_of_ne hi] at hb
            exact hmin i (List.mem_finRange i) b hb
        have hfuel' : ∑ i, (fl i - Function.update cnt e (cnt e + 1) i) ≤ fuel := by
          have h1 : ∑ i, (fl i - Function.update cnt e (cnt e + 1) i) =
              (fl e - (cnt e + 1)) + ∑ i ∈ Finset.univ.erase e, (fl i - cnt i) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
            simp only [Function.update_self]
            congr 1
            refine Finset.sum_congr rfl (fun i hi => ?_)
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
          have h2 : ∑ i, (fl i - cnt i) = (fl e - cnt e) + ∑ i ∈ Finset.univ.erase e, (fl i - cnt i) :=
            (Finset.add_sum_erase _ _ (Finset.mem_univ e)).symm
          omega
        obtain ⟨E', c, Bf, mm', hsc, hct, hRf, hle', hBf, hE', heq'⟩ :=
          ih (Function.update cnt e (cnt e + 1)) (Function.update st e a) a (call + 1) hinv' hat hH' hR hfuel'
        refine ⟨E' + 1, c, Bf, fun c' => if c' = code q.n e (cnt e) then call else mm' c', hsc, hct, hRf,
          fun i => (hcB i).trans (hle' i), hBf, by rw [hsumB] at hE'; omega, ?_⟩
        intro X sel jv z sums
        show StochasticGradient.advance _ E' (call + 1) ((malenia q).update _ _) = _
        rw [hstep X sel jv z sums, step_eq]
        dsimp only
        rw [ite_eq_right hR, heq' X sel jv z]
        have hG2 (i : Fin q.n) :
            Function.update sums e (sums e + g e X (z call r (code q.n e (cnt e)))) i +
              ∑ j ∈ Finset.Ico (Function.update cnt e (cnt e + 1) i) (Bf i),
                g i X (z (mm' (code q.n i j)) r (code q.n i j)) =
            sums i + ∑ j ∈ Finset.Ico (cnt i) (Bf i),
              g i X (z ((fun c' => if c' = code q.n e (cnt e) then call else mm' c') (code q.n i j))
                r (code q.n i j)) := by
          by_cases hi : i = e
          · subst hi
            simp only [Function.update_self]
            have hlt : cnt i < Bf i := lt_of_lt_of_le (Nat.lt_succ_self _) (by
              have := hle' i
              simpa using this)
            rw [Finset.sum_eq_sum_Ico_succ_bot hlt, ite_eq_left rfl, add_assoc]
            congr 2
            refine Finset.sum_congr rfl (fun j hj => ?_)
            have hne : code q.n i j ≠ code q.n i (cnt i) := by
              intro h
              have := (hcode i i j (cnt i) h).2
              rw [Finset.mem_Ico] at hj
              omega
            simp only [ite_eq_right hne]
          · simp only [Function.update_of_ne hi]
            congr 1
            refine Finset.sum_congr rfl (fun j _ => ?_)
            have hne : code q.n i j ≠ code q.n e (cnt e) := fun h => hi (hcode e i j (cnt e) h).1
            simp only [ite_eq_right hne]
        simp_rw [hG2]
        rfl
  have hinv0 : ∀ i, s ≤ (fun _ : Fin q.n => s) i ∧ (fun _ : Fin q.n => s) i ≤ s ∧
      V i ((fun _ : Fin q.n => s) i) = V i s + (fun _ : Fin q.n => (0 : ℕ)) i ∧
      (fun _ : Fin q.n => (0 : ℕ)) i ≤ fl i := fun i => ⟨le_rfl, le_rfl, by simp, Nat.zero_le _⟩
  have htle : s ≤ tstar := by
    by_contra h
    push Not at h
    have h1 := hfl ⟨0, hn⟩
    have h2 := hready.1 ⟨0, hn⟩
    have h3 : V ⟨0, hn⟩ tstar ≤ V ⟨0, hn⟩ s := hmono ⟨0, hn⟩ htstar h.le
    have h4 : (1 : ℝ) ≤ fl ⟨0, hn⟩ := by exact_mod_cast h2
    linarith
  have hH0 : ∀ i b, RennalaUniform.completion (V i) ((fun _ : Fin q.n => s) i) = some b → s ≤ b :=
    fun i b hb => (RennalaUniform.completion_spec (V i) (hV i).1 s hs b hb).1
  have hnr0 : ¬ harmonicReady q.n q.S (fun _ : Fin q.n => (0 : ℕ)) := by
    intro h
    have h1 : 1 ≤ 0 := h.1 ⟨0, hn⟩
    omega
  obtain ⟨E, c, Bf, mm, hsc, hct, hRf, -, hBf, hE, heq⟩ :=
    main _ (fun _ => 0) (fun _ => s) s call0 hinv0 htle hH0 hnr0 le_rfl
  refine ⟨E, c, Bf, mm, hsc, hct, hRf, hBf, by simpa using hE, ?_⟩
  intro X sel jv z
  rw [heq X sel jv z (fun _ => 0)]
  simp only [zero_add, ← Finset.range_eq_Ico]
  rfl


theorem iterate_congr {d n : ℕ} {Ω : Type} (g : Fin n → Point d → Ω → Point d) (gamma : ℝ)
    (B B' : ℕ → Fin n → ℕ) (x0 : Point d) (w w' : ℕ → ℕ → Ω) (k : ℕ)
    (hB : ∀ r < k, B r = B' r) (hw : ∀ r < k, w r = w' r) :
    iterate g gamma B x0 w k = iterate g gamma B' x0 w' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (fun r hr => hB r (by omega)) (fun r hr => hw r (by omega))
    show iterate g gamma B x0 w k - gamma • estimator (B k) g (iterate g gamma B x0 w k) (w k) =
      iterate g gamma B' x0 w' k - gamma • estimator (B' k) g (iterate g gamma B' x0 w' k) (w' k)
    rw [h1, hB k (by omega), hw k (by omega)]


theorem execute_malenia (q : Public) (V : Fin q.n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0))
    (hn : 0 < q.n) (hSn : q.n ≤ q.S)
    {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω)) (g : Fin q.n → Point q.d → Ω → Point q.d)
    (eta : ℝ) (heta : (q.S : ℝ) / q.n ≤ eta) (hfin : deadline V eta q.K < ⊤) (calls : ℕ)
    (hcalls : ∑ i, ⌊V i (deadline V eta q.K).toReal - V i 0⌋₊ ≤ calls) :
    ∃ (c : ℝ) (B : ℕ → Fin q.n → ℕ) (M : ℕ → ℕ → ℕ),
      ENNReal.ofReal c ≤ deadline V eta q.K ∧ (∀ r, harmonicReady q.n q.S (B r)) ∧
      ∀ (j : Fin (q.K + 1)) (z : ℕ → ℕ → ℕ → Ω),
        executeCounted (eventOracle q V P g) (malenia q) calls j z =
          ((iterate g q.gamma B q.x0 (fun r c' => z (M r c') r c') j.val, c), calls) := by
  classical
  have hadd : ∀ {St : Type} (G : ℕ → St → St) (a b call : ℕ) (x : St),
      StochasticGradient.advance G (a + b) call x =
        StochasticGradient.advance G b (call + a) (StochasticGradient.advance G a call x) := by
    intro St G a
    induction a with
    | zero => intro b call x; rw [Nat.zero_add, Nat.add_zero]; rfl
    | succ a ih =>
      intro b call x
      rw [show a + 1 + b = (a + b) + 1 by omega]
      show StochasticGradient.advance G (a + b) (call + 1) (G call x) = _
      rw [ih, show call + 1 + a = call + (a + 1) by omega]
      rfl
  have htop : ∀ r m, deadline V eta r = ⊤ → deadline V eta (r + m) = ⊤ := by
    intro r m h
    induction m with
    | zero => exact h
    | succ m ih =>
      show (if deadline V eta (r + m) = ⊤ then ⊤ else _) = ⊤
      rw [ite_eq_left ih]
  have hfinr : ∀ r, r ≤ q.K → deadline V eta r ≠ ⊤ := by
    intro r hr h
    have := htop r (q.K - r) h
    rw [show r + (q.K - r) = q.K by omega] at this
    exact (ne_of_lt hfin) this
  have hmono (i : Fin q.n) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : V i a ≤ V i b :=
    (hV i).2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab
  have hnr : (0 : ℝ) < q.n := by exact_mod_cast hn
  have hS0 : harmonicReady q.n q.S (fun _ => q.S) := by
    refine ⟨fun _ => le_trans (Nat.succ_le_of_lt hn) hSn, ?_⟩
    have hSr : (0 : ℝ) < q.S := lt_of_lt_of_le hnr (by exact_mod_cast hSn)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have he : ((1 / (q.n : ℝ)) * ((q.n : ℝ) * (1 / (q.S : ℝ))))⁻¹ = q.S := by field_simp
    rw [he, div_le_iff₀ hnr]
    have : (1 : ℝ) ≤ q.n := by exact_mod_cast hn
    nlinarith
  let Φ : (Fin q.n → ℤ) → Prop := fun Fv => (∀ i, (1 : ℤ) ≤ Fv i) ∧
    eta ≤ ((1 / (q.n : ℝ)) * ∑ i, 1 / (Fv i : ℝ))⁻¹
  have main : ∀ r, r ≤ q.K → ∃ (c : ℝ) (E : ℕ) (B : ℕ → Fin q.n → ℕ) (M : ℕ → ℕ → ℕ),
      0 ≤ c ∧ ENNReal.ofReal c ≤ deadline V eta r ∧ (∀ r', harmonicReady q.n q.S (B r')) ∧
      (∀ i, ((∑ r' ∈ Finset.range r, B r' i : ℕ) : ℝ) ≤ V i c - V i 0) ∧
      E = ∑ r' ∈ Finset.range r, ∑ i, B r' i ∧
      ∀ (j : Fin (q.K + 1)) (z : ℕ → ℕ → ℕ → Ω),
        StochasticGradient.advance (fun k state => (malenia q).update state ((eventAnswer q V g ((malenia q).query state).2 (z k)))) E 0 ((malenia q).initial j) =
          (⟨r, fun _ => 0, fun _ => 0, iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') r,
            fun _ => c, c, j.val,
            if j.val ≤ r then iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') j.val
            else q.x0⟩ : State q) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨0, 0, fun _ _ => q.S, fun _ _ => 0, le_rfl, by simp, fun _ => hS0, ?_, rfl, ?_⟩
      · intro i; simp
      · intro j z
        show (⟨0, fun _ => 0, fun _ => 0, q.x0, fun _ => 0, 0, j.val, q.x0⟩ : State q) = _
        by_cases hj : j.val = 0
        · rw [ite_eq_left (by omega), hj]; rfl
        · rw [ite_eq_right (by omega)]; rfl
    | succ r ih =>
      intro hr
      obtain ⟨c, E, B, M, hc0, hcd, hB, hBV, hE, hadv⟩ := ih (by omega)
      have hdr := hfinr r (by omega)
      have hdr1 := hfinr (r + 1) hr
      set τ := (deadline V eta r).toReal with hτ
      have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
      have hcτ : c ≤ τ := by
        rw [← ENNReal.ofReal_toReal hdr] at hcd
        exact (ENNReal.ofReal_le_ofReal_iff hτ0).mp hcd
      have hd1 : deadline V eta (r + 1) = roundTime V eta τ := by
        show (if deadline V eta r = ⊤ then ⊤ else _) = _
        rw [ite_eq_right hdr]
      have hex : ∃ t, 0 ≤ t ∧ Φ (fun i => ⌊V i t - V i τ⌋) := by
        by_contra hne
        apply hdr1
        rw [hd1]
        show (if ∃ t, 0 ≤ t ∧ (∀ i, (1 : ℤ) ≤ ⌊V i t - V i τ⌋) ∧
          eta ≤ ((1 / (q.n : ℝ)) * ∑ i, 1 / (⌊V i t - V i τ⌋ : ℝ))⁻¹ then _ else ⊤) = ⊤
        rw [ite_eq_right hne]
      obtain ⟨ht0, htc⟩ := floor_min_attained V hV (fun i => V i τ) Φ hex
      set tstar := sInf {t | 0 ≤ t ∧ Φ (fun i => ⌊V i t - V i τ⌋)} with htstar
      have hd1' : deadline V eta (r + 1) = ENNReal.ofReal tstar := by
        rw [hd1]
        show (if ∃ t, 0 ≤ t ∧ (∀ i, (1 : ℤ) ≤ ⌊V i t - V i τ⌋) ∧
          eta ≤ ((1 / (q.n : ℝ)) * ∑ i, 1 / (⌊V i t - V i τ⌋ : ℝ))⁻¹ then _ else ⊤) = _
        rw [ite_eq_left hex]
      have hready : harmonicReady q.n q.S (fun i => (⌊V i tstar - V i c⌋).toNat) := by
        have hτF : harmonicReady q.n q.S (fun i => (⌊V i tstar - V i τ⌋).toNat) := by
          refine ⟨fun i => by have h1 : (1 : ℤ) ≤ ⌊V i tstar - V i τ⌋ := htc.1 i; show 1 ≤ (⌊V i tstar - V i τ⌋).toNat; omega, ?_⟩
          have hcast : ∀ i, (((⌊V i tstar - V i τ⌋).toNat : ℕ) : ℝ) = (⌊V i tstar - V i τ⌋ : ℝ) := by
            intro i
            have h1 : (0 : ℤ) ≤ ⌊V i tstar - V i τ⌋ := le_trans (by norm_num) (htc.1 i)
            exact_mod_cast Int.toNat_of_nonneg h1
          simp_rw [hcast]
          exact heta.trans htc.2
        refine harmonic_mono _ _ (fun i => ?_) hτF
        have h1 : V i c ≤ V i τ := hmono i hc0 hcτ
        have h2 : ⌊V i tstar - V i τ⌋ ≤ ⌊V i tstar - V i c⌋ := Int.floor_mono (by linarith)
        omega
      obtain ⟨Er, c', Bf, mm, hcc', hc't, hRf, hBfV, hEr, hround⟩ :=
        round_step_h q V hV hn g r (by omega) c hc0 tstar ht0 hready E
      refine ⟨c', E + Er, Function.update B r Bf, Function.update M r mm, hc0.trans hcc', ?_, ?_, ?_, ?_, ?_⟩
      · rw [hd1']
        exact ENNReal.ofReal_le_ofReal hc't
      · intro r'
        by_cases h : r' = r
        · subst h; simp only [Function.update_self]; exact hRf
        · simp only [Function.update_of_ne h]; exact hB r'
      · intro i
        rw [Finset.sum_range_succ, Function.update_self]
        have hs : ∑ r' ∈ Finset.range r, Function.update B r Bf r' i = ∑ r' ∈ Finset.range r, B r' i :=
          Finset.sum_congr rfl (fun r' hr' => by
            rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hr'))])
        rw [hs, Nat.cast_add]
        linarith [hBV i, hBfV i]
      · rw [hE, hEr, Finset.sum_range_succ, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl (fun r' hr' => ?_)
        rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hr'))]
      · intro j z
        have hcong : ∀ k, k ≤ r → iterate g q.gamma (Function.update B r Bf) q.x0
            (fun r' c'' => z (Function.update M r mm r' c'') r' c'') k =
            iterate g q.gamma B q.x0 (fun r' c'' => z (M r' c'') r' c'') k := by
          intro k hk
          refine iterate_congr g q.gamma _ _ q.x0 _ _ k (fun r' hr' => ?_) (fun r' hr' => ?_)
          · rw [Function.update_of_ne (by omega)]
          · funext c''
            rw [Function.update_of_ne (by omega)]
        rw [hadd, hadv j z, Nat.zero_add, hround]
        have hit : iterate g q.gamma (Function.update B r Bf) q.x0
            (fun r' c'' => z (Function.update M r mm r' c'') r' c'') (r + 1) =
            iterate g q.gamma B q.x0 (fun r' c'' => z (M r' c'') r' c'') r -
              q.gamma • estimator Bf g (iterate g q.gamma B q.x0 (fun r' c'' => z (M r' c'') r' c'') r)
                (fun c'' => z (mm c'') r c'') := by
          show iterate g q.gamma (Function.update B r Bf) q.x0
              (fun r' c'' => z (Function.update M r mm r' c'') r' c'') r -
            q.gamma • estimator (Function.update B r Bf r) g
              (iterate g q.gamma (Function.update B r Bf) q.x0
                (fun r' c'' => z (Function.update M r mm r' c'') r' c'') r)
              (fun c'' => z (Function.update M r mm r c'') r c'') = _
          rw [hcong r le_rfl, Function.update_self]
          simp only [Function.update_self]
        rw [← hit]
        by_cases hj : j.val = r + 1
        · rw [ite_eq_left hj, ite_eq_left (by omega), hj]
        · rw [ite_eq_right hj]
          by_cases hjr : j.val ≤ r
          · rw [ite_eq_left hjr, ite_eq_left (by omega), hcong j.val hjr]
          · rw [ite_eq_right hjr, ite_eq_right (by omega)]
  obtain ⟨c, E, B, M, hc0, hcd, hB, hBV, hE, hadv⟩ := main q.K le_rfl
  have hEcalls : E ≤ calls := by
    have hτ0 : 0 ≤ (deadline V eta q.K).toReal := ENNReal.toReal_nonneg
    have hcτ : c ≤ (deadline V eta q.K).toReal := by
      rw [← ENNReal.ofReal_toReal (ne_of_lt hfin)] at hcd
      exact (ENNReal.ofReal_le_ofReal_iff hτ0).mp hcd
    rw [hE, Finset.sum_comm]
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hcalls
    apply Nat.le_floor
    have h1 := hmono i hc0 hcτ
    linarith [hBV i]
  refine ⟨c, B, M, hcd, hB, fun j z => ?_⟩
  have hidle : ∀ m call, StochasticGradient.advance (fun k state => (malenia q).update state ((eventAnswer q V g ((malenia q).query state).2 (z k)))) m call
      (⟨q.K, fun _ => 0, fun _ => 0, iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') q.K,
        fun _ => c, c, j.val,
        if j.val ≤ q.K then iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') j.val
        else q.x0⟩ : State q) =
      ⟨q.K, fun _ => 0, fun _ => 0, iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') q.K,
        fun _ => c, c, j.val,
        if j.val ≤ q.K then iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') j.val
        else q.x0⟩ := by
    intro m
    induction m with
    | zero => intro call; rfl
    | succ m ih =>
      intro call
      show StochasticGradient.advance (fun k state => (malenia q).update state ((eventAnswer q V g ((malenia q).query state).2 (z k)))) m (call + 1) ((malenia q).update _ _) = _
      have hu : (malenia q).update (⟨q.K, fun _ => 0, fun _ => 0,
          iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') q.K, fun _ => c, c, j.val,
          if j.val ≤ q.K then iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') j.val
          else q.x0⟩ : State q) ((eventAnswer q V g ((malenia q).query ⟨q.K, fun _ => 0, fun _ => 0,
              iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') q.K, fun _ => c, c, j.val,
              if j.val ≤ q.K then iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') j.val
              else q.x0⟩).2 (z call))) =
          ⟨q.K, fun _ => 0, fun _ => 0,
            iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') q.K, fun _ => c, c, j.val,
            if j.val ≤ q.K then iterate g q.gamma B q.x0 (fun r' c' => z (M r' c') r' c') j.val
            else q.x0⟩ := by
        show (if q.K ≤ q.K then _ else _) = _
        erw [ite_eq_left le_rfl]
      rw [hu, ih]
  erw [executeCounted_advance _ _ _ _ _ (fun k query => eventAnswer q V g query.2 (z k))
    (fun _ _ => rfl)]
  change ((malenia q).output (StochasticGradient.advance (fun k state => (malenia q).update state ((eventAnswer q V g ((malenia q).query state).2 (z k)))) calls 0 ((malenia q).initial j)), calls) = _
  rw [show calls = E + (calls - E) by omega, hadd, hadv j z, hidle]
  show ((if j.val ≤ q.K then _ else q.x0, c), E + (calls - E)) = _
  rw [ite_eq_left (by omega), show E + (calls - E) = calls by omega]


theorem environment_transport {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (M : ℕ → ℕ → ℕ) :
    (Measure.map (fun ξ (_ : ℕ) => arrays ξ) (P : Measure (ℕ → Ω))).map
        (fun (z : ℕ → ℕ → ℕ → Ω) (r c : ℕ) => z (M r c) r c) =
      Measure.map arrays (P : Measure (ℕ → Ω)) := by
  have h1 : Measurable (fun (z : ℕ → ℕ → ℕ → Ω) (r c : ℕ) => z (M r c) r c) := by fun_prop
  have h2 : Measurable (fun (ξ : ℕ → Ω) (_ : ℕ) => arrays ξ) := by
    show Measurable (fun (ξ : ℕ → Ω) (_ : ℕ) (r c : ℕ) => ξ (Nat.pair r c))
    fun_prop
  rw [Measure.map_map h1 h2]
  rfl


end OracleTemplate.MaleniaUniform
