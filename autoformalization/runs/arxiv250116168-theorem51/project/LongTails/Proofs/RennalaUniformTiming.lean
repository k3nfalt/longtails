import LongTails.Proofs.SingleOracleCounted
import LongTails.Setups.RennalaUniformTime
import LongTails.Proofs.SgdExecution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Filter Topology

namespace OracleTemplate.RennalaUniform

open Rennala

theorem work_properties (v : ℝ → ℝ) (hv : PowerAssumption v) :
    ContinuousOn (work v) (Set.Ici 0) ∧ MonotoneOn (work v) (Set.Ici 0) := by
  obtain ⟨hv, -, hint⟩ := hv
  constructor
  · intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have hu : (0 : ℝ) ≤ t + 1 := by linarith
    have hc := intervalIntegral.continuousOn_primitive_interval' (hint (t + 1) hu)
      (show (0 : ℝ) ∈ Set.uIcc (0 : ℝ) (t + 1) from Set.left_mem_uIcc)
    have hmem : t ∈ Set.uIcc (0 : ℝ) (t + 1) := by
      rw [Set.uIcc_of_le hu]; exact ⟨ht0, by linarith⟩
    have hnhds : Set.uIcc (0 : ℝ) (t + 1) ∈ 𝓝[Set.Ici 0] t := by
      rw [Set.uIcc_of_le hu]
      exact mem_nhdsWithin.mpr ⟨Set.Iio (t + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, le_of_lt hx.1⟩⟩
    exact (hc t hmem).mono_of_mem_nhdsWithin hnhds
  · intro a ha b hb hab
    have ha0 : (0 : ℝ) ≤ a := ha
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint a ha0)
      ((hint b (ha0.trans hab)).mono_set (by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le (ha0.trans hab)]
        exact Set.Icc_subset_Icc ha0 le_rfl))
    have hnn : 0 ≤ ∫ τ in a..b, v τ :=
      intervalIntegral.integral_nonneg hab (fun x hx => hv x (ha0.trans hx.1))
    show ∫ τ in (0 : ℝ)..a, v τ ≤ ∫ τ in (0 : ℝ)..b, v τ
    linarith


theorem min_attained {n : ℕ} (V : Fin n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0))
    (b : Fin n → ℝ) (η : ℝ) (hne : ∃ t, 0 ≤ t ∧ η ≤ ∑ i, (⌊V i t - b i⌋ : ℝ)) :
    0 ≤ sInf {t | 0 ≤ t ∧ η ≤ ∑ i, (⌊V i t - b i⌋ : ℝ)} ∧
      η ≤ ∑ i, (⌊V i (sInf {t | 0 ≤ t ∧ η ≤ ∑ i, (⌊V i t - b i⌋ : ℝ)}) - b i⌋ : ℝ) := by
  set A := {t | 0 ≤ t ∧ η ≤ ∑ i, (⌊V i t - b i⌋ : ℝ)}
  have hA : A.Nonempty := hne
  have hbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
  set t0 := sInf A
  have ht0 : 0 ≤ t0 := le_csInf hA (fun t ht => ht.1)
  refine ⟨ht0, ?_⟩
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ t in 𝓝[Set.Ici t0] t0, ∀ i, V i t - b i < ⌊V i t0 - b i⌋ + 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousWithinAt (V i) (Set.Ici t0) t0 :=
      ((hV i).1 t0 ht0).mono (fun x hx => le_trans ht0 hx)
    have hlt' : V i t0 - b i < ⌊V i t0 - b i⌋ + 1 := Int.lt_floor_add_one _
    have := (hc.sub continuousWithinAt_const).eventually (gt_mem_nhds hlt')
    exact this
  rcases (mem_nhdsGE_iff_exists_Ico_subset).mp hev with ⟨u, hu, hsub⟩
  obtain ⟨a, haA, hau⟩ := exists_lt_of_csInf_lt hA (show sInf A < u from hu)
  have hta : t0 ≤ a := csInf_le hbdd haA
  have hprop := hsub ⟨hta, hau⟩
  have hle : ∑ i, (⌊V i a - b i⌋ : ℝ) ≤ ∑ i, (⌊V i t0 - b i⌋ : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have h := hprop i
    have : ⌊V i a - b i⌋ ≤ ⌊V i t0 - b i⌋ := by
      rw [Int.floor_le_iff]
      exact_mod_cast h
    exact_mod_cast this
  linarith [haA.2]


theorem completion_attained (V : ℝ → ℝ) (hV : ContinuousOn V (Set.Ici 0)) (st : ℝ) (hst : 0 ≤ st)
    (t : ℝ) (ht : st ≤ t) (hVt : V st + 1 ≤ V t) :
    ∃ a, completion V st = some a ∧ st ≤ a ∧ a ≤ t ∧ V a ≤ V st + 1 := by
  classical
  set B := {u | st ≤ u ∧ V st + 1 ≤ V u}
  have hB : B.Nonempty := ⟨t, ht, hVt⟩
  have hbdd : BddBelow B := ⟨st, fun u hu => hu.1⟩
  have hex : ∃ u, st ≤ u ∧ V st + 1 ≤ V u := ⟨t, ht, hVt⟩
  refine ⟨sInf B, ?_, le_csInf hB (fun u hu => hu.1), csInf_le hbdd ⟨ht, hVt⟩, ?_⟩
  · show (if ∃ u, st ≤ u ∧ V st + 1 ≤ V u then some (sInf {u | st ≤ u ∧ V st + 1 ≤ V u}) else none) = _
    rw [ite_eq_left hex]
  · set a := sInf B
    have hsa : st ≤ a := le_csInf hB (fun u hu => hu.1)
    rcases hsa.eq_or_lt with h | h
    · rw [← h]; linarith
    · have hc : ContinuousWithinAt V (Set.Iio a) a := by
        have := hV a (le_trans hst hsa)
        exact this.mono_of_mem_nhdsWithin (by
          exact mem_nhdsWithin.mpr ⟨Set.Ioi st, isOpen_Ioi, h, fun x hx => le_of_lt (lt_of_le_of_lt hst hx.1)⟩)
      have hlim : Tendsto V (𝓝[Set.Iio a] a) (𝓝 (V a)) := hc
      have hev : ∀ᶠ u in 𝓝[Set.Iio a] a, V u ≤ V st + 1 := by
        have hmem : Set.Ioo st a ∈ 𝓝[Set.Iio a] a := Ioo_mem_nhdsLT h
        filter_upwards [hmem] with u hu
        by_contra hcon
        push Not at hcon
        have : a ≤ u := csInf_le hbdd ⟨le_of_lt hu.1, le_of_lt hcon⟩
        linarith [hu.2]
      exact le_of_tendsto hlim hev


theorem completion_spec (V : ℝ → ℝ) (hV : ContinuousOn V (Set.Ici 0)) (st : ℝ) (hst : 0 ≤ st) (a : ℝ)
    (h : completion V st = some a) : st ≤ a ∧ V a ≤ V st + 1 := by
  classical
  by_cases hex : ∃ t, st ≤ t ∧ V st + 1 ≤ V t
  · obtain ⟨t, ht, hVt⟩ := hex
    obtain ⟨a', ha', h1, -, h2⟩ := completion_attained V hV st hst t ht hVt
    rw [ha'] at h
    cases h
    exact ⟨h1, h2⟩
  · have hnone : completion V st = none := by
      show (if ∃ u, st ≤ u ∧ V st + 1 ≤ V u then some (sInf {u | st ≤ u ∧ V st + 1 ≤ V u}) else none) = _
      rw [ite_eq_right hex]
    rw [hnone] at h
    cases h


theorem earliest_spec {n : ℕ} (c : Fin n → Option ℝ) (l : List (Fin n)) :
    (∀ j a, earliest c l = some (j, a) → c j = some a ∧ ∀ i ∈ l, ∀ b, c i = some b → a ≤ b) ∧
      ((∃ i ∈ l, ∃ b, c i = some b) → ∃ j a, earliest c l = some (j, a)) := by
  induction l with
  | nil =>
    constructor
    · intro j a h
      change (none : Option (Fin n × ℝ)) = some (j, a) at h
      cases h
    · rintro ⟨i, hi, -⟩
      cases hi
  | cons i rest ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hdef : earliest c (i :: rest) = Option.elim (c i) (earliest c rest)
        (fun a => Option.elim (earliest c rest) (some (i, a))
          (fun p => if a ≤ p.2 then some (i, a) else some p)) := rfl
    rw [hdef]
    constructor
    · rcases hci : c i with _ | a'
      · intro j a h
        change earliest c rest = some (j, a) at h
        obtain ⟨h1, h2⟩ := ih1 j a h
        refine ⟨h1, fun i' hi' b hb => ?_⟩
        rcases List.mem_cons.mp hi' with rfl | hr
        · rw [hci] at hb; cases hb
        · exact h2 i' hr b hb
      · rcases her : earliest c rest with _ | ⟨j', b'⟩
        · intro j a h
          change some (i, a') = some (j, a) at h
          rw [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hci, fun i' hi' b hb => ?_⟩
          rcases List.mem_cons.mp hi' with rfl | hr
          · rw [hci] at hb; cases hb; exact le_rfl
          · exfalso
            obtain ⟨j0, a0, h0⟩ := ih2 ⟨i', hr, b, hb⟩
            rw [her] at h0; cases h0
        · intro j a h
          change (if a' ≤ b' then some (i, a') else some (j', b')) = some (j, a) at h
          obtain ⟨hj'1, hj'2⟩ := ih1 j' b' her
          by_cases hab : a' ≤ b'
          · rw [ite_eq_left hab, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨hci, fun i' hi' b hb => ?_⟩
            rcases List.mem_cons.mp hi' with rfl | hr
            · rw [hci] at hb; cases hb; exact le_rfl
            · exact hab.trans (hj'2 i' hr b hb)
          · rw [ite_eq_right hab, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨hj'1, fun i' hi' b hb => ?_⟩
            rcases List.mem_cons.mp hi' with rfl | hr
            · rw [hci] at hb; cases hb; exact le_of_lt (not_le.mp hab)
            · exact hj'2 i' hr b hb
    · rintro ⟨i', hi', b, hb⟩
      rcases hci : c i with _ | a'
      · change ∃ j a, earliest c rest = some (j, a)
        rcases List.mem_cons.mp hi' with rfl | hr
        · rw [hci] at hb; cases hb
        · exact ih2 ⟨i', hr, b, hb⟩
      · rcases her : earliest c rest with _ | ⟨j', b'⟩
        · exact ⟨i, a', rfl⟩
        · by_cases hab : a' ≤ b'
          · exact ⟨i, a', by change (if a' ≤ b' then some (i, a') else some (j', b')) = _; rw [ite_eq_left hab]⟩
          · exact ⟨j', b', by change (if a' ≤ b' then some (i, a') else some (j', b')) = _; rw [ite_eq_right hab]⟩


theorem round_step (q : Public) (V : Fin q.n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0)) (hS : 0 < q.S)
    {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω)) (g : Point q.d → Ω → Point q.d)
    (r : ℕ) (hr : r < q.K) (s : ℝ) (hs : 0 ≤ s) (tstar : ℝ) (htstar : 0 ≤ tstar)
    (hcond : (q.S : ℝ) ≤ ∑ i, (⌊V i tstar - V i s⌋ : ℝ)) :
    ∃ c, s ≤ c ∧ c ≤ tstar ∧ ∀ (X sel : Point q.d) (jv : ℕ) (ξ : ℕ → Ω),
      StochasticGradient.advance (fun k state => (rennala q).update state
          ((eventOracle q V P g).answer k ((rennala q).query state) (ξ k))) q.S (r * q.S)
        (⟨r, 0, 0, X, fun _ => s, s, jv, sel⟩ : State q) =
      ⟨r + 1, 0, 0, X - q.gamma • batchEstimator q.S g X (fun i => ξ (r * q.S + i.val)),
        fun _ => c, c, jv, if jv = r + 1 then X - q.gamma • batchEstimator q.S g X (fun i => ξ (r * q.S + i.val)) else sel⟩ := by
  classical
  have hadv : ∀ {St : Type} (F : ℕ → St → St) (m call : ℕ) (x : St),
      StochasticGradient.advance F (m + 1) call x = F (call + m) (StochasticGradient.advance F m call x) := by
    intro St F m
    induction m with
    | zero => intro call x; rfl
    | succ m ih =>
      intro call x
      show StochasticGradient.advance F (m + 1) (call + 1) (F call x) = _
      rw [ih (call + 1) (F call x)]
      show F (call + 1 + m) _ = F (call + (m + 1)) (StochasticGradient.advance F (m + 1) call x)
      rw [show call + 1 + m = call + (m + 1) by omega]
      rfl
  have hSr : (0 : ℝ) < q.S := by exact_mod_cast hS
  -- one event: from a mid-round configuration, the next event exists, is at most tstar, and preserves the invariant
  have hevent : ∀ (st : Fin q.n → ℝ) (cnt : Fin q.n → ℕ),
      (∀ i, s ≤ st i ∧ st i ≤ tstar ∧ V i (st i) ≤ V i s + cnt i) → (∑ i, cnt i) < q.S →
      ∃ j a, earliest (fun i => completion (V i) (st i)) (List.finRange q.n) = some (j, a) ∧
        st j ≤ a ∧ a ≤ tstar ∧ V j a ≤ V j s + (cnt j + 1) := by
    intro st cnt hinv hlt
    have hex : ∃ i, (cnt i : ℝ) + 1 ≤ V i tstar - V i s := by
      by_contra hno
      push Not at hno
      have hfl : ∀ i, (⌊V i tstar - V i s⌋ : ℝ) ≤ cnt i := by
        intro i
        have h := hno i
        have : ⌊V i tstar - V i s⌋ ≤ (cnt i : ℤ) := by
          rw [Int.floor_le_iff]; push_cast; linarith
        exact_mod_cast this
      have h1 : ∑ i, (⌊V i tstar - V i s⌋ : ℝ) ≤ ∑ i, (cnt i : ℝ) := Finset.sum_le_sum (fun i _ => hfl i)
      have h2 : (∑ i, (cnt i : ℝ)) < q.S := by exact_mod_cast hlt
      linarith
    obtain ⟨i, hi⟩ := hex
    obtain ⟨ci, hci, -, hcit, -⟩ := completion_attained (V i) (hV i).1 (st i) (hs.trans (hinv i).1)
      tstar (hinv i).2.1 (by linarith [(hinv i).2.2])
    obtain ⟨j, a, hja⟩ := (earliest_spec (fun i => completion (V i) (st i)) (List.finRange q.n)).2
      ⟨i, List.mem_finRange i, ci, hci⟩
    obtain ⟨hcj, hmin⟩ := (earliest_spec (fun i => completion (V i) (st i)) (List.finRange q.n)).1 j a hja
    have hai : a ≤ ci := hmin i (List.mem_finRange i) ci hci
    obtain ⟨hsta, hVa⟩ := completion_spec (V j) (hV j).1 (st j) (hs.trans (hinv j).1) a hcj
    refine ⟨j, a, hja, hsta, hai.trans hcit, ?_⟩
    have := (hinv j).2.2
    linarith
  -- mid-round invariant
  have hmid : ∀ m, m < q.S → ∃ (st : Fin q.n → ℝ) (clk : ℝ) (cnt : Fin q.n → ℕ),
      (∀ i, s ≤ st i ∧ st i ≤ tstar ∧ V i (st i) ≤ V i s + cnt i) ∧ (∑ i, cnt i = m) ∧ s ≤ clk ∧
      ∀ (X sel : Point q.d) (jv : ℕ) (ξ : ℕ → Ω),
        StochasticGradient.advance (fun k state => (rennala q).update state
          ((eventOracle q V P g).answer k ((rennala q).query state) (ξ k))) m (r * q.S)
          (⟨r, 0, 0, X, fun _ => s, s, jv, sel⟩ : State q) =
        ⟨r, m, ∑ l ∈ Finset.range m, (1 / (q.S : ℝ)) • g X (ξ (r * q.S + l)), X, st, clk, jv, sel⟩ := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => s, s, fun _ => 0, fun i => ⟨le_rfl, ?_, by simp⟩, by simp, le_rfl, ?_⟩
      · by_contra hlt
        push Not at hlt
        have : ∀ i, (⌊V i tstar - V i s⌋ : ℝ) ≤ 0 := by
          intro i
          have hm := (hV i).2 (show tstar ∈ Set.Ici (0:ℝ) from htstar) (show s ∈ Set.Ici (0:ℝ) from hs) hlt.le
          have : ⌊V i tstar - V i s⌋ ≤ 0 := Int.floor_nonpos (by linarith)
          exact_mod_cast this
        have := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => this i)
        linarith
      · intro X sel jv ξ
        simp only [Finset.range_zero, Finset.sum_empty]
        rfl
    | succ m ih =>
      intro hm1
      obtain ⟨st, clk, cnt, hinv, hsum, hclk, heq⟩ := ih (by omega)
      obtain ⟨j, a, hja, hsta, hat, hVa⟩ := hevent st cnt hinv (by omega)
      refine ⟨Function.update st j a, a, Function.update cnt j (cnt j + 1), ?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hij : i = j
        · subst hij
          simp only [Function.update_self]
          exact ⟨(hinv i).1.trans hsta, hat, by push_cast; linarith⟩
        · simp only [Function.update_of_ne hij]
          exact hinv i
      · rw [Finset.sum_update_of_mem (Finset.mem_univ j), ← hsum, Finset.sdiff_singleton_eq_erase,
          ← Finset.add_sum_erase _ cnt (Finset.mem_univ j)]
        ring
      · exact (hinv j).1.trans hsta
      · intro X sel jv ξ
        erw [hadv, heq X sel jv ξ]
        have hq : (rennala q).query (⟨r, m, ∑ l ∈ Finset.range m, (1 / (q.S : ℝ)) • g X (ξ (r * q.S + l)), X, st, clk, jv, sel⟩ : State q) =
            (0, some (X, st)) := by
          show (0, if q.K ≤ r then none else some (X, st)) = (0, some (X, st))
          rw [ite_eq_right (by omega)]
        rw [hq]
        have hans : (eventOracle q V P g).answer (r * q.S + m) (0, some (X, st)) (ξ (r * q.S + m)) =
            some (j, a, g X (ξ (r * q.S + m))) := by
          show eventAnswer q V g (some (X, st)) (ξ (r * q.S + m)) = _
          show Option.elim (earliest (fun i => completion (V i) (st i)) (List.finRange q.n)) none
            (fun p => some (p.1, p.2, g X (ξ (r * q.S + m)))) = _
          rw [hja]
          rfl
        rw [hans]
        show (if q.K ≤ r then _ else step q _ (some (j, a, g X (ξ (r * q.S + m))))) = _
        rw [ite_eq_right (by omega)]
        show (if m + 1 = q.S then _ else _) = _
        rw [ite_eq_right (by omega), Finset.sum_range_succ]
  obtain ⟨st, clk, cnt, hinv, hsum, hclk, heq⟩ := hmid (q.S - 1) (by omega)
  obtain ⟨j, a, hja, hsta, hat, -⟩ := hevent st cnt hinv (by omega)
  refine ⟨a, (hinv j).1.trans hsta, hat, ?_⟩
  intro X sel jv ξ
  have hSS : q.S = (q.S - 1) + 1 := by omega
  have hbe : batchEstimator q.S g X (fun i => ξ (r * q.S + i.val)) =
      ∑ l ∈ Finset.range (q.S - 1 + 1), (1 / (q.S : ℝ)) • g X (ξ (r * q.S + l)) := by
    show (1 / (q.S : ℝ)) • ∑ i : Fin q.S, g X (ξ (r * q.S + i.val)) = _
    rw [← Finset.smul_sum, ← hSS, Fin.sum_univ_eq_sum_range (fun l => g X (ξ (r * q.S + l))) q.S]
  rw [hbe]
  have h1 := hadv (fun k state => (rennala q).update state ((eventOracle q V P g).answer k ((rennala q).query state) (ξ k)))
    (q.S - 1) (r * q.S) (⟨r, 0, 0, X, fun _ => s, s, jv, sel⟩ : State q)
  rw [Nat.sub_add_cancel hS] at h1
  rw [h1, heq X sel jv ξ]
  have hq : (rennala q).query (⟨r, q.S - 1, ∑ l ∈ Finset.range (q.S - 1), (1 / (q.S : ℝ)) • g X (ξ (r * q.S + l)), X, st, clk, jv, sel⟩ : State q) =
      (0, some (X, st)) := by
    show (0, if q.K ≤ r then none else some (X, st)) = (0, some (X, st))
    rw [ite_eq_right (by omega)]
  rw [hq]
  have hans : (eventOracle q V P g).answer (r * q.S + (q.S - 1)) (0, some (X, st)) (ξ (r * q.S + (q.S - 1))) =
      some (j, a, g X (ξ (r * q.S + (q.S - 1)))) := by
    show eventAnswer q V g (some (X, st)) (ξ (r * q.S + (q.S - 1))) = _
    show Option.elim (earliest (fun i => completion (V i) (st i)) (List.finRange q.n)) none
      (fun p => some (p.1, p.2, g X (ξ (r * q.S + (q.S - 1))))) = _
    rw [hja]
    rfl
  rw [hans]
  show (if q.K ≤ r then _ else step q _ (some (j, a, g X (ξ (r * q.S + (q.S - 1)))))) = _
  rw [ite_eq_right (by omega)]
  show (if q.S - 1 + 1 = q.S then _ else _) = _
  rw [ite_eq_left (by omega), Finset.sum_range_succ]


theorem execute_uniform (q : Public) (V : Fin q.n → ℝ → ℝ)
    (hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0)) (hS : 0 < q.S)
    {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω)) (g : Point q.d → Ω → Point q.d)
    (hfin : deadline V q.S q.K < ⊤) :
    ∃ c : ℝ, ENNReal.ofReal c ≤ deadline V q.S q.K ∧
      ∀ (j : Fin (q.K + 1)) (ξ : ℕ → Ω),
        executeCounted (eventOracle q V P g) (rennala q) (q.K * q.S) j ξ =
          ((iterate g q.gamma q.S q.x0 ξ j.val, c), q.K * q.S) := by
  classical
  have hadd : ∀ {St : Type} (F : ℕ → St → St) (a b call : ℕ) (x : St),
      StochasticGradient.advance F (a + b) call x =
        StochasticGradient.advance F b (call + a) (StochasticGradient.advance F a call x) := by
    intro St F a
    induction a with
    | zero => intro b call x; rw [Nat.zero_add, Nat.add_zero]; rfl
    | succ a ih =>
      intro b call x
      rw [show a + 1 + b = (a + b) + 1 by omega]
      show StochasticGradient.advance F (a + b) (call + 1) (F call x) = _
      rw [ih, show call + 1 + a = call + (a + 1) by omega]
      rfl
  have htop : ∀ r m, deadline V q.S r = ⊤ → deadline V q.S (r + m) = ⊤ := by
    intro r m h
    induction m with
    | zero => exact h
    | succ m ih =>
      show (if deadline V q.S (r + m) = ⊤ then ⊤ else _) = ⊤
      rw [ite_eq_left ih]
  have hfinr : ∀ r, r ≤ q.K → deadline V q.S r ≠ ⊤ := by
    intro r hr h
    have := htop r (q.K - r) h
    rw [show r + (q.K - r) = q.K by omega] at this
    exact (ne_of_lt hfin) this
  have main : ∀ r, r ≤ q.K → ∃ c : ℝ, 0 ≤ c ∧ ENNReal.ofReal c ≤ deadline V q.S r ∧
      ∀ (j : Fin (q.K + 1)) (ξ : ℕ → Ω),
        StochasticGradient.advance (fun k state => (rennala q).update state
            ((eventOracle q V P g).answer k ((rennala q).query state) (ξ k))) (r * q.S) 0
          ((rennala q).initial j) =
        (⟨r, 0, 0, iterate g q.gamma q.S q.x0 ξ r, fun _ => c, c, j.val,
          if j.val ≤ r then iterate g q.gamma q.S q.x0 ξ j.val else q.x0⟩ : State q) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨0, le_rfl, by simp, fun j ξ => ?_⟩
      rw [Nat.zero_mul]
      show (⟨0, 0, 0, q.x0, fun _ => 0, 0, j.val, q.x0⟩ : State q) = _
      by_cases hj : j.val = 0
      · rw [ite_eq_left (by omega), hj]; rfl
      · rw [ite_eq_right (by omega)]; rfl
    | succ r ih =>
      intro hr
      obtain ⟨c, hc0, hcd, hadv⟩ := ih (by omega)
      have hdr := hfinr r (by omega)
      have hdr1 := hfinr (r + 1) hr
      set τ := (deadline V q.S r).toReal with hτ
      have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
      have hcτ : c ≤ τ := by
        rw [← ENNReal.ofReal_toReal hdr] at hcd
        exact (ENNReal.ofReal_le_ofReal_iff hτ0).mp hcd
      have hd1 : deadline V q.S (r + 1) = roundTime V q.S τ := by
        show (if deadline V q.S r = ⊤ then ⊤ else _) = _
        rw [ite_eq_right hdr]
      have hex : ∃ t, 0 ≤ t ∧ (q.S : ℝ) ≤ ∑ i, (⌊V i t - V i τ⌋ : ℝ) := by
        by_contra hne
        apply hdr1
        rw [hd1]
        show (if ∃ t, 0 ≤ t ∧ (q.S : ℝ) ≤ ∑ i, (⌊V i t - V i τ⌋ : ℝ) then _ else ⊤) = ⊤
        rw [ite_eq_right hne]
      obtain ⟨ht0, htc⟩ := min_attained V hV (fun i => V i τ) (q.S : ℝ) hex
      set tstar := sInf {t | 0 ≤ t ∧ (q.S : ℝ) ≤ ∑ i, (⌊V i t - V i τ⌋ : ℝ)} with htstar
      have hd1' : deadline V q.S (r + 1) = ENNReal.ofReal tstar := by
        rw [hd1]
        show (if ∃ t, 0 ≤ t ∧ (q.S : ℝ) ≤ ∑ i, (⌊V i t - V i τ⌋ : ℝ) then _ else ⊤) = _
        rw [ite_eq_left hex]
      have hcond : (q.S : ℝ) ≤ ∑ i, (⌊V i tstar - V i c⌋ : ℝ) := by
        refine htc.trans (Finset.sum_le_sum fun i _ => ?_)
        have : V i c ≤ V i τ := (hV i).2 (Set.mem_Ici.mpr hc0) (Set.mem_Ici.mpr hτ0) hcτ
        have h2 : V i tstar - V i τ ≤ V i tstar - V i c := by linarith
        exact_mod_cast Int.floor_mono h2
      obtain ⟨c', hcc', hc't, hround⟩ := round_step q V hV hS P g r (by omega) c hc0 tstar ht0 hcond
      refine ⟨c', hc0.trans hcc', ?_, fun j ξ => ?_⟩
      · rw [hd1']
        exact ENNReal.ofReal_le_ofReal hc't
      · rw [Nat.succ_mul, hadd, hadv j ξ, Nat.zero_add, hround]
        have hit : iterate g q.gamma q.S q.x0 ξ (r + 1) =
            iterate g q.gamma q.S q.x0 ξ r - q.gamma • batchEstimator q.S g
              (iterate g q.gamma q.S q.x0 ξ r) (fun i => ξ (r * q.S + i.val)) := rfl
        rw [← hit]
        by_cases hj : j.val = r + 1
        · rw [ite_eq_left hj, ite_eq_left (by omega), hj]
        · rw [ite_eq_right hj]
          by_cases hjr : j.val ≤ r
          · rw [ite_eq_left hjr, ite_eq_left (by omega)]
          · rw [ite_eq_right hjr, ite_eq_right (by omega)]
  obtain ⟨c, -, hcd, hadv⟩ := main q.K le_rfl
  refine ⟨c, hcd, fun j ξ => ?_⟩
  erw [executeCounted_advance, hadv j ξ]
  show ((if j.val ≤ q.K then iterate g q.gamma q.S q.x0 ξ j.val else q.x0, c), q.K * q.S) = _
  rw [ite_eq_left (by omega)]


end OracleTemplate.RennalaUniform
