import LongTails.Proofs.Execution
import LongTails.Proofs.SlidingInner

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GeneralizedSliding

open LongTails.Setups.SlidingGeneralizedSmooth

open CompositeGeneralized (mixPoint)

variable (p : Public) (r : ℕ → Query p → p.E)

noncomputable def trans (sc : SlideState p.E × ℕ) : SlideState p.E × ℕ :=
  ((sliding p).update sc.1 (r sc.2 ((sliding p).query sc.1)), sc.2 + 1)

def Idle (s : SlideState p.E) : Prop := p.R ^ 2 / p.ε ≤ s.A ∨ outerCap p ≤ s.k

variable {p} {r}

lemma trans_snd (n : ℕ) (sc : SlideState p.E × ℕ) : ((trans p r)^[n] sc).2 = sc.2 + n := by
  induction n generalizing sc with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [trans]
    ring

lemma trans_idle {s : SlideState p.E} (h0 : s.stage = 0) (hI : Idle p s) (k n : ℕ) :
    (trans p r)^[n] (s, k) = (s, k + n) := by
  have hI' : p.R ^ 2 / p.ε ≤ s.A ∨ outerCap p ≤ s.k := hI
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have e : trans p r (s, k) = (s, k + 1) := by
      simp only [trans, sliding, h0, ite_true, hI']
    rw [e, ih]
    ring_nf

lemma pair_start {s : SlideState p.E} (h0 : s.stage = 0) (hI : ¬ Idle p s) (c : ℕ) :
    (trans p r)^[2] (s, c) =
      ({ s with
          stage := 2
          a := slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖r c (Query.gradient s.x)‖)
          g := r (c + 1) (Query.gradient (mixPoint s.A
            (slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖r c (Query.gradient s.x)‖)) s.x s.z))
          T := innerLength p.M p.ε
            (slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖r c (Query.gradient s.x)‖))
          t := 0
          u := s.z
          ub := s.z }, c + 2) := by
  have hI' : ¬ (p.R ^ 2 / p.ε ≤ s.A ∨ outerCap p ≤ s.k) := hI
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, trans]
  simp [sliding, h0, hI']

lemma pair_cont {st : SlideState p.E} (h2 : st.stage = 2) (hne : st.t + 1 ≠ st.T) (c : ℕ) :
    (trans p r)^[2] (st, c) =
      ({ st with
          stage := 2
          t := st.t + 1
          w := innerTarget (wsum st.T / (st.a * (wsum st.T + 1))) (((st.t : ℝ) + 1) / 2) st.z
            st.u (st.g + r c (Query.subgradient st.u))
          u := r (c + 1) (Query.project (innerTarget (wsum st.T / (st.a * (wsum st.T + 1)))
            (((st.t : ℝ) + 1) / 2) st.z st.u (st.g + r c (Query.subgradient st.u))))
          ub := (wsum st.t / wsum (st.t + 1)) • st.ub + (((st.t : ℝ) + 2) / wsum (st.t + 1)) •
            r (c + 1) (Query.project (innerTarget (wsum st.T / (st.a * (wsum st.T + 1)))
              (((st.t : ℝ) + 1) / 2) st.z st.u (st.g + r c (Query.subgradient st.u)))) },
        c + 2) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, trans]
  simp [sliding, h2, hne]

lemma pair_fin {st : SlideState p.E} (h2 : st.stage = 2) (heq : st.t + 1 = st.T) (c : ℕ) :
    (trans p r)^[2] (st, c) =
      ({ st with
          stage := 0
          k := st.k + 1
          A := st.A + st.a
          w := innerTarget (wsum st.T / (st.a * (wsum st.T + 1))) (((st.t : ℝ) + 1) / 2) st.z
            st.u (st.g + r c (Query.subgradient st.u))
          x := mixPoint st.A st.a st.x ((wsum st.t / wsum (st.t + 1)) • st.ub +
            (((st.t : ℝ) + 2) / wsum (st.t + 1)) •
              r (c + 1) (Query.project (innerTarget (wsum st.T / (st.a * (wsum st.T + 1)))
                (((st.t : ℝ) + 1) / 2) st.z st.u (st.g + r c (Query.subgradient st.u)))))
          z := r (c + 1) (Query.project (innerTarget (wsum st.T / (st.a * (wsum st.T + 1)))
            (((st.t : ℝ) + 1) / 2) st.z st.u (st.g + r c (Query.subgradient st.u)))) },
        c + 2) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, trans]
  simp [sliding, h2, heq]

variable (p) (r)

noncomputable def weightAt (s : SlideState p.E) (k : ℕ) : ℝ :=
  slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖r k (Query.gradient s.x)‖)

noncomputable def gradY (s : SlideState p.E) (k : ℕ) : p.E :=
  r (k + 1) (Query.gradient (mixPoint s.A (weightAt p r s k) s.x s.z))

noncomputable def lenAt (s : SlideState p.E) (k : ℕ) : ℕ :=
  innerLength p.M p.ε (weightAt p r s k)

noncomputable def betaAt (s : SlideState p.E) (k : ℕ) : ℝ :=
  wsum (lenAt p r s k) / (weightAt p r s k * (wsum (lenAt p r s k) + 1))

noncomputable def subAt (k t : ℕ) (u : p.E) : p.E := r (k + 2 + 2 * t) (Query.subgradient u)

noncomputable def projAt (k t : ℕ) (w : p.E) : p.E := r (k + 2 + 2 * t + 1) (Query.project w)

noncomputable def innerAt (s : SlideState p.E) (k t : ℕ) : p.E × p.E :=
  innerSeq (projAt p r k) (subAt p r k) (betaAt p r s k) (gradY p r s k) s.z t

def InnerAt (s : SlideState p.E) (k j : ℕ) (st : SlideState p.E) : Prop :=
  st.stage = 2 ∧ st.k = s.k ∧ st.A = s.A ∧ st.x = s.x ∧ st.z = s.z ∧
    st.a = weightAt p r s k ∧ st.g = gradY p r s k ∧ st.T = lenAt p r s k ∧ st.t = j ∧
    st.u = (innerAt p r s k j).1 ∧ st.ub = (innerAt p r s k j).2

def OuterNext (s : SlideState p.E) (k : ℕ) (s' : SlideState p.E) : Prop :=
  s'.stage = 0 ∧ s'.k = s.k + 1 ∧ s'.A = s.A + weightAt p r s k ∧
    s'.x = mixPoint s.A (weightAt p r s k) s.x (innerAt p r s k (lenAt p r s k)).2 ∧
    s'.z = (innerAt p r s k (lenAt p r s k)).1

variable {p} {r}

lemma inner_start {s : SlideState p.E} (h0 : s.stage = 0) (hI : ¬ Idle p s) (k : ℕ) :
    ∃ st, (trans p r)^[2] (s, k) = (st, k + 2) ∧ InnerAt p r s k 0 st :=
  ⟨_, pair_start h0 hI k, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma inner_advance {s : SlideState p.E} {k j : ℕ} {st : SlideState p.E}
    (hst : InnerAt p r s k j st) (hj : j + 1 ≠ lenAt p r s k) :
    ∃ st', (trans p r)^[2] (st, k + 2 + 2 * j) = (st', k + 2 + 2 * (j + 1)) ∧
      InnerAt p r s k (j + 1) st' := by
  obtain ⟨h2, hk, hA, hx, hz, ha, hg, hT, ht, hu, hub⟩ := hst
  have hne : st.t + 1 ≠ st.T := by rw [ht, hT]; exact hj
  refine ⟨_, (pair_cont h2 hne _).trans
    (Prod.ext rfl (show k + 2 + 2 * j + 2 = k + 2 + 2 * (j + 1) by ring)),
    rfl, hk, hA, hx, hz, ha, hg, hT, by simp only [ht], ?_, ?_⟩
  · simp only
    rw [hu, hz, hg, ht, hT, ha]
    rfl
  · simp only
    rw [hu, hub, hz, hg, ht, hT, ha]
    rfl

lemma inner_reach {s : SlideState p.E} (h0 : s.stage = 0) (hI : ¬ Idle p s) (k : ℕ) :
    ∀ j, j < lenAt p r s k →
      ∃ st, (trans p r)^[2 + 2 * j] (s, k) = (st, k + 2 + 2 * j) ∧ InnerAt p r s k j st := by
  intro j
  induction j with
  | zero =>
    intro _
    simpa using inner_start (r := r) h0 hI k
  | succ j ih =>
    intro hj
    obtain ⟨st, hst, hin⟩ := ih (by omega)
    obtain ⟨st', hst', hin'⟩ := inner_advance hin (by omega)
    refine ⟨st', ?_, hin'⟩
    rw [show 2 + 2 * (j + 1) = 2 + (2 + 2 * j) by ring, Function.iterate_add_apply, hst, hst']

lemma lenAt_pos (s : SlideState p.E) (k : ℕ) : 2 ≤ lenAt p r s k := by
  simp only [lenAt, innerLength]; omega

lemma outer_macro {s : SlideState p.E} (h0 : s.stage = 0) (hI : ¬ Idle p s) (k : ℕ) :
    ∃ s', (trans p r)^[2 + 2 * lenAt p r s k] (s, k) = (s', k + 2 + 2 * lenAt p r s k) ∧
      OuterNext p r s k s' := by
  obtain ⟨j, hj⟩ : ∃ j, lenAt p r s k = j + 1 := ⟨lenAt p r s k - 1, by
    have := lenAt_pos (r := r) s k; omega⟩
  obtain ⟨st, hst, hin⟩ := inner_reach (r := r) h0 hI k j (by omega)
  obtain ⟨h2, hk, hA, hx, hz, ha, hg, hT, ht, hu, hub⟩ := hin
  have heq : st.t + 1 = st.T := by rw [ht, hT, hj]
  have e := pair_fin (r := r) h2 heq (k + 2 + 2 * j)
  refine ⟨((trans p r)^[2] (st, k + 2 + 2 * j)).1, ?_, ?_⟩
  · rw [hj, show 2 + 2 * (j + 1) = 2 + (2 + 2 * j) by ring, Function.iterate_add_apply, hst, e]
    exact Prod.ext rfl (show k + 2 + 2 * j + 2 = k + 2 + 2 * (j + 1) by ring)
  · rw [e]
    refine ⟨rfl, by simp only [hk], by simp only [hA, ha], ?_, ?_⟩
    · simp only
      rw [hj, hu, hub, hz, hg, ht, hT, ha, hA, hx]
      rfl
    · simp only
      rw [hj, hu, hz, hg, ht, hT, ha]
      rfl

def gscore (s : SlideState p.E) : ℕ :=
  2 * s.k + (if s.stage = 0 then 0 else if s.stage = 1 then 1 else 2)

def Reach (s : SlideState p.E) : Prop :=
  (s.stage = 0 → s.k ≤ outerCap p) ∧ (s.stage ≠ 0 → s.k < outerCap p)

lemma step_score (c : ℕ) (s : SlideState p.E) (hreach : Reach s) :
    (if ((sliding p).query s).1 = 0 then 1 else 0) + gscore s ≤
        gscore ((sliding p).update s (r c ((sliding p).query s))) ∧
      Reach ((sliding p).update s (r c ((sliding p).query s))) := by
  obtain ⟨hr0, hr1⟩ := hreach
  by_cases h0 : s.stage = 0
  · have hk0 := hr0 h0
    by_cases hI : p.R ^ 2 / p.ε ≤ s.A ∨ outerCap p ≤ s.k
    · simp [sliding, h0, hI, gscore, Reach, hk0]
    · have hk : s.k < outerCap p := by push Not at hI; exact hI.2
      simp [sliding, h0, hI, gscore, Reach, hk]; omega
  · have hk := hr1 h0
    by_cases h1 : s.stage = 1
    · simp [sliding, h1, gscore, Reach, hk]; omega
    · by_cases h2 : s.stage = 2
      · simp [sliding, h2, gscore, Reach, hk]
      · by_cases heq : s.t + 1 = s.T
        · simp [sliding, h0, h1, h2, heq, gscore, Reach]
          omega
        · simp [sliding, h0, h1, h2, heq, gscore, Reach, hk]

noncomputable def calls (p : Public) (r : ℕ → Query p → p.E) (n : ℕ) (i : Fin 3) : ℕ :=
  ∑ k ∈ Finset.range n,
    if ((sliding p).query ((trans p r)^[k] ((sliding p).initial (), 0)).1).1 = i then 1 else 0

lemma calls_succ (n : ℕ) (i : Fin 3) :
    calls p r (n + 1) i = calls p r n i +
      if ((sliding p).query ((trans p r)^[n] ((sliding p).initial (), 0)).1).1 = i then 1 else 0 := by
  simp only [calls, Finset.sum_range_succ]

lemma calls_le (n : ℕ) (i : Fin 3) : calls p r n i ≤ n := by
  induction n with
  | zero => simp [calls]
  | succ n ih => rw [calls_succ]; split_ifs <;> omega

lemma gradient_count (n : ℕ) : calls p r n 0 ≤ 2 * outerCap p := by
  have h : ∀ n, Reach ((trans p r)^[n] ((sliding p).initial (), 0)).1 ∧
      calls p r n 0 ≤ gscore ((trans p r)^[n] ((sliding p).initial (), 0)).1 := by
    intro n
    induction n with
    | zero => simp [Reach, calls, gscore, sliding]
    | succ n ih =>
      obtain ⟨hs, hr⟩ := step_score (r := r)
        (((trans p r)^[n] ((sliding p).initial (), 0)).2) _ ih.1
      rw [Function.iterate_succ_apply', calls_succ]
      exact ⟨hr, by dsimp only [trans]; omega⟩
  obtain ⟨hr0, hr1⟩ := (h n).1
  apply (h n).2.trans
  unfold gscore
  by_cases h0 : ((trans p r)^[n] ((sliding p).initial (), 0)).1.stage = 0
  · simp [h0]; have := hr0 h0; omega
  · have := hr1 h0
    split_ifs <;> omega

lemma remaining_succ (B : Fin 3 → ℕ) (n : ℕ) :
    (fun i => B i - calls p r (n + 1) i) =
      Function.update (fun i => B i - calls p r n i)
        ((sliding p).query ((trans p r)^[n] ((sliding p).initial (), 0)).1).1
        (B ((sliding p).query ((trans p r)^[n] ((sliding p).initial (), 0)).1).1 -
          calls p r n ((sliding p).query ((trans p r)^[n] ((sliding p).initial (), 0)).1).1 - 1) := by
  funext i
  by_cases hi : i = ((sliding p).query ((trans p r)^[n] ((sliding p).initial (), 0)).1).1
  · subst i
    simp [calls_succ, Nat.sub_sub]
  · simp [calls_succ, Function.update_of_ne hi, Ne.symm hi]

end OracleTemplate.GeneralizedSliding
