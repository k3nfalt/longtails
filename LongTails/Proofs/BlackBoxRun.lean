import LongTails.Algorithms.BlackBoxDiagonalAccelerated

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

variable {d : ℕ}

lemma xv_congr (m : Fin d → ℝ) (α μ : ℝ) (base : Vec d) {H H' : ℕ → ℝ × Vec d} :
    ∀ k, (∀ i, i < k → (H (2 * i)).2 = (H' (2 * i)).2) →
      xv m α μ base H k = xv m α μ base H' k
  | 0, _ => rfl
  | k + 1, h => by
      have ih := xv_congr m α μ base k (fun i hi => h i (by omega))
      simp only [xv, ih, h k (by omega)]

lemma phaseQuery_congr (m : Fin d → ℝ) (α μ : ℝ) {N : ℕ} (hN : 1 ≤ N) (base : Vec d)
    {H H' : ℕ → ℝ × Vec d} (s : ℕ) (h : ∀ i, i < s → H i = H' i) :
    phaseQuery m α μ N base H s = phaseQuery m α μ N base H' s := by
  unfold phaseQuery
  by_cases hs : s = 2 * N
  · subst hs
    simp only [↓reduceIte, zAt]
    rw [xv_congr m α μ base N (fun i hi => by rw [h (2 * i) (by omega)]),
      h (2 * N - 1) (by omega)]
  · simp only [hs, ↓reduceIte]
    by_cases he : s % 2 = 0
    · simp only [he, ↓reduceIte, yAt]
      rw [xv_congr m α μ base (s / 2) (fun i hi => by rw [h (2 * i) (by omega)])]
    · simp only [he, ↓reduceIte]
      rw [xv_congr m α μ base (s / 2 + 1) (fun i hi => by rw [h (2 * i) (by omega)])]

section Simulation

variable (f : Vec d → ℝ) (x0 : Vec d)

noncomputable def orc (q : Vec d) : ℝ × Vec d := (f q, gradient f q)

noncomputable def stepOf (st : St d) : St d := updateOf st (orc f (queryOf x0 st))

noncomputable def Hrep (st : St d) : ℕ → ℕ → ℝ × Vec d
  | 0 => st.H
  | t + 1 => Function.update (Hrep st t) t
      (orc f (phaseQuery st.m (alph st.lvl) (muh st.lvl) st.N st.base (Hrep st t) t))

lemma Hrep_stable (st : St d) {i t : ℕ} (h : i < t) : ∀ u, t ≤ u → Hrep f st u i = Hrep f st t i
  | 0, hu => by omega
  | u + 1, hu => by
      rcases Nat.lt_or_ge t (u + 1) with h' | h'
      · simp only [Hrep]
        rw [Function.update_of_ne (by omega)]
        exact Hrep_stable st h u (by omega)
      · have : t = u + 1 := by omega
        subst this; rfl

lemma phase_iterate (st : St d) (hp : st.probing = false) (h0 : st.s = 0) :
    ∀ t, t ≤ 2 * st.N →
      (stepOf f x0)^[t] st = { st with s := t, H := Hrep f st t }
  | 0, _ => by cases st; simp_all [Hrep]
  | t + 1, ht => by
      rw [Function.iterate_succ_apply', phase_iterate st hp h0 t (by omega)]
      unfold stepOf updateOf queryOf
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hne : t ≠ 2 * st.N := by omega
      simp only [St.N, St.m] at hne ⊢
      simp only [hne, ↓reduceIte, Hrep]
      rfl

lemma updateOf_end (st : St d) (hp : st.probing = false) (hs : st.s = 2 * st.N)
    (r : ℝ × Vec d) : updateOf st r = endPhase st (Function.update st.H st.s r) := by
  unfold updateOf
  simp only [hp, Bool.false_eq_true, ↓reduceIte, hs]

lemma queryOf_phase (st : St d) (hp : st.probing = false) :
    queryOf x0 st = phaseQuery st.m (alph st.lvl) (muh st.lvl) st.N st.base st.H st.s := by
  unfold queryOf
  simp only [hp, Bool.false_eq_true, ↓reduceIte]

lemma endPhase_congr (st : St d) (a : ℕ) (b H : ℕ → ℝ × Vec d) :
    endPhase { st with s := a, H := b } H = endPhase st H := by
  cases st; rfl

lemma phase_end (st : St d) (hp : st.probing = false) (h0 : st.s = 0) :
    (stepOf f x0)^[2 * st.N + 1] st = endPhase st (Hrep f st (2 * st.N + 1)) := by
  rw [Function.iterate_succ_apply', phase_iterate f x0 st hp h0 (2 * st.N) le_rfl]
  unfold stepOf
  rw [updateOf_end { st with s := 2 * st.N, H := Hrep f st (2 * st.N) } hp rfl,
    queryOf_phase x0 { st with s := 2 * st.N, H := Hrep f st (2 * st.N) } hp, endPhase_congr]
  rfl

def Cons (f : Vec d → ℝ) (m : Fin d → ℝ) (α μ : ℝ) (N : ℕ) (base : Vec d)
    (H : ℕ → ℝ × Vec d) : Prop :=
  ∀ i, i ≤ 2 * N → H i = orc f (phaseQuery m α μ N base H i)

lemma Hrep_cons (st : St d) (hN : 1 ≤ st.N) :
    Cons f st.m (alph st.lvl) (muh st.lvl) st.N st.base (Hrep f st (2 * st.N + 1)) := by
  intro i hi
  rw [Hrep_stable f st (show i < i + 1 by omega) (2 * st.N + 1) (by omega)]
  simp only [Hrep, Function.update_self]
  congr 1
  apply phaseQuery_congr _ _ _ hN
  intro j hj
  exact (Hrep_stable f st hj (2 * st.N + 1) (by omega)).symm

end Simulation

end OracleTemplate.BlackBoxDiagonal
