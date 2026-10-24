import LongTails.Algorithms.CyclicFullWidthPerceptron
import LongTails.Proofs.Execution
import Mathlib.Logic.Equiv.Fin.Rotate

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronExecution

open LongTails.Setups.CyclicFullWidthPerceptron
open LongTails.Algorithms.CyclicFullWidthPerceptron

noncomputable def advance (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) : State p.dimension p.count :=
  update (stepSize p) s (answer p D (s.cursor, s.point))

lemma advance_cursor (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) :
    (advance p D s).cursor = finRotate (p.count + 1) s.cursor := rfl

lemma advance_correct (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (h : 0 < margin (sample p D s.cursor) s.point) :
    (advance p D s).point = s.point := by
  simp [advance, update, answer, not_le.mpr h]

lemma advance_mistake (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (h : margin (sample p D s.cursor) s.point ≤ 0) :
    (advance p D s).point = move s.point (stepSize p)
      (direction (sample p D s.cursor) s.point) := by
  simp [advance, update, answer, h]

lemma separating_absorbed (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (h : Separates p D s.point) (k : ℕ) :
    ((advance p D)^[k] s).point = s.point := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [advance_correct p D _ (by rw [ih]; exact h _), ih]

lemma iterate_cursor (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (k : ℕ) :
    ((advance p D)^[k] s).cursor = (finRotate (p.count + 1))^[k] s.cursor := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Function.iterate_succ_apply', advance_cursor, ih]

lemma visits_all (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (i : Fin (p.count + 1)) :
    ∃ k < p.count + 1, ((advance p D)^[k] s).cursor = i := by
  let k : Fin (p.count + 1) := i - s.cursor
  refine ⟨k.val, k.isLt, ?_⟩
  rw [iterate_cursor, ← finCycle_eq_finRotate_iterate]
  simp [finCycle_apply, k]

lemma no_mistakes_point (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (k : ℕ)
    (h : ∀ j < k, 0 < margin (sample p D ((advance p D)^[j] s).cursor)
      ((advance p D)^[j] s).point) :
    ((advance p D)^[k] s).point = s.point := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', advance_correct p D _ (h k (by omega))]
      exact ih (fun j hj => h j (by omega))

lemma cycle_without_mistakes_separates (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count)
    (h : ∀ j < p.count + 1, 0 < margin (sample p D ((advance p D)^[j] s).cursor)
      ((advance p D)^[j] s).point) : Separates p D s.point := by
  intro i
  obtain ⟨k, hk, hi⟩ := visits_all p D s i
  have hc := h k hk
  rw [hi, no_mistakes_point p D s k (fun j hj => h j (by omega))] at hc
  exact hc

lemma nonseparating_cycle_mistake (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (h : ¬ Separates p D s.point) :
    ∃ j < p.count + 1, margin (sample p D ((advance p D)^[j] s).cursor)
      ((advance p D)^[j] s).point ≤ 0 := by
  by_contra hn
  push Not at hn
  exact h (cycle_without_mistakes_separates p D s hn)

noncomputable def mistakes (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if margin (sample p D s.cursor) s.point ≤ 0 then 1 else 0) +
      mistakes p D (advance p D s) k

lemma mistakes_add (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (a b : ℕ) :
    mistakes p D s (a + b) = mistakes p D s a +
      mistakes p D ((advance p D)^[a] s) b := by
  induction a generalizing s with
  | zero => simp [mistakes]
  | succ a ih =>
      rw [Nat.succ_add, mistakes, mistakes, ih]
      simp only [Function.iterate_succ_apply, Nat.add_assoc]

lemma zero_mistakes_correct (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (k : ℕ) (h : mistakes p D s k = 0) :
    ∀ j < k, 0 < margin (sample p D ((advance p D)^[j] s).cursor)
      ((advance p D)^[j] s).point := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
      simp only [mistakes, Nat.add_eq_zero_iff] at h
      have hc : 0 < margin (sample p D s.cursor) s.point := by
        split at h <;> simp_all
      intro j hj
      cases j with
      | zero => simpa using hc
      | succ j =>
          simpa only [Function.iterate_succ_apply] using ih (advance p D s) h.2 j (by omega)

lemma cycle_mistakes_positive (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (h : ¬ Separates p D s.point) :
    1 ≤ mistakes p D s (p.count + 1) := by
  by_contra hn
  have hz : mistakes p D s (p.count + 1) = 0 := by omega
  exact h (cycle_without_mistakes_separates p D s
    (zero_mistakes_correct p D s _ hz))

lemma cycles_count (p : Params) (D : Data p.dimension p.count)
    (s : State p.dimension p.count) (L : ℕ)
    (h : ¬ Separates p D (((advance p D)^[(p.count + 1) * L]) s).point) :
    L ≤ mistakes p D s ((p.count + 1) * L) := by
  induction L generalizing s with
  | zero => omega
  | succ L ih =>
      have hs : ¬ Separates p D s.point := by
        intro hs
        rw [separating_absorbed p D s hs] at h
        exact h hs
      have hc := cycle_mistakes_positive p D s hs
      rw [show (p.count + 1) * (L + 1) = (p.count + 1) + (p.count + 1) * L by ring,
        mistakes_add]
      have htail : ¬ Separates p D
          (((advance p D)^[(p.count + 1) * L]) (((advance p D)^[p.count + 1]) s)).point := by
        simpa only [Nat.mul_succ, Function.iterate_add_apply] using h
      have hi := ih (((advance p D)^[p.count + 1]) s) htail
      omega

lemma output_eq_iterate (p : Params) (D : Data p.dimension p.count)
    (oracle : Oracle (Fin (p.count + 1) × Space p.dimension) (Reply p.dimension))
    (hanswer : ∀ history query seed, oracle.answer history query seed = answer p D query.2)
    (K : ℕ) (seed : (k : ℕ) → oracle.Seed k) :
    output p oracle K seed =
      ((advance p D)^[K] (⟨initial p.dimension, 0⟩ : State p.dimension p.count)).point := by
  unfold output
  erw [execute_eq_of_answer_eq oracle (answer p D) (fun h q ξ => hanswer h (0, q) ξ),
    execute_iterate]
  rfl

def CheckedPrefix {d n : ℕ} (D : Data d n) (δ : ℝ) (U : Features d)
    (cursor : Fin (n + 1)) : Prop :=
  ∀ i, cursor.val = 0 ∨ i.val + 1 < cursor.val → -δ ≤ ⟪U, D.residual i⟫

lemma prefix_all {d n : ℕ} (D : Data d n) (δ : ℝ) (U : Features d)
    (h : CheckedPrefix D δ U 0) : ∀ i, -δ ≤ ⟪U, D.residual i⟫ :=
  fun i => h i (Or.inl rfl)

lemma prefix_after_reference {d n : ℕ} (D : Data d n) (δ : ℝ) (U : Features d)
    (hn : 0 < n) : CheckedPrefix D δ U (finRotate (n + 1) 0) := by
  intro i hi
  have hv : (finRotate (n + 1) 0).val = 1 := by
    rw [coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last]
    split <;> omega
  rcases hi with hi | hi <;> rw [hv] at hi <;> omega

lemma prefix_after_negative {d n : ℕ} (D : Data d n) (δ : ℝ) (U : Features d)
    (i : Fin n) (h : CheckedPrefix D δ U i.succ)
    (hi : -δ ≤ ⟪U, D.residual i⟫) :
    CheckedPrefix D δ U (finRotate (n + 1) i.succ) := by
  intro j hj
  have hji : j.val ≤ i.val := by
    by_cases hiLast : i.val + 1 = n
    · omega
    · have hv : (finRotate (n + 1) i.succ).val = i.val + 2 := by
        rw [coe_finRotate]
        simp only [Fin.ext_iff, Fin.val_succ, Fin.val_last, hiLast, ↓reduceIte]
      rcases hj with hj | hj <;> rw [hv] at hj <;> omega
  by_cases he : j = i
  · simpa [he] using hi
  · apply h j (Or.inr ?_)
    have hne : j.val ≠ i.val := fun hh => he (Fin.ext hh)
    simp only [Fin.val_succ]
    omega

end LongTails.Proofs.CyclicPerceptronExecution
