import LongTails.Algorithms.ArrowHurwicz
import LongTails.Proofs.ArrowHurwiczStep
import LongTails.Proofs.Execution

open Set
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ArrowHurwicz

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

section Run

variable (adj : F → E) (K : E →L[ℝ] F) (px : E × ℝ → E) (py : F × ℝ → F) (η : ℝ)
  (x0 : E) (y0 : F)

noncomputable def stepAH (z : E × F) : E × F :=
  (px (z.1 - η • adj z.2, η), py (z.2 + η • K (px (z.1 - η • adj z.2, η)), η))

noncomputable def traj (t : ℕ) : E × F := (stepAH adj K px py η)^[t] (x0, y0)

lemma traj_succ (t : ℕ) :
    traj adj K px py η x0 y0 (t + 1) = stepAH adj K px py η (traj adj K px py η x0 y0 t) :=
  Function.iterate_succ_apply' _ _ _

lemma traj_fst_succ (t : ℕ) :
    (traj adj K px py η x0 y0 (t + 1)).1 =
      px ((traj adj K px py η x0 y0 t).1 - η • adj (traj adj K px py η x0 y0 t).2, η) := by
  rw [traj_succ]; rfl

lemma traj_snd_succ (t : ℕ) :
    (traj adj K px py η x0 y0 (t + 1)).2 =
      py ((traj adj K px py η x0 y0 t).2 + η • K (traj adj K px py η x0 y0 (t + 1)).1, η) := by
  rw [traj_succ]; rfl

noncomputable def stateAt : ℕ → AHState E F
  | 0 => ⟨0, x0, y0, 0, 0, 0, 0, 0⟩
  | t + 1 => ⟨0, (traj adj K px py η x0 y0 (t + 1)).1, (traj adj K px py η x0 y0 (t + 1)).2,
      adj (traj adj K px py η x0 y0 t).2, K (traj adj K px py η x0 y0 (t + 1)).1,
      (stateAt t).sx + (traj adj K px py η x0 y0 (t + 1)).1,
      (stateAt t).sy + (traj adj K px py η x0 y0 (t + 1)).2, t + 1⟩

lemma stateAt_x (t : ℕ) : (stateAt adj K px py η x0 y0 t).x = (traj adj K px py η x0 y0 t).1 := by
  cases t <;> rfl

lemma stateAt_y (t : ℕ) : (stateAt adj K px py η x0 y0 t).y = (traj adj K px py η x0 y0 t).2 := by
  cases t <;> rfl

lemma stateAt_phase (t : ℕ) : (stateAt adj K px py η x0 y0 t).phase = 0 := by
  cases t <;> rfl

lemma stateAt_n (t : ℕ) : (stateAt adj K px py η x0 y0 t).n = t := by
  cases t <;> rfl

lemma stateAt_sx (t : ℕ) :
    (stateAt adj K px py η x0 y0 t).sx = ∑ s ∈ Finset.range t, (traj adj K px py η x0 y0 (s + 1)).1 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Finset.sum_range_succ, ← ih]; rfl

lemma stateAt_sy (t : ℕ) :
    (stateAt adj K px py η x0 y0 t).sy = ∑ s ∈ Finset.range t, (traj adj K px py η x0 y0 (s + 1)).2 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Finset.sum_range_succ, ← ih]; rfl

def answerFn : (F ⊕ E) ⊕ ((E × ℝ) ⊕ (F × ℝ)) → E ⊕ F :=
  Sum.elim (Sum.elim (fun y => Sum.inl (adj y)) (fun x => Sum.inr (K x)))
    (Sum.elim (fun q => Sum.inl (px q)) (fun q => Sum.inr (py q)))

lemma four_steps (t : ℕ) :
    (fun st => (arrowHurwicz η x0 y0).update st
      (answerFn adj K px py (((arrowHurwicz η x0 y0).query st).2)))^[4]
      (stateAt adj K px py η x0 y0 t) = stateAt adj K px py η x0 y0 (t + 1) := by
  have hx := stateAt_x adj K px py η x0 y0 t
  have hy := stateAt_y adj K px py η x0 y0 t
  have hp := stateAt_phase adj K px py η x0 y0 t
  have hn := stateAt_n adj K px py η x0 y0 t
  have h1 := traj_fst_succ adj K px py η x0 y0 t
  have h2 := traj_snd_succ adj K px py η x0 y0 t
  generalize hs : stateAt adj K px py η x0 y0 t = st at hx hy hp hn
  obtain ⟨ph, x, y, v, w, sx, sy, n⟩ := st
  simp only at hx hy hp hn
  subst hp hn hx hy
  have d10 : (1 : ℕ) ≠ 0 := by decide
  have d20 : (2 : ℕ) ≠ 0 := by decide
  have d21 : (2 : ℕ) ≠ 1 := by decide
  have d30 : (3 : ℕ) ≠ 0 := by decide
  have d31 : (3 : ℕ) ≠ 1 := by decide
  have d32 : (3 : ℕ) ≠ 2 := by decide
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    arrowHurwicz, answerFn, Sum.elim_inl, Sum.elim_inr, ↓reduceIte, d10, d20, d21, d30, d31, d32]
  simp only [stateAt, hs, ← h1, h2]

lemma run_state (t : ℕ) :
    (fun st => (arrowHurwicz η x0 y0).update st
      (answerFn adj K px py (((arrowHurwicz η x0 y0).query st).2)))^[4 * t]
      ((arrowHurwicz η x0 y0).initial ()) = stateAt adj K px py η x0 y0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show 4 * (t + 1) = 4 + 4 * t by ring, Function.iterate_add_apply, ih]
    exact four_steps adj K px py η x0 y0 t

lemma execute_ah (t : ℕ) :
    execute { answer := fun _ (_, query) _ => answerFn adj K px py query } (arrowHurwicz η x0 y0)
      (fun _ => (4 * t)) = (arrowHurwicz η x0 y0).output (stateAt adj K px py η x0 y0 t) := by
  erw [execute_iterate (answerFn adj K px py) (arrowHurwicz η x0 y0) (4 * t) (), run_state]

lemma output_eq (t : ℕ) (ht : 0 < t) :
    (arrowHurwicz η x0 y0).output (stateAt adj K px py η x0 y0 t) =
      (((t : ℝ))⁻¹ • ∑ s ∈ Finset.range t, (traj adj K px py η x0 y0 (s + 1)).1,
        ((t : ℝ))⁻¹ • ∑ s ∈ Finset.range t, (traj adj K px py η x0 y0 (s + 1)).2) := by
  have hn := stateAt_n adj K px py η x0 y0 t
  have ht0 : t ≠ 0 := by omega
  simp only [arrowHurwicz, hn, ht0, ↓reduceIte, stateAt_sx, stateAt_sy]

end Run

end OracleTemplate.ArrowHurwicz
