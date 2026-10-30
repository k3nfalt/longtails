import LongTails.Algorithms.AuxiliaryPlan
import LongTails.Proofs.Execution

namespace LongTails.Proofs.AuxiliaryPlan

open OracleTemplate LongTails.Algorithms.AuxiliaryPlan

namespace TwoPlan

open LongTails.Algorithms.AuxiliaryPlan.TwoPlan

variable {Q R α β : Type}

@[simp] lemma eval_done (g : Fin 2 → Q → R) (a : α) : eval g (done a : TwoPlan Q R α) = a := rfl

@[simp] lemma eval_ask (g : Fin 2 → Q → R) (i : Fin 2) (q : Q) (next : R → TwoPlan Q R α) :
    eval g (ask i q next) = eval g (next (g i q)) := rfl

@[simp] lemma calls_done (g : Fin 2 → Q → R) (j : Fin 2) (a : α) :
    calls g j (done a : TwoPlan Q R α) = 0 := rfl

lemma eval_bind (g : Fin 2 → Q → R) (p : TwoPlan Q R α) (k : α → TwoPlan Q R β) :
    eval g (andThen p k) = eval g (k (eval g p)) := by
  induction p with
  | done a => rfl
  | ask i q next ih => exact ih (g i q)

lemma calls_bind (g : Fin 2 → Q → R) (j : Fin 2) (p : TwoPlan Q R α) (k : α → TwoPlan Q R β) :
    calls g j (andThen p k) = calls g j p + calls g j (k (eval g p)) := by
  induction p with
  | done a => simp [andThen, calls, eval]
  | ask i q next ih =>
      simp only [andThen, calls, eval]
      rw [ih (g i q)]
      ring

@[simp] lemma eval_bind' (g : Fin 2 → Q → R) (p : TwoPlan Q R α) (k : α → TwoPlan Q R β) :
    eval g (p >>= k) = eval g (k (eval g p)) :=
  eval_bind g p k

@[simp] lemma eval_pure (g : Fin 2 → Q → R) (a : α) : eval g (pure a : TwoPlan Q R α) = a := rfl

lemma calls_bind' (g : Fin 2 → Q → R) (j : Fin 2) (p : TwoPlan Q R α) (k : α → TwoPlan Q R β) :
    calls g j (p >>= k) = calls g j p + calls g j (k (eval g p)) :=
  calls_bind g j p k

@[simp] lemma calls_pure (g : Fin 2 → Q → R) (j : Fin 2) (a : α) :
    calls g j (pure a : TwoPlan Q R α) = 0 := rfl

@[simp] lemma eval_call (g : Fin 2 → Q → R) (i : Fin 2) (q : Q) :
    eval g (call i q : TwoPlan Q R R) = g i q := rfl

lemma calls_call (g : Fin 2 → Q → R) (i j : Fin 2) (q : Q) :
    calls g j (call i q : TwoPlan Q R R) = if i = j then 1 else 0 := by
  simp [call, calls]

lemma eval_loop (g : Fin 2 → Q → R) (body : β → TwoPlan Q R β) (n : ℕ) (s : β) :
    eval g (loop n body s) = (fun t => eval g (body t))^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [loop, eval_bind, ih, Function.iterate_succ_apply]

lemma calls_loop_le (g : Fin 2 → Q → R) (j : Fin 2) (body : β → TwoPlan Q R β) (c : ℕ)
    (hc : ∀ s, calls g j (body s) ≤ c) (n : ℕ) (s : β) :
    calls g j (loop n body s) ≤ n * c := by
  induction n generalizing s with
  | zero => simp [loop]
  | succ n ih =>
      simp only [loop, calls_bind]
      have h1 := hc s
      have h2 := ih (eval g (body s))
      nlinarith

def length (g : Fin 2 → Q → R) : TwoPlan Q R α → ℕ
  | done _ => 0
  | ask i q next => 1 + length g (next (g i q))

lemma length_eq (g : Fin 2 → Q → R) (p : TwoPlan Q R α) :
    length g p = calls g 0 p + calls g 1 p := by
  induction p with
  | done a => rfl
  | ask i q next ih =>
      simp only [length, calls, ih (g i q)]
      fin_cases i <;> simp <;> ring

lemma eval_step (g : Fin 2 → Q → R) (p : TwoPlan Q R α) : eval g (step g p) = eval g p := by
  cases p <;> rfl

lemma iterate_step_done (g : Fin 2 → Q → R) (a : α) (k : ℕ) :
    (step g)^[k] (done a : TwoPlan Q R α) = done a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih

lemma iterate_step_of_length_le (g : Fin 2 → Q → R) (p : TwoPlan Q R α) (k : ℕ)
    (hk : length g p ≤ k) : (step g)^[k] p = done (eval g p) := by
  induction p generalizing k with
  | done a => exact iterate_step_done g a k
  | ask i q next ih =>
      cases k with
      | zero => simp [length] at hk
      | succ k =>
          rw [Function.iterate_succ_apply]
          simp only [length] at hk
          exact ih (g i q) k (by omega)

lemma length_iterate (g : Fin 2 → Q → R) (p : TwoPlan Q R α) (k : ℕ) :
    length g ((step g)^[k] p) = length g p - k := by
  induction p generalizing k with
  | done a => simp [iterate_step_done, length]
  | ask i q next ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [Function.iterate_succ_apply]
          simp only [step, length]
          rw [ih (g i q) k]
          omega

lemma calls_iterate_succ (g : Fin 2 → Q → R) (q0 : Q) (j : Fin 2) (p : TwoPlan Q R α) (k : ℕ)
    (hk : k < length g p) :
    calls g j ((step g)^[k] p) =
      (if (index q0 ((step g)^[k] p)).1 = j then 1 else 0) + calls g j ((step g)^[k + 1] p) := by
  rw [Function.iterate_succ_apply']
  generalize hs : (step g)^[k] p = s
  have hl : 0 < length g s := by rw [← hs, length_iterate]; omega
  cases s with
  | done a => simp [length] at hl
  | ask i q next => by_cases h : i = j <;> simp [calls, index, step, h]

lemma step_eq_advance (g : Fin 2 → Q → R) (q0 : Q) (s : TwoPlan Q R α) :
    step g s = advance s (g (index q0 s).1 (index q0 s).2) := by
  cases s <;> rfl

lemma execute_eq_eval (g : Fin 2 → Q → R) (q0 : Q) (a0 : α) (p : TwoPlan Q R α)
    (O : Oracle Q R 2) (hO : ∀ hist i q s, O.answer hist (i, q) s = g i q)
    (B : Fin 2 → ℕ) (hB : ∀ j, calls g j p ≤ B j) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm q0 a0 p) B () ξ = eval g p := by
  have hO' : ∀ hist qq s, O.answer hist qq s = g qq.1 qq.2 := fun hist qq s => hO hist qq.1 qq.2 s
  let pc : ℕ → Fin 2 → ℕ := fun k j =>
    ((List.range k).filter (fun s => (index q0 ((step g)^[s] p)).1 = j)).length
  have hpc : ∀ k j, pc (k + 1) j =
      pc k j + (if (index q0 ((step g)^[k] p)).1 = j then 1 else 0) := by
    intro k j
    simp only [pc, List.range_succ, List.filter_append, List.length_append]
    split_ifs with h <;> simp [h]
  have hinv : ∀ k j, k ≤ length g p → pc k j + calls g j ((step g)^[k] p) = calls g j p := by
    intro k j hk
    induction k with
    | zero => simp [pc]
    | succ k ih =>
        have h1 := ih (by omega)
        have h2 := calls_iterate_succ g q0 j p k (by omega)
        rw [hpc]
        omega
  apply execute_eq_of_safe_prefix O (algorithm q0 a0 p) B () ξ (fun k => (step g)^[k] p)
    (fun k j => B j - pc k j) (length g p) (eval g p)
  · rfl
  · intro history
    change (step g)^[history.length + 1] p = advance ((step g)^[history.length] p)
      (O.answer history (index q0 ((step g)^[history.length] p)) (ξ history.length))
    rw [Function.iterate_succ_apply', hO']
    exact step_eq_advance g q0 _
  · funext j; simp [pc]
  · intro k
    funext j
    change B j - pc (k + 1) j = Function.update (fun j => B j - pc k j)
      (index q0 ((step g)^[k] p)).1 (B (index q0 ((step g)^[k] p)).1 -
        pc k (index q0 ((step g)^[k] p)).1 - 1) j
    by_cases h : j = (index q0 ((step g)^[k] p)).1
    · rw [h, Function.update_self, hpc]
      simp only [↓reduceIte]
      omega
    · have h' : ¬ (index q0 ((step g)^[k] p)).1 = j := fun e => h e.symm
      rw [Function.update_of_ne h, hpc]
      simp only [h', ↓reduceIte, add_zero]
  · intro k hk
    change 0 < B (index q0 ((step g)^[k] p)).1 - pc k (index q0 ((step g)^[k] p)).1
    have hl : 0 < length g ((step g)^[k] p) := by rw [length_iterate]; omega
    have h1 := hinv k (index q0 ((step g)^[k] p)).1 hk.le
    have h2 : 0 < calls g (index q0 ((step g)^[k] p)).1 ((step g)^[k] p) := by
      generalize (step g)^[k] p = s at hl ⊢
      cases s with
      | done a => simp [length] at hl
      | ask i q next => simp [index, calls]
    have h3 := hB (index q0 ((step g)^[k] p)).1
    omega
  · intro k hk
    change result a0 ((step g)^[k] p) = _
    rw [iterate_step_of_length_le g p k hk]
    rfl
  · rw [length_eq, Fin.sum_univ_two]
    exact Nat.add_le_add (hB 0) (hB 1)

end TwoPlan

end LongTails.Proofs.AuxiliaryPlan
