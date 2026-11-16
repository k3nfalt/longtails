import LongTails.Proofs.InterpolatedFiniteSumDistinctSearch
import LongTails.Proofs.InterpolatedFiniteSumHiding

namespace LongTails.Proofs.InterpolatedFiniteSumOwnerExecution

open FiniteSumNondualLowerSearch (discoveries)

variable {S : Type*} {m : ℕ}

def replay (update : S → Bool → S) : S → List Bool → S
  | s, [] => s
  | s, bit :: h => replay update (update s bit) h

def policy (query : S → Fin m) (update : S → Bool → S) (s : S) (h : List Bool) : Fin m :=
  query (replay update s h)

lemma policy_cons (query : S → Fin m) (update : S → Bool → S) (s : S) (bit : Bool) :
    (fun h => policy query update s (bit :: h)) = policy query update (update s bit) := rfl

def step (query : S → Fin m) (update : S → Bool → S) (s : S × List (Fin m) × ℕ) :
    S × List (Fin m) × ℕ :=
  match s.2.1 with
  | [] => (update s.1 false, [], s.2.2)
  | a :: w => if query s.1 = a then (update s.1 true, w, s.2.2 + 1)
    else (update s.1 false, a :: w, s.2.2)

lemma discoveries_nil (b : ℕ) (q : List Bool → Fin m) : discoveries m b q [] = 0 := by
  cases b <;> rfl

lemma iterate_count (query : S → Fin m) (update : S → Bool → S) (b : ℕ)
    (s : S) (w : List (Fin m)) (c : ℕ) :
    ((step query update)^[b] (s, w, c)).2.2 = c + discoveries m b (policy query update s) w := by
  induction b generalizing s w c with
  | zero => simp [discoveries]
  | succ b ih =>
    rw [Function.iterate_succ_apply]
    cases w with
    | nil => simp only [step, ih, discoveries_nil, discoveries, Nat.add_zero]
    | cons a w =>
      by_cases h : query s = a
      · simp [step, h, ih, discoveries, policy, replay, Nat.add_assoc]
        rfl
      · simp [step, h, ih, discoveries, policy, replay]
        rfl

lemma step_prefix (query : S → Fin m) (update : S → Bool → S) (past : S → List (Fin m))
    (ht : ∀ s, past (update s true) = past s ++ [query s])
    (hf : ∀ s, past (update s false) = past s) (s : S × List (Fin m) × ℕ) :
    past (step query update s).1 ++ (step query update s).2.1 = past s.1 ++ s.2.1 := by
  rcases s with ⟨s, w, c⟩
  cases w with
  | nil => simp only [step, hf]
  | cons a w =>
    by_cases h : query s = a
    · simp [step, h, ht, List.append_assoc]
    · simp only [step, ite_eq_right h, hf]

lemma iterate_prefix (query : S → Fin m) (update : S → Bool → S) (past : S → List (Fin m))
    (ht : ∀ s, past (update s true) = past s ++ [query s])
    (hf : ∀ s, past (update s false) = past s) (b : ℕ) (s : S × List (Fin m) × ℕ) :
    past ((step query update)^[b] s).1 ++ ((step query update)^[b] s).2.1 = past s.1 ++ s.2.1 := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Function.iterate_succ_apply', step_prefix query update past ht hf]
    exact ih

lemma iterate_past_length (query : S → Fin m) (update : S → Bool → S) (past : S → List (Fin m))
    (ht : ∀ s, past (update s true) = past s ++ [query s])
    (hf : ∀ s, past (update s false) = past s) (b : ℕ) (s : S) (w : List (Fin m)) :
    (past ((step query update)^[b] (s, w, 0)).1).length =
      (past s).length + discoveries m b (policy query update s) w := by
  have hinv : ∀ b (s : S) w c,
      (past ((step query update)^[b] (s, w, c)).1).length + c =
        (past s).length + ((step query update)^[b] (s, w, c)).2.2 := by
    intro b
    induction b with
    | zero => intros; rfl
    | succ b ih =>
      intro s w c
      rw [Function.iterate_succ_apply]
      cases w with
      | nil => simpa only [step, hf] using ih (update s false) [] c
      | cons a w =>
        by_cases h : query s = a
        · simp only [step, ite_eq_left h]
          have hh := ih (update s true) w (c + 1)
          rw [ht, List.length_append, List.length_singleton] at hh
          omega
        · simpa only [step, ite_eq_right h, hf] using ih (update s false) (a :: w) c
  have hh := hinv b s w 0
  simpa only [Nat.add_zero, iterate_count, Nat.zero_add] using hh

end LongTails.Proofs.InterpolatedFiniteSumOwnerExecution
