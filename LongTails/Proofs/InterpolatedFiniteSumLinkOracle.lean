import LongTails.Proofs.InterpolatedFiniteSumOwnerExecution
import LongTails.Proofs.Execution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open OracleTemplate Classical

namespace LongTails.Proofs.InterpolatedFiniteSumLinkOracle

variable {Q V O : Type*} {m T d : ℕ}

noncomputable def decoded (owner : Q → Fin m) (link : (Fin T → Fin d) → ℕ → Q → V)
    (inactive : Q → V) (π : Fin T → Fin d) (past : List (Fin m)) (bit : Bool) (q : Q) : V :=
  if owner q ∈ past then link π (past.idxOf (owner q)) q
  else if bit then link π past.length q else inactive q

lemma decoded_local (owner : Q → Fin m) (link : (Fin T → Fin d) → ℕ → Q → V)
    (inactive : Q → V)
    (hlink : ∀ π ρ j q, (∀ i : Fin T, i.val ≤ j → π i = ρ i) → link π j q = link ρ j q)
    (π ρ : Fin T → Fin d) (past : List (Fin m)) (bit : Bool) (q : Q)
    (h : ∀ i : Fin T, i.val < past.length + (if bit then 1 else 0) → π i = ρ i) :
    decoded owner link inactive π past bit q = decoded owner link inactive ρ past bit q := by
  by_cases hp : owner q ∈ past
  · simp only [decoded, ite_eq_left hp]
    apply hlink
    intro i hi
    apply h i
    have hj := List.idxOf_lt_length_of_mem hp
    omega
  · simp only [decoded, ite_eq_right hp]
    cases bit with
    | false => rfl
    | true =>
      apply hlink
      intro i hi
      apply h i
      simpa only [Bool.true_eq, ite_true] using (show i.val < past.length + 1 by omega)

abbrev ReplayState (A : Algorithm Q V O) (m : ℕ) := A.State × List (Fin m)

noncomputable def query (A : Algorithm Q V O) (owner : Q → Fin m) (s : ReplayState A m) : Fin m :=
  owner (A.query s.1).2

noncomputable def update (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (π : Fin T → Fin d) (s : ReplayState A m) (bit : Bool) : ReplayState A m :=
  (A.update s.1 (decoded owner link inactive π s.2 bit (A.query s.1).2),
    if bit then s.2 ++ [owner (A.query s.1).2] else s.2)

abbrev State (A : Algorithm Q V O) (m : ℕ) := ReplayState A m × List (Fin m) × ℕ

noncomputable def hit (A : Algorithm Q V O) (owner : Q → Fin m) (s : State A m) : Bool :=
  match s.2.1 with
  | [] => false
  | a :: _ => decide (query A owner s.1 = a)

noncomputable def step (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (π : Fin T → Fin d) : State A m → State A m :=
  InterpolatedFiniteSumOwnerExecution.step (query A owner) (update A owner link inactive π)

lemma step_eq (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (π : Fin T → Fin d) (s : State A m) :
    step A owner link inactive π s =
      (update A owner link inactive π s.1 (hit A owner s),
        if hit A owner s then s.2.1.tail else s.2.1,
        s.2.2 + if hit A owner s then 1 else 0) := by
  rcases s with ⟨s, w, c⟩
  cases w with
  | nil => simp [step, hit, InterpolatedFiniteSumOwnerExecution.step]
  | cons a w =>
    by_cases h : query A owner s = a <;>
      simp [step, hit, InterpolatedFiniteSumOwnerExecution.step, h]

noncomputable def reveal (A : Algorithm Q V O) (owner : Q → Fin m) (s : State A m) : Finset (Fin T) :=
  Finset.univ.filter (fun i => i.val < s.1.2.length + if hit A owner s then 1 else 0)

lemma step_local (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (hlink : ∀ π ρ j q, (∀ i : Fin T, i.val ≤ j → π i = ρ i) → link π j q = link ρ j q)
    (π ρ : Fin T → Fin d) (s : State A m)
    (h : ∀ i ∈ reveal A owner s, π i = ρ i) : step A owner link inactive π s = step A owner link inactive ρ s := by
  rw [step_eq, step_eq]
  have hh := decoded_local owner link inactive hlink π ρ s.1.2 (hit A owner s) (A.query s.1.1).2
    (by intro i hi; exact h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
  simp only [update, hh]

noncomputable def process (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (initial : A.State) (w : List (Fin m)) (π : Fin T → Fin d) (b : ℕ) : State A m × Finset (Fin T) :=
  InterpolatedFiniteSumHiding.run (step A owner link inactive) (reveal A owner) ((initial, []), w, 0) π b

lemma process_state (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (initial : A.State) (w : List (Fin m)) (π : Fin T → Fin d) (b : ℕ) :
    (process A owner link inactive initial w π b).1 =
      (step A owner link inactive π)^[b] ((initial, []), w, 0) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change step A owner link inactive π (process A owner link inactive initial w π b).1 = _
    rw [Function.iterate_succ_apply', ih]

lemma process_seen (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (initial : A.State) (w : List (Fin m)) (π : Fin T → Fin d) (b : ℕ) (i : Fin T) :
    i ∈ (process A owner link inactive initial w π b).2 ↔
      i.val < (process A owner link inactive initial w π b).1.1.2.length := by
  induction b with
  | zero => simp [process, InterpolatedFiniteSumHiding.run]
  | succ b ih =>
    change i ∈ (process A owner link inactive initial w π b).2 ∪
      reveal A owner (process A owner link inactive initial w π b).1 ↔ _
    rw [Finset.mem_union, ih]
    simp only [reveal, Finset.mem_filter, Finset.mem_univ, true_and]
    change _ ↔ i.val < (step A owner link inactive π (process A owner link inactive initial w π b).1).1.2.length
    rw [step_eq]
    simp only [update]
    cases hit A owner (process A owner link inactive initial w π b).1 <;>
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero, ite_true,
        List.length_append, List.length_singleton] <;> omega

lemma process_prefix (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (initial : A.State) (w : List (Fin m)) (π : Fin T → Fin d) (b : ℕ) :
    (process A owner link inactive initial w π b).1.1.2 ++
      (process A owner link inactive initial w π b).1.2.1 = w := by
  rw [process_state]
  exact InterpolatedFiniteSumOwnerExecution.iterate_prefix (query A owner) (update A owner link inactive π)
    Prod.snd (by intros; rfl) (by intros; rfl) b ((initial, []), w, 0)

lemma process_discoveries (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (initial : A.State) (w : List (Fin m)) (π : Fin T → Fin d) (b : ℕ) :
    (process A owner link inactive initial w π b).1.1.2.length =
      FiniteSumNondualLowerSearch.discoveries m b
        (InterpolatedFiniteSumOwnerExecution.policy (query A owner) (update A owner link inactive π) (initial, [])) w := by
  rw [process_state]
  simpa only [step, List.length_nil, Nat.zero_add] using InterpolatedFiniteSumOwnerExecution.iterate_past_length (query A owner) (update A owner link inactive π)
    Prod.snd (by intros; rfl) (by intros; rfl) b (initial, []) w

lemma process_coupling (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V) (full : Q → V)
    (initial : A.State) (w : List (Fin m)) (π : Fin T → Fin d) (b : ℕ)
    (h : ∀ t < b,
      let s := (process A owner link inactive initial w π t).1
      full (A.query s.1.1).2 = decoded owner link inactive π s.1.2 (hit A owner s) (A.query s.1.1).2) :
    (fun s => A.update s (full (A.query s).2))^[b] initial =
      (process A owner link inactive initial w π b).1.1.1 := by
  have he (t : ℕ) (ht : t ≤ b) :
      (fun s => A.update s (full (A.query s).2))^[t] initial =
        (process A owner link inactive initial w π t).1.1.1 := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by omega), h t (by omega)]
      change _ = (step A owner link inactive π (process A owner link inactive initial w π t).1).1.1
      rw [step_eq]
      rfl
  exact he b le_rfl

noncomputable def observation (A : Algorithm Q V O) (point : Q → EuclideanSpace ℝ (Fin d))
    (outputPoint : O → EuclideanSpace ℝ (Fin d)) (b : ℕ) (j : Fin (b + 1)) (s : State A m) :
    EuclideanSpace ℝ (Fin d) :=
  if j.val = b then outputPoint (A.output s.1.1) else point (A.query s.1.1).2

noncomputable def Bad (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (point : Q → EuclideanSpace ℝ (Fin d)) (outputPoint : O → EuclideanSpace ℝ (Fin d))
    (initial : A.State) (w : List (Fin m)) (b : ℕ) (B θ : ℝ) (carrier : Fin d) (π : Fin T → Fin d) : Prop :=
  ¬Function.Injective π ∨ (∃ i, π i = carrier) ∨
    ∃ j : Fin (b + 1), ∃ i, i ∉ (process A owner link inactive initial w π j.val).2 ∧
      π i ∈ SmoothConvexFiniteHiding.largeSet B θ
        (observation A point outputPoint b j (process A owner link inactive initial w π j.val).1)

lemma bad_bound (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (hlink : ∀ π ρ j q, (∀ i : Fin T, i.val ≤ j → π i = ρ i) → link π j q = link ρ j q)
    (point : Q → EuclideanSpace ℝ (Fin d)) (outputPoint : O → EuclideanSpace ℝ (Fin d))
    (initial : A.State) (w : List (Fin m)) (b : ℕ) (B θ : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (carrier : Fin d) :
    (d : ℝ) * (∑ π : Fin T → Fin d,
      if Bad A owner link inactive point outputPoint initial w b B θ carrier π then (1 : ℝ) else 0) ≤
      ((T : ℝ) ^ 2 + T + (b + 1 : ℕ) * T * (B ^ 2 / θ ^ 2)) * Fintype.card (Fin T → Fin d) := by
  have h := InterpolatedFiniteSumHiding.combined_bad_bound (step A owner link inactive) (reveal A owner)
    ((initial, []), w, 0) (step_local A owner link inactive hlink) (fun j : Fin (b + 1) => j.val)
    (observation A point outputPoint b) B θ hB hθ carrier
  simp only [Fintype.card_fin] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  dsimp only [Bad, process]
  split_ifs with hh
  · simp_all only
  · simp_all only

lemma good_coordinate (A : Algorithm Q V O) (owner : Q → Fin m)
    (link : (Fin T → Fin d) → ℕ → Q → V) (inactive : Q → V)
    (point : Q → EuclideanSpace ℝ (Fin d)) (outputPoint : O → EuclideanSpace ℝ (Fin d))
    (initial : A.State) (w : List (Fin m)) (b : ℕ) (B θ : ℝ) (carrier : Fin d) (π : Fin T → Fin d)
    (hgood : ¬Bad A owner link inactive point outputPoint initial w b B θ carrier π)
    (j : Fin (b + 1)) (i : Fin T)
    (hcount : (process A owner link inactive initial w π j.val).1.1.2.length ≤ i.val)
    (hnear : ‖observation A point outputPoint b j (process A owner link inactive initial w π j.val).1‖ ≤ B) :
    |observation A point outputPoint b j (process A owner link inactive initial w π j.val).1 (π i)| ≤ θ := by
  apply SmoothConvexFiniteHiding.not_largeSet_small B θ _ hnear
  intro hlarge
  apply hgood
  right; right
  refine ⟨j, i, ?_, hlarge⟩
  rw [process_seen]
  omega

noncomputable def test (owner : Q → Fin m) (q : Q) : List (Fin m) → Bool
  | [] => false
  | a :: _ => decide (owner q = a)

noncomputable def lookup (owner : Q → Fin m) (link : (Fin T → Fin d) → ℕ → Q → V)
    (inactive : Q → V) (π : Fin T → Fin d) (w : List (Fin m)) (q : Q) : V :=
  if owner q ∈ w then link π (w.idxOf (owner q)) q else inactive q

lemma decoded_lookup (owner : Q → Fin m) (link : (Fin T → Fin d) → ℕ → Q → V)
    (inactive : Q → V) (π : Fin T → Fin d) (past rest : List (Fin m)) (q : Q)
    (hfuture : ∀ j, past.length < j → link π j q = inactive q) :
    decoded owner link inactive π past (test owner q rest) q =
      lookup owner link inactive π (past ++ rest) q := by
  by_cases hp : owner q ∈ past
  · have hm : owner q ∈ past ++ rest := List.mem_append_left rest hp
    simp only [decoded, lookup, ite_eq_left hp, ite_eq_left hm, List.idxOf_append_of_mem hp]
  · cases rest with
    | nil => simp [decoded, lookup, test, hp]
    | cons a rest =>
      by_cases ha : owner q = a
      · have hap : a ∉ past := by simpa only [ha] using hp
        simp [decoded, lookup, test, ha, hap, List.idxOf_append_of_notMem hap]
      · have hidx : (past ++ a :: rest).idxOf (owner q) = past.length + (a :: rest).idxOf (owner q) :=
          List.idxOf_append_of_notMem hp
        have hpos : past.length < (past ++ a :: rest).idxOf (owner q) := by
          rw [hidx, List.idxOf_cons_ne rest (Ne.symm ha)]
          omega
        have hh := hfuture _ hpos
        simp only [decoded, ite_eq_right hp, test, decide_eq_false ha, Bool.false_eq_true, ite_false,
          lookup, hh]
        split_ifs <;> rfl

end LongTails.Proofs.InterpolatedFiniteSumLinkOracle
