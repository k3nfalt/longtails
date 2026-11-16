import LongTails.Proofs.InterpolatedFiniteSumHiding
import LongTails.Proofs.Execution
import LongTails.Proofs.SparseGroupExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open OracleTemplate Classical

namespace LongTails.Proofs.InterpolatedFiniteSumBlockExecution

open InterpolatedFiniteSumHiding

variable {Q V O : Type*} {g T d : ℕ}

abbrev State (A : Algorithm Q V O) (g : ℕ) := A.State × (Fin g → ℕ)

noncomputable def step (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (π : (Fin g × Fin T) → Fin d) (s : State A g) : State A g :=
  let q := (A.query s.1).2
  let i := which q
  (A.update s.1 (reply π q (s.2 i)), Function.update s.2 i (min (s.2 i + 1) T))

noncomputable def reveal (A : Algorithm Q V O) (which : Q → Fin g) (s : State A g) :
    Finset (Fin g × Fin T) :=
  Finset.univ.filter (fun ij => ij.1 = which (A.query s.1).2 ∧ ij.2.val < s.2 ij.1 + 1)

noncomputable def process (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (initial : A.State) (π : (Fin g × Fin T) → Fin d) (t : ℕ) :
    State A g × Finset (Fin g × Fin T) :=
  run (step A which reply) (reveal A which) (initial, fun _ => 0) π t

lemma step_local (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (hreply : ∀ π ρ q r, (∀ j : Fin T, j.val < r + 1 → π (which q, j) = ρ (which q, j)) →
      reply π q r = reply ρ q r)
    (π ρ : (Fin g × Fin T) → Fin d) (s : State A g)
    (h : ∀ ij ∈ reveal A which s, π ij = ρ ij) : step A which reply π s = step A which reply ρ s := by
  have he : reply π (A.query s.1).2 (s.2 (which (A.query s.1).2)) =
      reply ρ (A.query s.1).2 (s.2 (which (A.query s.1).2)) := by
    apply hreply
    intro j hj
    exact h _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hj⟩)
  simp only [step, he]

lemma process_counts_le (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (initial : A.State) (π : (Fin g × Fin T) → Fin d) (t : ℕ) (i : Fin g) :
    (process A which reply initial π t).1.2 i ≤ T := by
  induction t with
  | zero => simp [process, run]
  | succ t ih =>
    change Function.update (process A which reply initial π t).1.2
      (which (A.query (process A which reply initial π t).1.1).2)
      (min ((process A which reply initial π t).1.2
        (which (A.query (process A which reply initial π t).1.1).2) + 1) T) i ≤ T
    simp only [Function.update_apply]
    split_ifs
    · exact Nat.min_le_right _ _
    · exact ih

lemma process_count_sum (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (initial : A.State) (π : (Fin g × Fin T) → Fin d) (t : ℕ) :
    (∑ i, (process A which reply initial π t).1.2 i) ≤ t := by
  induction t with
  | zero => simp [process, run]
  | succ t ih =>
    let s := (process A which reply initial π t).1
    let i := which (A.query s.1).2
    change (∑ j, Function.update s.2 i (min (s.2 i + 1) T) j) ≤ t + 1
    calc
      _ ≤ ∑ j, Function.update s.2 i (s.2 i + 1) j := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : j = i
        · subst j
          simp only [Function.update_self, Nat.min_le_left]
        · simp only [Function.update_of_ne h, le_refl]
      _ = (∑ j, s.2 j) + 1 := SparseGroupExecution.sum_update_increment _ _
      _ ≤ _ := Nat.add_le_add_right ih 1

lemma process_seen (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (initial : A.State) (π : (Fin g × Fin T) → Fin d) (t : ℕ) (ij : Fin g × Fin T) :
    ij ∈ (process A which reply initial π t).2 ↔ ij.2.val < (process A which reply initial π t).1.2 ij.1 := by
  induction t with
  | zero => simp [process, run]
  | succ t ih =>
    change ij ∈ (process A which reply initial π t).2 ∪
      reveal A which (process A which reply initial π t).1 ↔ _
    rw [Finset.mem_union, ih]
    simp only [reveal, Finset.mem_filter, Finset.mem_univ, true_and]
    change ij.2.val < (process A which reply initial π t).1.2 ij.1 ∨
        ij.1 = which (A.query (process A which reply initial π t).1.1).2 ∧
          ij.2.val < (process A which reply initial π t).1.2 ij.1 + 1 ↔
      ij.2.val < Function.update (process A which reply initial π t).1.2
        (which (A.query (process A which reply initial π t).1.1).2)
        (min ((process A which reply initial π t).1.2
          (which (A.query (process A which reply initial π t).1.1).2) + 1) T) ij.1
    by_cases h : ij.1 = which (A.query (process A which reply initial π t).1.1).2
    · rw [h, Function.update_self]
      have hj := ij.2.isLt
      simp only [true_and]
      omega
    · simp only [h, false_and, or_false, Function.update_of_ne h]

lemma process_coupling (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (full : Q → V) (initial : A.State) (π : (Fin g × Fin T) → Fin d) (b : ℕ)
    (h : ∀ t < b, full (A.query (process A which reply initial π t).1.1).2 =
      reply π (A.query (process A which reply initial π t).1.1).2
        ((process A which reply initial π t).1.2
          (which (A.query (process A which reply initial π t).1.1).2))) :
    (fun s => A.update s (full (A.query s).2))^[b] initial =
      (process A which reply initial π b).1.1 := by
  have he (t : ℕ) (ht : t ≤ b) :
      (fun s => A.update s (full (A.query s).2))^[t] initial =
        (process A which reply initial π t).1.1 := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by omega), h t (by omega)]
      rfl
  exact he b le_rfl

noncomputable def observation (A : Algorithm Q V O) (point : Q → EuclideanSpace ℝ (Fin d))
    (outputPoint : O → EuclideanSpace ℝ (Fin d)) (b : ℕ) (j : Fin (b + 1))
    (s : State A g) : EuclideanSpace ℝ (Fin d) :=
  if j.val = b then outputPoint (A.output s.1) else point (A.query s.1).2

noncomputable def Bad (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (point : Q → EuclideanSpace ℝ (Fin d)) (outputPoint : O → EuclideanSpace ℝ (Fin d))
    (initial : A.State) (b : ℕ) (B θ : ℝ) (carrier : Fin d)
    (π : (Fin g × Fin T) → Fin d) : Prop :=
  ¬Function.Injective π ∨ (∃ ij, π ij = carrier) ∨
    ∃ j : Fin (b + 1), ∃ ij, ij ∉ (process A which reply initial π j.val).2 ∧
      π ij ∈ SmoothConvexFiniteHiding.largeSet B θ
        (observation A point outputPoint b j (process A which reply initial π j.val).1)

lemma bad_bound (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (hreply : ∀ π ρ q r, (∀ j : Fin T, j.val < r + 1 → π (which q, j) = ρ (which q, j)) →
      reply π q r = reply ρ q r)
    (point : Q → EuclideanSpace ℝ (Fin d)) (outputPoint : O → EuclideanSpace ℝ (Fin d))
    (initial : A.State) (b : ℕ) (B θ : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (carrier : Fin d) :
    (d : ℝ) * (∑ π : (Fin g × Fin T) → Fin d,
      if Bad A which reply point outputPoint initial b B θ carrier π then (1 : ℝ) else 0) ≤
      (((g : ℝ) * T) ^ 2 + g * T + (b + 1 : ℕ) * g * T * (B ^ 2 / θ ^ 2)) *
        Fintype.card ((Fin g × Fin T) → Fin d) := by
  have h := combined_bad_bound (step A which reply) (reveal A which) (initial, fun _ => 0)
    (step_local A which reply hreply) (fun j : Fin (b + 1) => j.val)
    (observation A point outputPoint b) B θ hB hθ carrier
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, mul_assoc] at h ⊢
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  dsimp only [Bad, process]
  split_ifs <;> rfl

lemma good_coordinate (A : Algorithm Q V O) (which : Q → Fin g)
    (reply : ((Fin g × Fin T) → Fin d) → Q → ℕ → V)
    (point : Q → EuclideanSpace ℝ (Fin d)) (outputPoint : O → EuclideanSpace ℝ (Fin d))
    (initial : A.State) (b : ℕ) (B θ : ℝ) (carrier : Fin d)
    (π : (Fin g × Fin T) → Fin d)
    (hgood : ¬Bad A which reply point outputPoint initial b B θ carrier π)
    (j : Fin (b + 1)) (ij : Fin g × Fin T)
    (hcount : (process A which reply initial π j.val).1.2 ij.1 ≤ ij.2.val)
    (hnear : ‖observation A point outputPoint b j (process A which reply initial π j.val).1‖ ≤ B) :
    |observation A point outputPoint b j (process A which reply initial π j.val).1 (π ij)| ≤ θ := by
  apply SmoothConvexFiniteHiding.not_largeSet_small B θ _ hnear
  intro hlarge
  apply hgood
  right; right
  refine ⟨j, ij, ?_, hlarge⟩
  rw [process_seen]
  omega

end LongTails.Proofs.InterpolatedFiniteSumBlockExecution
