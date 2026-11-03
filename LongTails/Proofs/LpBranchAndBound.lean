import LongTails.Algorithms.LpBranchAndBound
import LongTails.Proofs.Execution
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OracleTemplate.BoundedMixedIntegerLinear

open LongTails.Setups.BoundedMixedIntegerLinear Matrix

def MemBox (P : Params) (β : Box P) (z : Fin P.p → ℤ) : Prop := ∀ j, β.1 j ≤ z j ∧ z j ≤ β.2 j

def boxCard (P : Params) (β : Box P) : ℕ := ∏ j, (β.2 j - β.1 j + 1).toNat

def potential (P : Params) (stack : List (Box P)) : ℕ :=
  (stack.map fun β => 2 * boxCard P β - 1).sum

structure Good (P : Params) (s : SearchState P) : Prop where
  nonempty : ∀ β ∈ s.stack, BoxNonempty P β
  feasible : ∀ x, s.incumbent = some x → MixedFeasible P x
  covered : ∀ x, MixedFeasible P x → Improves P s.incumbent (objective P (toPoint P x)) →
    ∃ β ∈ s.stack, MemBox P β x.1

lemma boxCard_pos {P : Params} {β : Box P} (h : BoxNonempty P β) : 0 < boxCard P β := by
  unfold boxCard
  apply Finset.prod_pos
  intro j _
  have := h j
  omega

lemma boxCard_split {P : Params} (β : Box P) (j : Fin P.p) (t : ℤ) (h1 : β.1 j ≤ t)
    (h2 : t + 1 ≤ β.2 j) :
    boxCard P (leftChild P β j t) + boxCard P (rightChild P β j t) = boxCard P β := by
  unfold boxCard leftChild rightChild
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => (β.2 i - β.1 i + 1).toNat) (Finset.mem_univ j)]
  have e1 : ∏ i ∈ Finset.univ.erase j, (Function.update β.2 j t i - β.1 i + 1).toNat =
      ∏ i ∈ Finset.univ.erase j, (β.2 i - β.1 i + 1).toNat := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have e2 : ∏ i ∈ Finset.univ.erase j, (β.2 i - Function.update β.1 j (t + 1) i + 1).toNat =
      ∏ i ∈ Finset.univ.erase j, (β.2 i - β.1 i + 1).toNat := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only at e1 e2 ⊢
  rw [e1, e2, Function.update_self, Function.update_self, ← add_mul]
  congr 1
  omega

lemma potential_cons (P : Params) (β : Box P) (rest : List (Box P)) :
    potential P (β :: rest) = (2 * boxCard P β - 1) + potential P rest := by
  simp [potential]

lemma relaxation_of_mixed {P : Params} {β : Box P} {x : Solution P} (hx : MixedFeasible P x)
    (hβ : MemBox P β x.1) : RelaxationFeasible P β (toPoint P x) := by
  refine ⟨hx.1, fun j => ?_, fun j => ?_⟩
  · show ((P.lo j : ℤ) : ℝ) ≤ (x.1 j : ℝ) ∧ (x.1 j : ℝ) ≤ ((P.hi j : ℤ) : ℝ)
    exact ⟨by exact_mod_cast (hx.2 j).1, by exact_mod_cast (hx.2 j).2⟩
  · show ((β.1 j : ℤ) : ℝ) ≤ (x.1 j : ℝ) ∧ (x.1 j : ℝ) ≤ ((β.2 j : ℤ) : ℝ)
    exact ⟨by exact_mod_cast (hβ j).1, by exact_mod_cast (hβ j).2⟩

lemma floor_add_one_le {r : ℝ} {u : ℤ} (hr : Int.fract r ≠ 0) (hu : r ≤ u) : ⌊r⌋ + 1 ≤ u := by
  have hlt : (⌊r⌋ : ℝ) < r := by
    rcases (Int.floor_le r).lt_or_eq with h | h
    · exact h
    · exact absurd (show Int.fract r = 0 by rw [Int.fract]; linarith) hr
  have : ⌊r⌋ < u := by exact_mod_cast hlt.trans_le hu
  omega

lemma cast_floor_of_fract {r : ℝ} (hr : Int.fract r = 0) : (⌊r⌋ : ℝ) = r := by
  rw [Int.fract] at hr
  linarith

lemma branchUpdate_nil (P : Params) (s : SearchState P) (r : Option (Point P))
    (h : s.stack = []) : branchUpdate P s r = s := by
  unfold branchUpdate
  rw [h]

lemma good_update {P : Params} {s : SearchState P} (hs : Good P s) {r : Option (Point P)}
    (hr : SolvesRelaxation P (s.stack.headD (P.lo, P.hi)) r) (hne : s.stack ≠ []) :
    Good P (branchUpdate P s r) ∧
      potential P (branchUpdate P s r).stack + 1 ≤ potential P s.stack := by
  obtain ⟨stack, inc⟩ := s
  obtain _ | ⟨β, rest⟩ := stack
  · exact absurd rfl hne
  have hβ : BoxNonempty P β := hs.nonempty β (by simp)
  have hcard := boxCard_pos hβ
  have hpot := potential_cons P β rest
  simp only [List.headD_cons] at hr
  have hrest : Good P ⟨rest, inc⟩ → Good P ⟨rest, inc⟩ ∧
      potential P rest + 1 ≤ potential P (β :: rest) := fun h => ⟨h, by omega⟩
  cases r with
  | none =>
    refine hrest ⟨fun γ hγ => hs.nonempty γ (by simp [hγ]), hs.feasible, fun x hx himp => ?_⟩
    obtain ⟨γ, hγ, hmem⟩ := hs.covered x hx himp
    rcases List.mem_cons.1 hγ with rfl | hγ
    · exact absurd (relaxation_of_mixed hx hmem) (hr _)
    · exact ⟨γ, hγ, hmem⟩
  | some y =>
    change Good P (processNode P β rest inc y) ∧
      potential P (processNode P β rest inc y).stack + 1 ≤ potential P (β :: rest)
    unfold processNode
    by_cases himp : Improves P inc (objective P y)
    · rw [ite_eq_right (not_not.2 himp)]
      by_cases hfrac : ∃ j, Int.fract (y.1 j) ≠ 0
      · rw [dite_eq_left hfrac]
        set j := hfrac.choose
        have hj : Int.fract (y.1 j) ≠ 0 := hfrac.choose_spec
        set t := ⌊y.1 j⌋
        have hlo : β.1 j ≤ t := Int.le_floor.2 (hr.1.2.2 j).1
        have hhi : t + 1 ≤ β.2 j := floor_add_one_le hj (hr.1.2.2 j).2
        have hsplit := boxCard_split β j t hlo hhi
        have hL : BoxNonempty P (leftChild P β j t) := by
          intro i
          by_cases hi : i = j
          · subst hi; simp [leftChild, hlo]
          · simp [leftChild, Function.update_of_ne hi, hβ i]
        have hR : BoxNonempty P (rightChild P β j t) := by
          intro i
          by_cases hi : i = j
          · subst hi; simp [rightChild, hhi]
          · simp [rightChild, Function.update_of_ne hi, hβ i]
        have hcL := boxCard_pos hL
        have hcR := boxCard_pos hR
        refine ⟨⟨fun γ hγ => ?_, hs.feasible, fun x hx hxi => ?_⟩, ?_⟩
        · simp only [List.mem_cons] at hγ
          rcases hγ with rfl | rfl | hγ
          · exact hL
          · exact hR
          · exact hs.nonempty γ (by simp [hγ])
        · obtain ⟨γ, hγ, hmem⟩ := hs.covered x hx hxi
          rcases List.mem_cons.1 hγ with rfl | hγ
          · rcases le_or_gt (x.1 j) t with hle | hlt
            · refine ⟨leftChild P γ j t, by simp, fun i => ?_⟩
              by_cases hi : i = j
              · rw [hi]; simp [leftChild, hle, (hmem j).1]
              · simp [leftChild, Function.update_of_ne hi, hmem i]
            · refine ⟨rightChild P γ j t, by simp, fun i => ?_⟩
              by_cases hi : i = j
              · rw [hi]; simp only [rightChild, Function.update_self]; exact ⟨by omega, (hmem j).2⟩
              · simp [rightChild, Function.update_of_ne hi, hmem i]
          · exact ⟨γ, by simp [hγ], hmem⟩
        · simp only [potential_cons] at hpot ⊢
          omega
      · rw [dite_eq_right hfrac]
        push Not at hfrac
        have hpt : toPoint P (fun j => ⌊y.1 j⌋, y.2) = y := by
          obtain ⟨z, w⟩ := y
          simp only [toPoint, Prod.mk.injEq, and_true]
          funext j
          exact cast_floor_of_fract (hfrac j)
        refine ⟨⟨fun γ hγ => hs.nonempty γ (by simp [hγ]), fun x hx => ?_, fun x hx hxi => ?_⟩, ?_⟩
        · cases hx
          refine ⟨by rw [hpt]; exact hr.1.1, fun j => ⟨?_, ?_⟩⟩
          · exact Int.le_floor.2 (hr.1.2.1 j).1
          · have h1 := (hr.1.2.1 j).2
            have h2 : (⌊y.1 j⌋ : ℝ) ≤ P.hi j := (Int.floor_le _).trans h1
            exact_mod_cast h2
        · have hlt := hxi _ rfl
          rw [hpt] at hlt
          obtain ⟨γ, hγ, hmem⟩ := hs.covered x hx (fun w hw => hlt.trans (himp w hw))
          rcases List.mem_cons.1 hγ with rfl | hγ
          · exact absurd (hr.2 _ (relaxation_of_mixed hx hmem)) (not_le.2 hlt)
          · exact ⟨γ, hγ, hmem⟩
        · simpa using (show potential P rest + 1 ≤ potential P (β :: rest) by omega)
    · rw [ite_eq_left himp]
      refine hrest ⟨fun γ hγ => hs.nonempty γ (by simp [hγ]), hs.feasible, fun x hx hxi => ?_⟩
      obtain ⟨γ, hγ, hmem⟩ := hs.covered x hx hxi
      rcases List.mem_cons.1 hγ with rfl | hγ
      · exfalso
        apply himp
        intro w hw
        exact (hr.2 _ (relaxation_of_mixed hx hmem)).trans_lt (hxi w hw)
      · exact ⟨γ, hγ, hmem⟩

lemma good_initial (P : Params) : Good P ⟨initialStack P, none⟩ := by
  classical
  refine ⟨fun β hβ => ?_, fun x hx => (by cases hx), fun x hx _ => ?_⟩
  · unfold initialStack at hβ
    split_ifs at hβ with h
    · simp only [List.mem_singleton] at hβ
      exact hβ ▸ h
    · simp at hβ
  · have h : BoxNonempty P (P.lo, P.hi) := fun j => (hx.2 j).1.trans (hx.2 j).2
    refine ⟨(P.lo, P.hi), ?_, hx.2⟩
    unfold initialStack
    rw [ite_eq_left h]
    simp

lemma potential_initial (P : Params) :
    potential P (initialStack P) ≤ 2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1 := by
  classical
  unfold initialStack
  split_ifs
  · simp [potential, boxCard]
  · simp [potential]

lemma solves_of_good {P : Params} {s : SearchState P} (hs : Good P s) (h : s.stack = []) :
    SolvesMixed P s.incumbent := by
  obtain ⟨stack, inc⟩ := s
  simp only at h
  subst h
  cases inc with
  | none =>
    intro x hx
    obtain ⟨γ, hγ, _⟩ := hs.covered x hx (fun w hw => by cases hw)
    simp at hγ
  | some w =>
    refine ⟨hs.feasible w rfl, fun x hx => ?_⟩
    by_contra hlt
    obtain ⟨γ, hγ, _⟩ := hs.covered x hx (fun v hv => by
      cases hv
      exact not_le.1 hlt)
    simp at hγ

lemma stack_nil_of_potential {P : Params} {s : SearchState P} (hs : Good P s)
    (h : potential P s.stack = 0) : s.stack = [] := by
  obtain ⟨stack, inc⟩ := s
  cases stack with
  | nil => rfl
  | cons β rest =>
    exfalso
    have := boxCard_pos (hs.nonempty β (by simp))
    change potential P (β :: rest) = 0 at h
    rw [potential_cons] at h
    omega

lemma run_good (P : Params) (O : Oracle (Box P) (Option (Point P)))
    (hO : IsRelaxationOracle P O) (seed : (lpBranchAndBound P).Seed) (ξ : (k : ℕ) → O.Seed k)
    (k : ℕ) :
    let F := fun sc : (lpBranchAndBound P).State × List ((Fin 1 × Box P) × Option (Point P)) =>
      let query := (lpBranchAndBound P).query sc.1
      let reply := O.answer sc.2 query (ξ sc.2.length)
      ((lpBranchAndBound P).update sc.1 reply, sc.2 ++ [(query, reply)])
    Good P (F^[k] ((lpBranchAndBound P).initial seed, [])).1 ∧
      ((F^[k] ((lpBranchAndBound P).initial seed, [])).1.stack = [] ∨
        potential P (F^[k] ((lpBranchAndBound P).initial seed, [])).1.stack + k ≤
          potential P (initialStack P)) := by
  intro F
  induction k with
  | zero => exact ⟨good_initial P, Or.inr (Nat.le_of_eq (Nat.add_zero _))⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set sc := F^[k] ((lpBranchAndBound P).initial seed, [])
    obtain ⟨hg, hk⟩ := ih
    have hr : SolvesRelaxation P (sc.1.stack.headD (P.lo, P.hi))
        (O.answer sc.2 ((lpBranchAndBound P).query sc.1) (ξ sc.2.length)) :=
      hO _ _ _
    change Good P (branchUpdate P sc.1 _) ∧ ((branchUpdate P sc.1 _).stack = [] ∨
      potential P (branchUpdate P sc.1 _).stack + (k + 1) ≤ potential P (initialStack P))
    by_cases hnil : sc.1.stack = []
    · rw [branchUpdate_nil P sc.1 _ hnil]
      exact ⟨hg, Or.inl hnil⟩
    · obtain ⟨hg', hp⟩ := good_update hg hr hnil
      refine ⟨hg', Or.inr ?_⟩
      rcases hk with hk | hk
      · exact absurd hk hnil
      · omega

lemma lpBranchAndBound_solves (P : Params) (O : Oracle (Box P) (Option (Point P)))
    (hO : IsRelaxationOracle P O) (seed : (lpBranchAndBound P).Seed) (ξ : (k : ℕ) → O.Seed k) :
    SolvesMixed P (execute O (lpBranchAndBound P)
      (fun _ => 2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1) seed ξ) := by
  rw [execute_indexed]
  obtain ⟨hg, hk⟩ := run_good P O hO seed ξ (2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1)
  refine solves_of_good hg ?_
  rcases hk with hk | hk
  · exact hk
  · have hpi := potential_initial P
    exact stack_nil_of_potential hg (by omega)

end OracleTemplate.BoundedMixedIntegerLinear
