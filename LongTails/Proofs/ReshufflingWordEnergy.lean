import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Reshuffling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma endpoint_energy (A B C : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) {M : ℝ} (hM : 0 ≤ M)
    (hB : ‖B‖ ≤ M) (x : E) :
    |⟪x, A (B (C x))⟫| ≤ M / 2 * (‖A x‖ ^ 2 + ‖C x‖ ^ 2) := by
  have hs : ⟪A x, B (C x)⟫ = ⟪x, A (B (C x))⟫ := hA x (B (C x))
  rw [← hs]
  have hb : ‖B (C x)‖ ≤ M * ‖C x‖ :=
    (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  calc
    _ ≤ ‖A x‖ * ‖B (C x)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖A x‖ * (M * ‖C x‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ _ := by nlinarith [mul_nonneg hM (sq_nonneg (‖A x‖ - ‖C x‖))]

lemma weighted_endpoint_energy {W : Type*} (s : Finset W)
    (a : W → ℝ) (A B C : W → E →L[ℝ] E) {M : ℝ}
    (hM : 0 ≤ M) (ha : ∀ w ∈ s, 0 ≤ a w)
    (hA : ∀ w ∈ s, (A w).toLinearMap.IsSymmetric)
    (hB : ∀ w ∈ s, ‖B w‖ ≤ M) (x : E) :
    |∑ w ∈ s, a w * ⟪x, A w (B w (C w x))⟫| ≤
      M / 2 * ((∑ w ∈ s, a w * ‖A w x‖ ^ 2) +
        ∑ w ∈ s, a w * ‖C w x‖ ^ 2) := by
  calc
    _ ≤ ∑ w ∈ s, |a w * ⟪x, A w (B w (C w x))⟫| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ s, a w * (M / 2 * (‖A w x‖ ^ 2 + ‖C w x‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro w hw
      rw [abs_mul, abs_of_nonneg (ha w hw)]
      exact mul_le_mul_of_nonneg_left
        (endpoint_energy (A w) (B w) (C w) (hA w hw) hM (hB w hw) x) (ha w hw)
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring

lemma endpoint_energy_of_marginals {W I : Type*} [Fintype I]
    (s : Finset W) (a : W → ℝ) (A : I → E →L[ℝ] E)
    (B : W → E →L[ℝ] E) (left right : W → I) {M mass : ℝ}
    (hM : 0 ≤ M) (ha : ∀ w ∈ s, 0 ≤ a w)
    (hA : ∀ i, (A i).toLinearMap.IsSymmetric)
    (hB : ∀ w ∈ s, ‖B w‖ ≤ M) (x : E)
    (hl : ∑ w ∈ s, a w * ‖A (left w) x‖ ^ 2 = mass * ∑ i, ‖A i x‖ ^ 2)
    (hr : ∑ w ∈ s, a w * ‖A (right w) x‖ ^ 2 = mass * ∑ i, ‖A i x‖ ^ 2) :
    |∑ w ∈ s, a w * ⟪x, A (left w) (B w (A (right w) x))⟫| ≤
      M * mass * ∑ i, ‖A i x‖ ^ 2 := by
  have h := weighted_endpoint_energy s a (fun w => A (left w)) B
    (fun w => A (right w)) hM ha (fun w _ => hA (left w)) hB x
  rw [hl, hr] at h
  convert h using 1; ring

lemma permutation_marginal_eq {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid V] (f : I → V) (i j : I) :
    (∑ π : Equiv.Perm I, f (π i)) = ∑ π : Equiv.Perm I, f (π j) := by
  classical
  apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  simp [Equiv.Perm.mul_apply]

lemma permutation_marginal_sum {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℝ) (i : I) :
    (Fintype.card I : ℝ) * (∑ π : Equiv.Perm I, f (π i)) =
      (Fintype.card (Equiv.Perm I) : ℝ) * ∑ j, f j := by
  classical
  calc
    _ = ∑ j : I, ∑ π : Equiv.Perm I, f (π j) := by
      simp_rw [← permutation_marginal_eq f i]
      simp
    _ = ∑ π : Equiv.Perm I, ∑ j : I, f (π j) := Finset.sum_comm
    _ = _ := by simp_rw [Equiv.sum_comp]; simp

lemma norm_word_le {I : Type*} (A : I → E →L[ℝ] E) {L : ℝ}
    (hL : 0 ≤ L) (hA : ∀ i, ‖A i‖ ≤ L) (w : List I) :
    ‖(w.map A).prod‖ ≤ L ^ w.length := by
  induction w with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    exact (norm_mul_le _ _).trans ((mul_le_mul (hA i) ih (norm_nonneg _) hL).trans_eq
      (mul_comm _ _))

lemma permutation_word_energy {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (left right : I) (w : List I) (x : E) :
    (Fintype.card I : ℝ) *
        |∑ π : Equiv.Perm I, ⟪x, A (π left) ((w.map (fun i => A (π i))).prod (A (π right) x))⟫| ≤
      (Fintype.card (Equiv.Perm I) : ℝ) * L ^ w.length * ∑ i, ‖A i x‖ ^ 2 := by
  classical
  have h := weighted_endpoint_energy Finset.univ (fun _ : Equiv.Perm I => (1 : ℝ))
    (fun π => A (π left)) (fun π => (w.map (fun i => A (π i))).prod)
    (fun π => A (π right)) (pow_nonneg hL _) (by intros; norm_num)
    (fun π _ => hs _) (fun π _ => norm_word_le _ hL (fun i => hA _) w) x
  simp only [one_mul] at h
  have hn := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ _)
  have hl := permutation_marginal_sum (fun i => ‖A i x‖ ^ 2) left
  have hr := permutation_marginal_sum (fun i => ‖A i x‖ ^ 2) right
  calc
    _ ≤ _ := hn
    _ = L ^ w.length / 2 *
        ((Fintype.card I : ℝ) * (∑ π : Equiv.Perm I, ‖A (π left) x‖ ^ 2) +
        (Fintype.card I : ℝ) * (∑ π : Equiv.Perm I, ‖A (π right) x‖ ^ 2)) := by ring
    _ = _ := by rw [hl, hr]; ring

lemma permutation_full_word_energy {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (w : List I) (hw : 2 ≤ w.length) (x : E) :
    (Fintype.card I : ℝ) *
        |∑ π : Equiv.Perm I, ⟪x, (w.map (fun i => A (π i))).prod x⟫| ≤
      (Fintype.card (Equiv.Perm I) : ℝ) * L ^ (w.length - 2) * ∑ i, ‖A i x‖ ^ 2 := by
  induction w using List.reverseRecOn with
  | nil => simp at hw
  | append_singleton w b ih =>
    cases w with
    | nil => simp at hw
    | cons a mid =>
      simpa only [List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, mul_apply_eq_comp, List.length_append,
        List.length_cons, List.length_nil, Nat.add_zero,
        show mid.length + 1 + (0 + 1) - 2 = mid.length by omega] using
          permutation_word_energy A hL hs hA a b mid x

lemma reverse_word_inner {I : Type*} (A : I → E →L[ℝ] E)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (w : List I) (x y : E) :
    ⟪x, (w.map A).prod y⟫ = ⟪(w.reverse.map A).prod x, y⟫ := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, List.reverse_cons,
      List.map_append, List.prod_append, List.map_nil, List.prod_nil, mul_one]
    have he : ⟪A a x, (w.map A).prod y⟫ = ⟪x, A a ((w.map A).prod y)⟫ := hs a x _
    rw [← he, ih]

lemma palindrome_energy {I : Type*} (A : I → E →L[ℝ] E)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (w : List I) (x : E) :
    ⟪x, ((w ++ w.reverse).map A).prod x⟫ = ‖(w.reverse.map A).prod x‖ ^ 2 := by
  rw [List.map_append, List.prod_append, mul_apply_eq_comp, reverse_word_inner A hs,
    real_inner_self_eq_norm_sq]

lemma permutation_family_energy {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (family : List (List I)) (m : ℕ) (hm : 2 ≤ m)
    (hw : ∀ w ∈ family, w.length = m) (x : E) :
    (Fintype.card I : ℝ) *
        |(family.map (fun w => ∑ π : Equiv.Perm I, ⟪x, (w.map (fun i => A (π i))).prod x⟫)).sum| ≤
      family.length * (Fintype.card (Equiv.Perm I) : ℝ) * L ^ (m - 2) * ∑ i, ‖A i x‖ ^ 2 := by
  induction family with
  | nil => simp
  | cons w family ih =>
    have hlen := hw w (by simp)
    have hhead := permutation_full_word_energy A hL hs hA w (by omega) x
    rw [hlen] at hhead
    have htail := ih (fun v hv => hw v (List.mem_cons_of_mem w hv))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ha := mul_le_mul_of_nonneg_left (abs_add_le
      (∑ π : Equiv.Perm I, ⟪x, (w.map (fun i => A (π i))).prod x⟫)
      (family.map (fun v => ∑ π : Equiv.Perm I, ⟪x, (v.map (fun i => A (π i))).prod x⟫)).sum)
      (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ _)
    nlinarith

end OracleTemplate.Reshuffling
