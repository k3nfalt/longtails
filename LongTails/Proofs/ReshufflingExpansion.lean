import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.Sublists
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.Reshuffling

lemma sum_flatMap {I V : Type*} [AddMonoid V] (w : List I) (f : I → List V) :
    (w.flatMap f).sum = (w.map (fun i => (f i).sum)).sum := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

lemma ordered_product_expansion {I R : Type*} [Semiring R]
    (A : I → R) (w : List I) :
    (w.map (fun i => 1 + A i)).prod =
      (w.sublists'.map (fun v => (v.map A).prod)).sum := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.sublists'_cons, List.map_append,
      List.sum_append, List.map_map, Function.comp_def]
    simp only [List.sum_map_mul_left]
    rw [← ih]
    exact add_mul _ _ _ |>.trans (by rw [one_mul])

lemma ordered_product_scaled_expansion {I R : Type*} [Ring R] [Algebra ℝ R]
    (A : I → R) (z : ℝ) (w : List I) :
    (w.map (fun i => 1 + z • A i)).prod =
      (w.sublists'.map (fun v => z ^ v.length • (v.map A).prod)).sum := by
  rw [ordered_product_expansion]
  congr 1
  apply List.map_congr_left
  intro v hv
  clear hv
  induction v with
  | nil => simp
  | cons i v ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, pow_succ', mul_comm z]

lemma permutation_tuple_sum_eq {J I V : Type*} [Finite J] [Fintype I]
    [DecidableEq I] [AddCommMonoid V] (F : (J → I) → V)
    (f g : J → I) (hf : Function.Injective f) (hg : Function.Injective g) :
    (∑ π : Equiv.Perm I, F (fun j => π (f j))) =
      ∑ π : Equiv.Perm I, F (fun j => π (g j)) := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  calc
    _ = ∑ π : Equiv.Perm I, F (fun j => (π * σ) (f j)) :=
      (Equiv.sum_comp (Equiv.mulRight σ) (fun π => F (fun j => π (f j)))).symm
    _ = _ := by simp only [Equiv.Perm.mul_apply, hσ]

lemma permutation_embedding_average {J I V : Type*} [Fintype J] [Fintype I]
    [DecidableEq I] [AddCommMonoid V] (F : (J → I) → V) (f : J ↪ I) :
    Fintype.card (J ↪ I) • (∑ π : Equiv.Perm I, F (fun j => π (f j))) =
      Fintype.card (Equiv.Perm I) • ∑ g : J ↪ I, F g := by
  classical
  calc
    _ = ∑ g : J ↪ I, ∑ π : Equiv.Perm I, F (fun j => π (g j)) := by
      simp_rw [← permutation_tuple_sum_eq F f _ f.injective (Function.Embedding.injective _)]
      simp
    _ = ∑ π : Equiv.Perm I, ∑ g : J ↪ I, F (fun j => π (g j)) := Finset.sum_comm
    _ = ∑ _π : Equiv.Perm I, ∑ g : J ↪ I, F g := by
      apply Finset.sum_congr rfl
      intro π hπ
      exact (Equiv.embeddingCongr (Equiv.refl J) π).sum_comp (fun g => F g)
    _ = _ := by simp

lemma ordered_product_graded_expansion {I R : Type*} [Ring R] [Algebra ℝ R]
    (A : I → R) (z : ℝ) (w : List I) :
    (w.map (fun i => 1 + z • A i)).prod =
      ((List.range (w.length + 1)).map (fun m =>
        z ^ m • ((w.sublistsLen m).map (fun v => (v.map A).prod)).sum)).sum := by
  rw [ordered_product_scaled_expansion]
  have hp := (List.range_bind_sublistsLen_perm w).map
    (fun v => z ^ v.length • (v.map A).prod)
  rw [← hp.sum_eq, List.map_flatMap, sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro m hm
  rw [List.smul_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  simp only [List.length_of_sublistsLen hv, Function.comp_def]

lemma embedding_card_factorial_choose (m n : ℕ) :
    Fintype.card (Fin m ↪ Fin n) = m.factorial * n.choose m := by
  rw [Fintype.card_embedding_eq]
  simp only [Fintype.card_fin, Nat.descFactorial_eq_factorial_mul_choose]

lemma nodup_word_average {I V : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid V]
    (F : List I → V) (w : List I) (m : ℕ) (hw : w.Nodup) (hm : w.length = m) :
    Fintype.card (Fin m ↪ I) • (∑ π : Equiv.Perm I, F (w.map π)) =
      Fintype.card (Equiv.Perm I) • ∑ g : Fin m ↪ I, F (List.ofFn g) := by
  subst m
  let e : Fin w.length ↪ I := ⟨w.get, hw.injective_get⟩
  have h := permutation_embedding_average (fun g => F (List.ofFn g)) e
  have he : ∀ π : Equiv.Perm I, List.ofFn (fun j => π (e j)) = w.map π := by
    intro π
    change List.ofFn (fun j => π (w.get j)) = w.map π
    simpa only [List.map_ofFn, Function.comp_def] using congrArg (List.map π) (List.ofFn_get w)
  simpa only [he] using h

lemma sum_power_words {I R : Type*} [Fintype I] [Semiring R]
    (A : I → R) (m : ℕ) :
    (∑ i, A i) ^ m = ∑ f : Fin m → I, (List.ofFn (fun j => A (f j))).prod := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => I)).sum_comp
      (fun f => (List.ofFn (fun j => A (f j))).prod)]
    change (∑ i, A i) ^ (m + 1) =
      ∑ p : I × (Fin m → I),
        (List.ofFn (fun j => A (Fin.cons (α := fun _ : Fin (m + 1) => I) p.1 p.2 j))).prod
    simp only [Fintype.sum_prod_type, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
    simp only [← Finset.mul_sum, ← ih, ← Finset.sum_mul, pow_succ']

lemma injective_word_sum {I V : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid V]
    (m : ℕ) (F : (Fin m → I) → V) :
    (∑ f ∈ Finset.univ.filter Function.Injective, F f) = ∑ g : Fin m ↪ I, F g := by
  classical
  rw [Finset.sum_subtype (p := Function.Injective) _ (by simp)]
  let e : {f : Fin m → I // Function.Injective f} ≃ (Fin m ↪ I) :=
    { toFun := fun f => ⟨f.val, f.property⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma word_sum_partition {I V : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid V]
    (m : ℕ) (F : (Fin m → I) → V) :
    (∑ f, F f) = (∑ g : Fin m ↪ I, F g) +
      ∑ f ∈ Finset.univ.filter (fun f => ¬ Function.Injective f), F f := by
  classical
  rw [← injective_word_sum]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

lemma noninjective_relabel_sum {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (F : (Fin m → I) → ℝ) (π : Equiv.Perm I) :
    (∑ f : Fin m → I, if Function.Injective f then 0 else F (fun j => π (f j))) =
      ∑ f : Fin m → I, if Function.Injective f then 0 else F f := by
  classical
  apply Fintype.sum_equiv ((Equiv.refl (Fin m)).arrowCongr π)
  intro f
  change (if Function.Injective f then 0 else F (fun j => π (f j))) =
    if Function.Injective (fun j => π (f j)) then 0 else F (fun j => π (f j))
  have hi : Function.Injective (fun j => π (f j)) ↔ Function.Injective f := by
    constructor
    · intro h a b hab
      apply h
      exact congrArg π hab
    · intro h a b hab
      exact h (π.injective hab)
  simp only [hi]

end OracleTemplate.Reshuffling
