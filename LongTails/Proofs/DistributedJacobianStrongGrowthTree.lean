import LongTails.Algorithms.DistributedLocalExtragradientTree
import Mathlib.Tactic

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTree

open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Setups.DistributedJacobianStrongGrowth

lemma child_depth (p : Params) (hp : valid p) (u v : Fin p.n) (hu : u ∈ children p v) :
    p.depth v + 1 = p.depth u := by
  have hh : u ≠ p.root ∧ p.parent u = v := (Finset.mem_filter.mp hu).2
  simpa only [hh.2] using hp.2.2.2.1 u hh.1

lemma ancestor_root (p : Params) (hp : valid p) (k : ℕ) (v : Fin p.n)
    (hdepth : p.depth v ≤ k) : ancestor p k v = p.root := by
  induction k generalizing v with
  | zero =>
      change v = p.root
      by_contra hv
      have hh := hp.2.2.2.1 v hv
      omega
  | succ k ih =>
      change ancestor p k (p.parent v) = p.root
      apply ih
      by_cases hv : v = p.root
      · rw [hv, hp.2.1, hp.2.2.1]
        exact Nat.zero_le _
      · have hh := hp.2.2.2.1 v hv
        omega

lemma parent_ancestor (p : Params) (k : ℕ) (v : Fin p.n) :
    p.parent (ancestor p k v) = ancestor p k (p.parent v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => exact ih (p.parent v)

lemma ancestor_depth (p : Params) (hp : valid p) (k : ℕ) (v : Fin p.n)
    (hk : k ≤ p.depth v) : p.depth (ancestor p k v) + k = p.depth v := by
  induction k generalizing v with
  | zero => simp [ancestor]
  | succ k ih =>
      have hv : v ≠ p.root := by intro he; rw [he, hp.2.2.1] at hk; omega
      have hd := hp.2.2.2.1 v hv
      have hh := ih (p.parent v) (by omega)
      change p.depth (ancestor p k (p.parent v)) + (k + 1) = p.depth v
      omega

lemma descendant_root (p : Params) (hp : valid p) (u : Fin p.n) : Descendant p p.root u := by
  exact ⟨p.depth u, ancestor_root p hp _ _ le_rfl, by rw [hp.2.2.1]; omega⟩

lemma descendant_split (p : Params) (hp : valid p) (v u : Fin p.n) :
    Descendant p v u ↔ u = v ∨ ∃ c ∈ children p v, Descendant p c u := by
  constructor
  · rintro ⟨k, ha, hd⟩
    cases k with
    | zero => exact Or.inl ha
    | succ k =>
        let c := ancestor p k u
        have hdc := ancestor_depth p hp k u (by omega)
        have hparent : p.parent c = v := by
          rw [parent_ancestor]
          exact ha
        have hc : c ≠ p.root := by
          intro he
          change p.depth c + k = p.depth u at hdc
          rw [he, hp.2.2.1] at hdc
          omega
        exact Or.inr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hparent⟩, k, rfl, hdc⟩
  · rintro (he | ⟨c, hc, k, ha, hd⟩)
    · subst u
      exact ⟨0, rfl, by omega⟩
    · have hchild := (Finset.mem_filter.mp hc).2
      have hdepth := child_depth p hp c v hc
      refine ⟨k + 1, ?_, by omega⟩
      change ancestor p k (p.parent u) = v
      rw [← parent_ancestor, ha, hchild.2]

lemma child_descendants_disjoint (p : Params) (hp : valid p) (v a b u : Fin p.n)
    (ha : a ∈ children p v) (hb : b ∈ children p v)
    (hau : Descendant p a u) (hbu : Descendant p b u) : a = b := by
  obtain ⟨ka, hea, hda⟩ := hau
  obtain ⟨kb, heb, hdb⟩ := hbu
  have hdepA := child_depth p hp a v ha
  have hdepB := child_depth p hp b v hb
  have he : ka = kb := by omega
  rw [he] at hea
  exact hea.symm.trans heb

lemma subtree_root (p : Params) (hp : valid p) : subtree p p.root = Finset.univ := by
  classical
  ext u
  simp only [subtree, Finset.mem_filter, Finset.mem_univ, true_and]
  exact iff_true_intro (descendant_root p hp u)

lemma subtree_split (p : Params) (hp : valid p) (v : Fin p.n) :
    subtree p v = insert v ((children p v).biUnion (subtree p)) := by
  classical
  ext u
  simp only [subtree, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_biUnion]
  exact descendant_split p hp v u

lemma self_not_child_subtree (p : Params) (hp : valid p) (v : Fin p.n) :
    v ∉ (children p v).biUnion (subtree p) := by
  classical
  intro hv
  obtain ⟨c, hc, hcv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨k, _, hd⟩ := (Finset.mem_filter.mp hcv).2
  have hh := child_depth p hp c v hc
  omega

lemma subtree_sum (p : Params) (hp : valid p) (v : Fin p.n) (values : Fin p.n → ℕ) :
    ∑ u ∈ subtree p v, values u =
      values v + ∑ c ∈ children p v, ∑ u ∈ subtree p c, values u := by
  classical
  rw [subtree_split p hp v, Finset.sum_insert (self_not_child_subtree p hp v)]
  congr 1
  apply Finset.sum_biUnion
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro u hau hbu
  exact hab (child_descendants_disjoint p hp v a b u ha hb
    (Finset.mem_filter.mp hau).2 (Finset.mem_filter.mp hbu).2)

lemma subtree_sum_le (p : Params) (v : Fin p.n) (values : Fin p.n → ℕ) (B : ℕ)
    (hvalues : ∀ u, values u ≤ B) : (∑ u ∈ subtree p v, values u) ≤ (p.n : ℕ) * B := by
  classical
  calc
    _ ≤ ∑ u : Fin p.n, values u := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ _ : Fin p.n, B := Finset.sum_le_sum fun u _ => hvalues u
    _ = _ := by simp

lemma accept_preserves {n d : ℕ} (allowed : Finset (Fin n)) (state : Collector n d)
    (own : Fin d → ℕ) (payloads : Fin n → Fin d → ℕ)
    (hseen : state.seen ⊆ allowed)
    (htotal : ∀ j, state.total j = own j + ∑ u ∈ state.seen, payloads u j)
    (sender : Fin n) :
    (accept allowed state sender (payloads sender)).seen ⊆ allowed ∧
      ∀ j, (accept allowed state sender (payloads sender)).total j =
        own j + ∑ u ∈ (accept allowed state sender (payloads sender)).seen, payloads u j := by
  classical
  unfold accept
  split_ifs with h
  · constructor
    · exact Finset.insert_subset h.1 hseen
    · intro j
      simp only [Finset.sum_insert h.2, htotal]
      omega
  · exact ⟨hseen, htotal⟩

lemma accept_duplicate {n d : ℕ} (allowed : Finset (Fin n)) (state : Collector n d)
    (sender : Fin n) (payload : Fin d → ℕ) (hseen : sender ∈ state.seen) :
    accept allowed state sender payload = state := by
  simp [accept, hseen]

lemma collector_complete {n d : ℕ} (allowed : Finset (Fin n)) (state : Collector n d)
    (own : Fin d → ℕ) (payloads : Fin n → Fin d → ℕ)
    (hseen : state.seen ⊆ allowed) (hready : allowed ⊆ state.seen)
    (htotal : ∀ j, state.total j = own j + ∑ u ∈ state.seen, payloads u j) :
    ∀ j, state.total j = own j + ∑ u ∈ allowed, payloads u j := by
  have he := Finset.Subset.antisymm hseen hready
  simpa only [he] using htotal

end LongTails.Proofs.DistributedJacobianStrongGrowthTree
