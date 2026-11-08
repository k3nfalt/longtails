import LongTails.Proofs.BirchCollectionEuclidean
import LongTails.Proofs.AdaptiveIID

namespace LongTails.Proofs.BirchResourceForest

open Finset MeasureTheory ProbabilityTheory OracleTemplate.BirchSgd
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchSgd (ReprContained DistanceBounded)

structure Forest where
  root : ℕ → ℕ
  head : ℕ → ℕ
  saved : ℕ → ℕ

def Earlier (root k v : ℕ) : Prop :=
  v = 2 * root ∨ ∃ j, root ≤ j ∧ j < k ∧ v = 2 * j + 1

def Forest.Valid (s : Forest) (B : ℕ) : Prop :=
  (∀ k, s.root k ≤ k ∧ k - s.root k < B) ∧
  (∀ i k, s.root k ≤ i → i ≤ k → s.root i = s.root k) ∧
  ∀ k, Earlier (s.root k) k (s.head k) ∧ Earlier (s.root k) k (s.saved k)

def tree (s : Forest) : Tree where
  base j := if j % 2 = 0 then s.head (j / 2) else j - 1
  point j := if j % 2 = 0 then s.saved (j / 2) else 0
  grad j := 2 * (j / 2)

def branch (k : ℕ) : ℕ := 2 * k

lemma earlier_le {r k v : ℕ} (hr : r ≤ k) (h : Earlier r k v) : v ≤ 2 * k := by
  rcases h with h | ⟨j, _, hj, h⟩ <;> omega

lemma tree_wellFormed (s : Forest) (B : ℕ) (hs : s.Valid B) : (tree s).WellFormed := by
  intro j
  have hk := (hs.1 (j / 2)).1
  have hb := earlier_le hk (hs.2.2 (j / 2)).1
  have hp := earlier_le hk (hs.2.2 (j / 2)).2
  dsimp only [tree]
  split <;> omega

lemma main_branch (s : Forest) : (tree s).IsMainBranch branch := by
  refine ⟨rfl, fun k => ⟨by unfold branch; omega, ?_⟩⟩
  dsimp only [branch, tree]
  split <;> omega

lemma aux_sample (s : Forest) (k : ℕ) : (tree s).auxSample branch k = 2 * k := by
  dsimp only [Tree.auxSample, branch, tree]
  omega

lemma aux_node (s : Forest) (k : ℕ) : (tree s).auxNode branch k = s.saved k := by
  unfold Tree.auxNode
  rw [aux_sample]
  dsimp only [tree]
  rw [ite_eq_left (by omega), show 2 * k / 2 = k by omega]

lemma private_base (s : Forest) (k : ℕ) : (tree s).base (2 * k) = s.head k := by
  dsimp only [tree]
  rw [ite_eq_left (by omega), show 2 * k / 2 = k by omega]

lemma global_repr_mono (s : Forest) (B : ℕ) (hs : s.Valid B) :
    Monotone (fun k => (tree s).repr (branch k)) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [branch_repr_succ _ (tree_wellFormed s B hs) _ (main_branch s)]
  exact Multiset.le_cons_self _ _

lemma private_repr (s : Forest) (B : ℕ) (hs : s.Valid B) (k : ℕ) :
    (tree s).repr (2 * k + 1) ≤ (tree s).repr (branch (k + 1)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [repr_succ _ _ (tree_wellFormed s B hs _).1, private_base,
      branch_repr_succ _ (tree_wellFormed s B hs) _ (main_branch s), aux_sample]
    have hg : (tree s).grad (2 * k) = 2 * k := by dsimp only [tree]; omega
    rw [hg]
    apply Multiset.cons_le_cons
    rcases (hs.2.2 k).1 with he | ⟨j, _, hj, he⟩
    · rw [he]
      exact global_repr_mono s B hs (hs.1 k).1
    · rw [he]
      exact (ih j hj).trans (global_repr_mono s B hs (by omega : j + 1 ≤ k))

lemma contained (s : Forest) (B : ℕ) (hs : s.Valid B) : ReprContained (tree s) branch := by
  intro k
  rw [aux_node]
  rcases (hs.2.2 k).2 with he | ⟨j, _, hj, he⟩
  · rw [he]
    exact global_repr_mono s B hs (hs.1 k).1
  · rw [he]
    exact (private_repr s B hs j).trans (global_repr_mono s B hs (by omega : j + 1 ≤ k))

lemma private_history (s : Forest) (B : ℕ) (hs : s.Valid B) (k : ℕ) :
    (tree s).depth (2 * k + 1) ≤ k + 1 ∧
      branch (s.root k) ∈ (tree s).ancestors (2 * k + 1) := by
  have hT := tree_wellFormed s B hs
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [depth_succ _ _ (hT _).1, ancestors_succ _ _ (hT _).1, private_base]
    rcases (hs.2.2 k).1 with he | ⟨j, hr, hj, he⟩
    · rw [he, show 2 * s.root k = branch (s.root k) from rfl,
        branch_depth _ hT _ (main_branch s)]
      refine ⟨Nat.add_le_add_right (hs.1 k).1 1, mem_insert_of_mem ?_⟩
      rw [branch_ancestors _ hT _ (main_branch s)]
      exact mem_image_of_mem _ (mem_range.mpr (Nat.lt_succ_self _))
    · rw [he]
      have h := ih j hj
      refine ⟨by omega, mem_insert_of_mem ?_⟩
      rw [← hs.2.1 j k hr hj.le]
      exact h.2

lemma distance (s : Forest) (B : ℕ) (hs : s.Valid B) :
    DistanceBounded (tree s) branch (B - 1 : ℕ) := by
  intro k
  rw [aux_node]
  let T := tree s
  have hT := tree_wellFormed s B hs
  have hk := (hs.1 k).1
  have ha : branch (s.root k) ∈ T.ancestors (branch k) := by
    rw [branch_ancestors _ hT _ (main_branch s)]
    exact mem_image_of_mem _ (mem_range.mpr (Nat.lt_succ_of_le hk))
  have hz : T.depth (s.saved k) ≤ k ∧ branch (s.root k) ∈ T.ancestors (s.saved k) := by
    rcases (hs.2.2 k).2 with he | ⟨j, hr, hj, he⟩
    · rw [he, show 2 * s.root k = branch (s.root k) from rfl,
        branch_depth _ hT _ (main_branch s), branch_ancestors _ hT _ (main_branch s)]
      exact ⟨hk, mem_image_of_mem _ (mem_range.mpr (Nat.lt_succ_self _))⟩
    · rw [he, ← hs.2.1 j k hr hj.le]
      exact ⟨(private_history s B hs j).1.trans (by omega), (private_history s B hs j).2⟩
  have hc : s.root k ≤ ((T.ancestors (branch k) ∩ T.ancestors (s.saved k)).sup T.depth) := by
    rw [← branch_depth _ hT _ (main_branch s) (s.root k)]
    exact le_sup (f := T.depth) (mem_inter.mpr ⟨ha, hz.2⟩)
  apply Nat.cast_le.mpr
  unfold Tree.dist
  rw [branch_depth _ hT _ (main_branch s)]
  let a := (T.ancestors (branch k) ∩ T.ancestors (s.saved k)).sup T.depth
  change max (k - a) (T.depth (s.saved k) - a) ≤ B - 1
  have hca : s.root k ≤ a := hc
  have hza := hz.1
  have hb := (hs.1 k).2
  exact max_le (by omega) (by omega)

lemma realize_prefix {d : ℕ} {Ω : Type} (T : Tree) (γ : ℝ) (x₀ : Point d)
    (g : Point d → Ω → Point d) (ξ ζ : ℕ → Ω) (k : ℕ)
    (h : ∀ j < k, ξ j = ζ j) : T.realize γ x₀ g ξ k = T.realize γ x₀ g ζ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Tree.realize, Tree.realize, ih (fun j hj => h j (by omega)), h k (by omega)]

lemma iid_independent {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (s : Forest) (B : ℕ) (hs : s.Valid B)
    (γ : ℝ) (x₀ : Point d) (g : Point d → Ω → Point d) (hg : Measurable (Function.uncurry g))
    (μ : ProbabilityMeasure Ω) (P : Measure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) P) :
    LongTails.Setups.BirchSgd.SampleIndependent (tree s) branch γ x₀ g P := by
  classical
  intro k
  let T := tree s
  let z₀ := Classical.choice (nonempty_of_isProbabilityMeasure (μ : Measure Ω))
  let pre := fun (ξ : ℕ → Ω) (i : Fin (2 * k)) => ξ i.val
  let extend := fun (x : Fin (2 * k) → Ω) (j : ℕ) => if hj : j < 2 * k then x ⟨j, hj⟩ else z₀
  have he : Measurable extend := by
    apply Measurable.of_eval
    intro j
    by_cases h : j < 2 * k
    · simpa only [extend, dite_eq_left h] using
        (measurable_pi_apply (⟨j, h⟩ : Fin (2 * k)))
    · simp only [extend, dite_eq_right h]
      exact measurable_const
  let past := fun (ξ : ℕ → Ω) (i : Fin k) =>
    (T.vertex γ x₀ g ξ (branch (i.val + 1)), T.vertex γ x₀ g ξ (T.auxNode branch (i.val + 1)),
      ξ (T.auxSample branch i.val))
  have hm : Measurable past := past_measurable _ _ _ _ _ hg _
  have hpre (ξ : ℕ → Ω) : past ξ = past (extend (pre ξ)) := by
    funext i
    have hib := i.isLt
    have hsame (j : ℕ) (hj : j < 2 * k) : ξ j = extend (pre ξ) j := by
      simp only [extend, dite_eq_left hj, pre]
    have hv (j : ℕ) (hj : j ≤ 2 * k) :
        T.vertex γ x₀ g ξ j = T.vertex γ x₀ g (extend (pre ξ)) j := by
      unfold Tree.vertex
      rw [realize_prefix T γ x₀ g ξ (extend (pre ξ)) j (fun l hl => hsame l (hl.trans_le hj))]
    have hz : T.auxNode branch (i.val + 1) ≤ 2 * k := by
      dsimp only [T]
      rw [aux_node]
      exact (earlier_le (hs.1 _).1 (hs.2.2 _).2).trans (by omega)
    dsimp only [past]
    rw [hv _ (by unfold branch; omega), hv _ hz]
    have hj : T.auxSample branch i.val < 2 * k := by
      dsimp only [T]
      rw [aux_sample]
      omega
    rw [hsame _ hj]
  have hin := hiid.prefix_tail_independent (2 * k)
  have hh := hin.symm.comp (measurable_pi_apply 0) (hm.comp he)
  change IndepFun (fun ξ => ξ (T.auxSample branch k)) past P
  have hf : (past ∘ extend) ∘ pre = past := funext (fun ξ => (hpre ξ).symm)
  change IndepFun (fun ξ : ℕ → Ω => ξ (2 * k + 0)) ((past ∘ extend) ∘ pre) P at hh
  rw [hf, Nat.add_zero] at hh
  dsimp only [T]
  rw [aux_sample]
  exact hh

end LongTails.Proofs.BirchResourceForest
