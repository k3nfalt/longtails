import LongTails.Algorithms.BestBoundBranchAndBound
import LongTails.Proofs.LpBranchAndBound

namespace OracleTemplate.HiddenMixedIntegerLinear

open LongTails.Setups LongTails.Setups.HiddenMixedIntegerLinear Matrix
open OracleTemplate.BoundedMixedIntegerLinear
  (Good MemBox boxCard potential BoxNonempty Improves leftChild rightChild SearchState
    boxCard_pos boxCard_split potential_cons relaxation_of_mixed floor_add_one_le
    cast_floor_of_fract solves_of_good)
open LongTails.Setups.BoundedMixedIntegerLinear
  (objective toPoint MixedFeasible RelaxationFeasible RowFeasible InBox SolvesRelaxation
    IsRelaxationOracle SolvesMixed)

instance (Q : Public) : Std.Total (KeyLE Q) := ⟨fun a b => le_total a.2 b.2⟩

instance (Q : Public) : IsTrans (Entry Q) (KeyLE Q) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩

def KeyBelow (P : Params) (k : WithBot ℝ) : Prop :=
  ∀ x, MixedFeasible (data P) x → k ≤ (objective (data P) (toPoint (data P) x) : WithBot ℝ)

def slack (P : Params) (β : Box P.toPublic) (z : Fin P.p → ℤ) : ℕ :=
  (Finset.univ.filter fun k => β.1 k < z k).card + (Finset.univ.filter fun k => z k < β.2 k).card

noncomputable def weight (P : Params) (β : Box P.toPublic) : ℕ :=
  open Classical in ∑ z ∈ (goodPoints P).filter (MemBox (data P) β), slack P β z

noncomputable def entryCost (P : Params) (e : Entry P.toPublic) : ℕ :=
  open Classical in (if KeyBelow P e.2 then 1 else 0) + 2 * weight P e.1

noncomputable def gapPotential (P : Params) (l : List (Entry P.toPublic)) : ℕ :=
  (l.map (entryCost P)).sum

def boxPotential (P : Params) (l : List (Entry P.toPublic)) : ℕ :=
  potential (data P) (l.map Prod.fst)

structure Inv (P : Params) (s : BestBoundState P.toPublic) : Prop where
  good : Good (data P) ⟨s.nodes.map Prod.fst, s.incumbent⟩
  sorted : s.nodes.Pairwise (KeyLE P.toPublic)
  key : ∀ e ∈ s.nodes, ∀ x, RelaxationFeasible (data P) e.1 x →
    e.2 ≤ (objective (data P) x : WithBot ℝ)
  clean : ∀ e ∈ s.nodes, ∀ w, s.incumbent = some w →
    e.2 < (objective (data P) (toPoint (data P) w) : WithBot ℝ)

lemma lagrangian_le_objective {P : Params} (hlam : ∀ i, 0 ≤ P.lam i)
    (hd : P.d + P.lam ᵥ* P.G = 0) {x : (Fin P.p → ℝ) × (Fin P.q → ℝ)}
    (hx : RowFeasible (data P) x) : lagrangian P x.1 ≤ objective (data P) x := by
  have hrow : P.lam ⬝ᵥ (P.A *ᵥ x.1 + P.G *ᵥ x.2) ≤ P.lam ⬝ᵥ P.b := by
    unfold dotProduct
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hlam i)
  have hdx : P.d ⬝ᵥ x.2 = -(P.lam ⬝ᵥ (P.G *ᵥ x.2)) := by
    have : P.d = -(P.lam ᵥ* P.G) := eq_neg_of_add_eq_zero_left hd
    rw [this, neg_dotProduct, dotProduct_mulVec]
  rw [dotProduct_add] at hrow
  unfold lagrangian
  change (P.c + P.lam ᵥ* P.A) ⬝ᵥ x.1 - P.lam ⬝ᵥ P.b ≤ P.c ⬝ᵥ x.1 + P.d ⬝ᵥ x.2
  rw [hdx, add_dotProduct, ← dotProduct_mulVec]
  linarith

noncomputable def roundDown (P : Params) (z : Fin P.p → ℝ) : Fin P.p → ℤ := fun k =>
  if 0 ≤ (P.c + P.lam ᵥ* P.A) k then ⌊z k⌋ else ⌈z k⌉

lemma lagrangian_roundDown (P : Params) (z : Fin P.p → ℝ) :
    lagrangian P (fun k => (roundDown P z k : ℝ)) ≤ lagrangian P z := by
  unfold lagrangian
  apply sub_le_sub_right
  unfold dotProduct
  refine Finset.sum_le_sum fun k _ => ?_
  unfold roundDown
  dsimp only
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (Int.floor_le _) h
  · exact mul_le_mul_of_nonpos_left (Int.le_ceil _) (le_of_lt (not_le.1 h))

lemma roundDown_mem {P : Params} {β : Box P.toPublic} {z : Fin P.p → ℝ}
    (hz : ∀ k, (β.1 k : ℝ) ≤ z k ∧ z k ≤ β.2 k) : MemBox (data P) β (roundDown P z) := by
  intro k
  unfold roundDown
  have h1 := (hz k).1
  have h2 := (hz k).2
  dsimp only
  split_ifs
  · exact ⟨Int.le_floor.2 h1, by exact_mod_cast (Int.floor_le _).trans h2⟩
  · exact ⟨by exact_mod_cast h1.trans (Int.le_ceil _), Int.ceil_le.2 h2⟩

lemma roundDown_frac {P : Params} (z : Fin P.p → ℝ) {j : Fin P.p} (hj : Int.fract (z j) ≠ 0) :
    roundDown P z j = ⌊z j⌋ ∨ roundDown P z j = ⌊z j⌋ + 1 := by
  unfold roundDown
  split_ifs
  · exact Or.inl rfl
  · right
    rw [Int.ceil_eq_iff]
    have hlt : (⌊z j⌋ : ℝ) < z j := by
      rcases (Int.floor_le (z j)).lt_or_eq with h | h
      · exact h
      · exact absurd (show Int.fract (z j) = 0 by rw [Int.fract]; linarith) hj
    push_cast
    constructor
    · linarith
    · exact (Int.lt_floor_add_one _).le

lemma slack_le_root (P : Params) (z : Fin P.p → ℤ) : slack P (P.lo, P.hi) z ≤ 2 * P.p := by
  unfold slack
  have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin P.p)) fun k => P.lo k < z k
  have h2 := Finset.card_filter_le (Finset.univ : Finset (Fin P.p)) fun k => z k < P.hi k
  simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
  simp only at h1 h2 ⊢
  omega

lemma slack_left_le (P : Params) (β : Box P.toPublic) (j : Fin P.p) (t : ℤ) (z : Fin P.p → ℤ)
    (ht : t ≤ β.2 j) : slack P (leftChild (data P) β j t) z ≤ slack P β z := by
  unfold slack leftChild
  simp only
  apply Nat.add_le_add_left
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  by_cases hkj : k = j
  · subst hkj; rw [Function.update_self] at hk; omega
  · rwa [Function.update_of_ne hkj] at hk

lemma slack_left_lt (P : Params) (β : Box P.toPublic) (j : Fin P.p) (t : ℤ) (z : Fin P.p → ℤ)
    (ht : t + 1 ≤ β.2 j) (hz : z j = t) :
    slack P (leftChild (data P) β j t) z + 1 ≤ slack P β z := by
  unfold slack leftChild
  simp only
  rw [add_assoc]
  apply Nat.add_le_add_left
  apply Finset.card_lt_card
  refine ⟨fun k hk => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    by_cases hkj : k = j
    · subst hkj; rw [Function.update_self] at hk; omega
    · rwa [Function.update_of_ne hkj] at hk
  · have := h (show j ∈ Finset.univ.filter fun k => z k < β.2 k by simp; omega)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_self] at this
    omega

lemma slack_right_le (P : Params) (β : Box P.toPublic) (j : Fin P.p) (t : ℤ) (z : Fin P.p → ℤ)
    (ht : β.1 j ≤ t) : slack P (rightChild (data P) β j t) z ≤ slack P β z := by
  unfold slack rightChild
  simp only
  apply Nat.add_le_add_right
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  by_cases hkj : k = j
  · subst hkj; rw [Function.update_self] at hk; omega
  · rwa [Function.update_of_ne hkj] at hk

lemma slack_right_lt (P : Params) (β : Box P.toPublic) (j : Fin P.p) (t : ℤ) (z : Fin P.p → ℤ)
    (ht : β.1 j ≤ t) (hz : z j = t + 1) :
    slack P (rightChild (data P) β j t) z + 1 ≤ slack P β z := by
  unfold slack rightChild
  simp only
  rw [add_right_comm]
  apply Nat.add_le_add_right
  apply Finset.card_lt_card
  refine ⟨fun k hk => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    by_cases hkj : k = j
    · subst hkj; rw [Function.update_self] at hk; omega
    · rwa [Function.update_of_ne hkj] at hk
  · have := h (show j ∈ Finset.univ.filter fun k => β.1 k < z k by simp; omega)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_self] at this
    omega

lemma memBox_leftChild {P : Params} {β : Box P.toPublic} {j : Fin P.p} {t : ℤ}
    {z : Fin P.p → ℤ} (h : MemBox (data P) β z) (hj : z j ≤ t) :
    MemBox (data P) (leftChild (data P) β j t) z := by
  intro k
  by_cases hkj : k = j
  · subst hkj; simp [leftChild, hj, (h k).1]
  · simpa [leftChild, Function.update_of_ne hkj] using h k

lemma memBox_rightChild {P : Params} {β : Box P.toPublic} {j : Fin P.p} {t : ℤ}
    {z : Fin P.p → ℤ} (h : MemBox (data P) β z) (hj : t + 1 ≤ z j) :
    MemBox (data P) (rightChild (data P) β j t) z := by
  intro k
  by_cases hkj : k = j
  · subst hkj; simp only [rightChild, Function.update_self]; exact ⟨hj, (h k).2⟩
  · simpa [rightChild, Function.update_of_ne hkj] using h k

lemma memBox_of_leftChild {P : Params} {β : Box P.toPublic} {j : Fin P.p} {t : ℤ}
    {z : Fin P.p → ℤ} (h : MemBox (data P) (leftChild (data P) β j t) z) (ht : t ≤ β.2 j) :
    MemBox (data P) β z ∧ z j ≤ t := by
  refine ⟨fun k => ?_, ?_⟩
  · have hk := h k
    by_cases hkj : k = j
    · subst hkj
      simp only [leftChild, Function.update_self] at hk
      exact ⟨hk.1, hk.2.trans ht⟩
    · simpa [leftChild, Function.update_of_ne hkj] using hk
  · simpa [leftChild] using (h j).2

lemma memBox_of_rightChild {P : Params} {β : Box P.toPublic} {j : Fin P.p} {t : ℤ}
    {z : Fin P.p → ℤ} (h : MemBox (data P) (rightChild (data P) β j t) z) (ht : β.1 j ≤ t) :
    MemBox (data P) β z ∧ t + 1 ≤ z j := by
  refine ⟨fun k => ?_, ?_⟩
  · have hk := h k
    by_cases hkj : k = j
    · subst hkj
      simp only [rightChild, Function.update_self] at hk
      exact ⟨by omega, hk.2⟩
    · simpa [rightChild, Function.update_of_ne hkj] using hk
  · simpa [rightChild] using (h j).1

lemma weight_split (P : Params) (β : Box P.toPublic) (j : Fin P.p) (t : ℤ)
    (h1 : β.1 j ≤ t) (h2 : t + 1 ≤ β.2 j) :
    weight P (leftChild (data P) β j t) + weight P (rightChild (data P) β j t) ≤ weight P β := by
  classical
  unfold weight
  set G := goodPoints P
  have hL : ∑ z ∈ G.filter (MemBox (data P) (leftChild (data P) β j t)),
      slack P (leftChild (data P) β j t) z ≤
      ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ z j ≤ t), slack P β z := by
    rw [show G.filter (MemBox (data P) (leftChild (data P) β j t)) =
        G.filter (fun z => MemBox (data P) β z ∧ z j ≤ t) from
      Finset.filter_congr fun z _ => ⟨fun h => memBox_of_leftChild h (by omega),
        fun h => memBox_leftChild h.1 h.2⟩]
    exact Finset.sum_le_sum fun z _ => slack_left_le P β j t z (by omega)
  have hR : ∑ z ∈ G.filter (MemBox (data P) (rightChild (data P) β j t)),
      slack P (rightChild (data P) β j t) z ≤
      ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ ¬ z j ≤ t), slack P β z := by
    rw [show G.filter (MemBox (data P) (rightChild (data P) β j t)) =
        G.filter (fun z => MemBox (data P) β z ∧ ¬ z j ≤ t) from
      Finset.filter_congr fun z _ => ⟨fun h => ⟨(memBox_of_rightChild h h1).1,
        by have := (memBox_of_rightChild h h1).2; omega⟩,
        fun h => memBox_rightChild h.1 (by omega)⟩]
    exact Finset.sum_le_sum fun z _ => slack_right_le P β j t z h1
  have hsplit := Finset.sum_filter_add_sum_filter_not (G.filter (MemBox (data P) β))
    (fun z => z j ≤ t) (slack P β)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  omega

lemma weight_split_lt (P : Params) (β : Box P.toPublic) (j : Fin P.p) (t : ℤ)
    (h1 : β.1 j ≤ t) (h2 : t + 1 ≤ β.2 j) (z' : Fin P.p → ℤ) (hz' : z' ∈ goodPoints P)
    (hm : MemBox (data P) β z') (hj : z' j = t ∨ z' j = t + 1) :
    weight P (leftChild (data P) β j t) + weight P (rightChild (data P) β j t) + 1 ≤
      weight P β := by
  classical
  unfold weight
  set G := goodPoints P
  have hLeq : G.filter (MemBox (data P) (leftChild (data P) β j t)) =
      G.filter (fun z => MemBox (data P) β z ∧ z j ≤ t) :=
    Finset.filter_congr fun z _ => ⟨fun h => memBox_of_leftChild h (by omega),
      fun h => memBox_leftChild h.1 h.2⟩
  have hReq : G.filter (MemBox (data P) (rightChild (data P) β j t)) =
      G.filter (fun z => MemBox (data P) β z ∧ ¬ z j ≤ t) :=
    Finset.filter_congr fun z _ => ⟨fun h => ⟨(memBox_of_rightChild h h1).1,
      by have := (memBox_of_rightChild h h1).2; omega⟩,
      fun h => memBox_rightChild h.1 (by omega)⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (G.filter (MemBox (data P) β))
    (fun z => z j ≤ t) (slack P β)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  rw [hLeq, hReq]
  rcases hj with hj | hj
  · have hmem : z' ∈ G.filter (fun z => MemBox (data P) β z ∧ z j ≤ t) := by
      simp [Finset.mem_filter, hz', hm, hj]
    have hL : ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ z j ≤ t),
        slack P (leftChild (data P) β j t) z + 1 ≤
        ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ z j ≤ t), slack P β z := by
      exact Nat.succ_le_of_lt (Finset.sum_lt_sum (fun z _ => slack_left_le P β j t z (by omega))
        ⟨z', hmem, Nat.lt_of_succ_le (slack_left_lt P β j t z' h2 hj)⟩)
    have hR : ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ ¬ z j ≤ t),
        slack P (rightChild (data P) β j t) z ≤
        ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ ¬ z j ≤ t), slack P β z :=
      Finset.sum_le_sum fun z _ => slack_right_le P β j t z h1
    omega
  · have hmem : z' ∈ G.filter (fun z => MemBox (data P) β z ∧ ¬ z j ≤ t) := by
      simp only [Finset.mem_filter]
      exact ⟨hz', hm, by omega⟩
    have hR : ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ ¬ z j ≤ t),
        slack P (rightChild (data P) β j t) z + 1 ≤
        ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ ¬ z j ≤ t), slack P β z := by
      exact Nat.succ_le_of_lt (Finset.sum_lt_sum (fun z _ => slack_right_le P β j t z h1)
        ⟨z', hmem, Nat.lt_of_succ_le (slack_right_lt P β j t z' h1 hj)⟩)
    have hL : ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ z j ≤ t),
        slack P (leftChild (data P) β j t) z ≤
        ∑ z ∈ G.filter (fun z => MemBox (data P) β z ∧ z j ≤ t), slack P β z :=
      Finset.sum_le_sum fun z _ => slack_left_le P β j t z (by omega)
    omega

lemma good_perm {P : Params} {l₁ l₂ : List (Box P.toPublic)} {inc : Option (Solution P.toPublic)}
    (h : Good (data P) ⟨l₁, inc⟩) (hp : l₁.Perm l₂) : Good (data P) ⟨l₂, inc⟩ :=
  ⟨fun β hβ => h.nonempty β (hp.mem_iff.2 hβ), h.feasible, fun x hx hi => by
    obtain ⟨γ, hγ, hm⟩ := h.covered x hx hi
    exact ⟨γ, hp.mem_iff.1 hγ, hm⟩⟩

lemma sum_map_filter_le {α : Type*} (f : α → ℕ) (q : α → Bool) (l : List α) :
    ((l.filter q).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : q a = true
    · simp [ha]; omega
    · simp [ha]; omega

lemma head_keyBelow {P : Params} {s : BestBoundState P.toPublic} (hs : Inv P s)
    {e : Entry P.toPublic} {rest : List (Entry P.toPublic)} (h : s.nodes = e :: rest) :
    KeyBelow P e.2 := by
  intro x hx
  by_cases himp : Improves (data P) s.incumbent (objective (data P) (toPoint (data P) x))
  · obtain ⟨γ, hγ, hmem⟩ := hs.good.covered x hx himp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hγ
    have hkey := hs.key f hf _ (relaxation_of_mixed hx hmem)
    have hsorted := hs.sorted
    rw [h] at hf hsorted
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hkey
    · exact (List.rel_of_pairwise_cons hsorted hf).trans hkey
  · simp only [Improves, not_forall, not_lt] at himp
    obtain ⟨w, hw, hle⟩ := himp
    have := hs.clean e (by rw [h]; exact List.mem_cons_self) w hw
    exact this.le.trans (WithBot.coe_le_coe.2 hle)

lemma entryCost_head {P : Params} {s : BestBoundState P.toPublic} (hs : Inv P s)
    {e : Entry P.toPublic} {rest : List (Entry P.toPublic)} (h : s.nodes = e :: rest) :
    entryCost P e = 1 + 2 * weight P e.1 := by
  classical
  unfold entryCost
  rw [ite_eq_left (head_keyBelow hs h)]

lemma relaxation_of_leftChild {P : Params} {β : Box P.toPublic} {j : Fin P.p} {t : ℤ}
    (ht : t ≤ β.2 j) {x : (Fin P.p → ℝ) × (Fin P.q → ℝ)}
    (hx : RelaxationFeasible (data P) (leftChild (data P) β j t) x) :
    RelaxationFeasible (data P) β x := by
  refine ⟨hx.1, hx.2.1, fun k => ?_⟩
  have hk := hx.2.2 k
  by_cases hkj : k = j
  · subst hkj
    simp only [leftChild, Function.update_self] at hk
    exact ⟨hk.1, hk.2.trans (by exact_mod_cast ht)⟩
  · simpa [leftChild, Function.update_of_ne hkj] using hk

lemma relaxation_of_rightChild {P : Params} {β : Box P.toPublic} {j : Fin P.p} {t : ℤ}
    (ht : β.1 j ≤ t) {x : (Fin P.p → ℝ) × (Fin P.q → ℝ)}
    (hx : RelaxationFeasible (data P) (rightChild (data P) β j t) x) :
    RelaxationFeasible (data P) β x := by
  refine ⟨hx.1, hx.2.1, fun k => ?_⟩
  have hk := hx.2.2 k
  by_cases hkj : k = j
  · subst hkj
    simp only [rightChild, Function.update_self] at hk
    exact ⟨le_trans (by push_cast; linarith [(show (β.1 k : ℝ) ≤ t by exact_mod_cast ht)]) hk.1,
      hk.2⟩
  · simpa [rightChild, Function.update_of_ne hkj] using hk

lemma roundDown_good {P : Params} (hlam : ∀ i, 0 ≤ P.lam i) (hd : P.d + P.lam ᵥ* P.G = 0)
    {y : (Fin P.p → ℝ) × (Fin P.q → ℝ)} (hy : RelaxationFeasible (data P) (P.lo, P.hi) y)
    (hkey : KeyBelow P (objective (data P) y : WithBot ℝ)) :
    roundDown P y.1 ∈ goodPoints P := by
  classical
  unfold goodPoints
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun k => Finset.mem_Icc.2 (roundDown_mem (β := (P.lo, P.hi)) hy.2.1 k), ?_⟩
  intro x hx
  have h1 := lagrangian_roundDown P y.1
  have h2 := lagrangian_le_objective hlam hd hy.1
  have h3 := WithBot.coe_le_coe.1 (hkey x hx)
  convert h1.trans (h2.trans h3) using 1

lemma gapPotential_cons (P : Params) (e : Entry P.toPublic) (l : List (Entry P.toPublic)) :
    gapPotential P (e :: l) = entryCost P e + gapPotential P l := by
  simp [gapPotential]

lemma boxPotential_cons (P : Params) (e : Entry P.toPublic) (l : List (Entry P.toPublic)) :
    boxPotential P (e :: l) = (2 * boxCard (data P) e.1 - 1) + boxPotential P l := by
  simp [boxPotential, potential]

lemma gapPotential_perm (P : Params) {l₁ l₂ : List (Entry P.toPublic)} (h : l₁.Perm l₂) :
    gapPotential P l₁ = gapPotential P l₂ := (h.map _).sum_eq

lemma boxPotential_perm (P : Params) {l₁ l₂ : List (Entry P.toPublic)} (h : l₁.Perm l₂) :
    boxPotential P l₁ = boxPotential P l₂ := ((h.map Prod.fst).map _).sum_eq

lemma insert_perm (Q : Public) (a b : Entry Q) (l : List (Entry Q)) :
    (insertEntry Q a (insertEntry Q b l)).Perm (a :: b :: l) :=
  (List.perm_orderedInsert _ a _).trans ((List.perm_orderedInsert _ b l).cons a)

lemma bestBoundNode_eq (P : Params) (β : Box P.toPublic) (rest : List (Entry P.toPublic))
    (inc : Option (Solution P.toPublic)) (y : Point P.toPublic) :
    bestBoundNode P.toPublic β rest inc y =
      open Classical in
      if ¬ Improves (data P) inc (objective (data P) y) then ⟨rest, inc⟩
      else if h : ∃ j, Int.fract (y.1 j) ≠ 0 then
        ⟨insertEntry P.toPublic (leftChild (data P) β h.choose ⌊y.1 h.choose⌋,
            (objective (data P) y : WithBot ℝ))
          (insertEntry P.toPublic (rightChild (data P) β h.choose ⌊y.1 h.choose⌋,
            (objective (data P) y : WithBot ℝ)) rest), inc⟩
      else ⟨rest.filter (keepEntry P.toPublic (fun j => ⌊y.1 j⌋, y.2)),
        some (fun j => ⌊y.1 j⌋, y.2)⟩ := rfl

lemma inv_update {P : Params} (hlam : ∀ i, 0 ≤ P.lam i) (hd : P.d + P.lam ᵥ* P.G = 0)
    {s : BestBoundState P.toPublic} (hs : Inv P s) {r : Option (Point P.toPublic)}
    (hr : SolvesRelaxation (data P) (s.nodes.headD ((P.lo, P.hi), ⊥)).1 r)
    (hne : s.nodes ≠ []) :
    Inv P (bestBoundUpdate P.toPublic s r) ∧
      boxPotential P (bestBoundUpdate P.toPublic s r).nodes + 1 ≤ boxPotential P s.nodes ∧
      gapPotential P (bestBoundUpdate P.toPublic s r).nodes + 1 ≤ gapPotential P s.nodes := by
  obtain ⟨nodes, inc⟩ := s
  obtain _ | ⟨e, rest⟩ := nodes
  · exact absurd rfl hne
  obtain ⟨β, k⟩ := e
  have hhead := entryCost_head hs (show (⟨(β, k) :: rest, inc⟩ : BestBoundState _).nodes =
    (β, k) :: rest from rfl)
  have hβ : BoxNonempty (data P) β := hs.good.nonempty β (by simp)
  have hcard := boxCard_pos hβ
  have hbp := boxPotential_cons P (β, k) rest
  have hgp := gapPotential_cons P (β, k) rest
  simp only at hbp hgp hhead
  simp only [List.headD_cons] at hr
  have hrestInv : ∀ inc', inc' = inc → Inv P ⟨rest, inc⟩ →
      Inv P ⟨rest, inc⟩ ∧ boxPotential P rest + 1 ≤ boxPotential P ((β, k) :: rest) ∧
        gapPotential P rest + 1 ≤ gapPotential P ((β, k) :: rest) := by
    intro _ _ h
    exact ⟨h, by omega, by omega⟩
  have hsub : ∀ (good : Good (data P) ⟨rest.map Prod.fst, inc⟩), Inv P ⟨rest, inc⟩ :=
    fun good => ⟨good, hs.sorted.of_cons, fun f hf => hs.key f (by simp [hf]),
      fun f hf => hs.clean f (by simp [hf])⟩
  cases r with
  | none =>
    refine hrestInv inc rfl (hsub ⟨fun γ hγ => hs.good.nonempty γ (by simp_all),
      hs.good.feasible, fun x hx himp => ?_⟩)
    obtain ⟨γ, hγ, hmem⟩ := hs.good.covered x hx himp
    simp only [List.map_cons, List.mem_cons] at hγ
    rcases hγ with rfl | hγ
    · exact absurd (relaxation_of_mixed hx hmem) (hr _)
    · exact ⟨γ, hγ, hmem⟩
  | some y =>
    change Inv P (bestBoundNode P.toPublic β rest inc y) ∧
      boxPotential P (bestBoundNode P.toPublic β rest inc y).nodes + 1 ≤
        boxPotential P ((β, k) :: rest) ∧
      gapPotential P (bestBoundNode P.toPublic β rest inc y).nodes + 1 ≤
        gapPotential P ((β, k) :: rest)
    rw [bestBoundNode_eq]
    by_cases himp : Improves (data P) inc (objective (data P) y)
    · rw [ite_eq_right (not_not.2 himp)]
      by_cases hfrac : ∃ j, Int.fract (y.1 j) ≠ 0
      · rw [dite_eq_left hfrac]
        set j := hfrac.choose
        have hj : Int.fract (y.1 j) ≠ 0 := hfrac.choose_spec
        set t := ⌊y.1 j⌋
        have hlo : β.1 j ≤ t := Int.le_floor.2 (hr.1.2.2 j).1
        have hhi : t + 1 ≤ β.2 j := floor_add_one_le hj (hr.1.2.2 j).2
        have hsplit := boxCard_split (P := data P) β j t hlo hhi
        have hL : BoxNonempty (data P) (leftChild (data P) β j t) := by
          intro i
          by_cases hi : i = j
          · subst hi; simp [leftChild, hlo]
          · simp [leftChild, Function.update_of_ne hi, hβ i]
        have hR : BoxNonempty (data P) (rightChild (data P) β j t) := by
          intro i
          by_cases hi : i = j
          · subst hi; simp [rightChild, hhi]
          · simp [rightChild, Function.update_of_ne hi, hβ i]
        have hcL := boxCard_pos hL
        have hcR := boxCard_pos hR
        set v : WithBot ℝ := (objective (data P) y : WithBot ℝ)
        set eL : Entry P.toPublic := (leftChild (data P) β j t, v)
        set eR : Entry P.toPublic := (rightChild (data P) β j t, v)
        have hperm := insert_perm P.toPublic eL eR rest
        refine ⟨⟨good_perm (l₁ := eL.1 :: eR.1 :: rest.map Prod.fst) ?_
            (by simpa using (hperm.map Prod.fst).symm), ?_, ?_, ?_⟩, ?_, ?_⟩
        · refine ⟨fun γ hγ => ?_, hs.good.feasible, fun x hx hxi => ?_⟩
          · simp only [List.mem_cons] at hγ
            rcases hγ with rfl | rfl | hγ
            · exact hL
            · exact hR
            · exact hs.good.nonempty γ (by simp [hγ])
          · obtain ⟨γ, hγ, hmem⟩ := hs.good.covered x hx hxi
            simp only [List.map_cons, List.mem_cons] at hγ
            rcases hγ with rfl | hγ
            · rcases le_or_gt (x.1 j) t with hle | hlt
              · exact ⟨eL.1, by simp, memBox_leftChild hmem hle⟩
              · exact ⟨eR.1, by simp, memBox_rightChild hmem (by omega)⟩
            · exact ⟨γ, by simp [hγ], hmem⟩
        · exact (hs.sorted.of_cons.orderedInsert eR rest).orderedInsert eL _
        · intro f hf x hx
          rcases List.mem_cons.1 (hperm.mem_iff.1 hf) with rfl | hf
          · exact WithBot.coe_le_coe.2 (hr.2 x (relaxation_of_leftChild (by omega) hx))
          rcases List.mem_cons.1 hf with rfl | hf
          · exact WithBot.coe_le_coe.2 (hr.2 x (relaxation_of_rightChild hlo hx))
          · exact hs.key f (by simp [hf]) x hx
        · intro f hf w hw
          rcases List.mem_cons.1 (hperm.mem_iff.1 hf) with rfl | hf
          · exact WithBot.coe_lt_coe.2 (himp w hw)
          rcases List.mem_cons.1 hf with rfl | hf
          · exact WithBot.coe_lt_coe.2 (himp w hw)
          · exact hs.clean f (by simp [hf]) w hw
        · change boxPotential P (insertEntry P.toPublic eL (insertEntry P.toPublic eR rest)) + 1 ≤ _
          rw [boxPotential_perm P hperm, boxPotential_cons, boxPotential_cons, hbp]
          simp only [eL, eR]
          omega
        · change gapPotential P (insertEntry P.toPublic eL (insertEntry P.toPublic eR rest)) + 1 ≤ _
          rw [gapPotential_perm P hperm, gapPotential_cons, gapPotential_cons, hgp, hhead]
          have hw := weight_split P β j t hlo hhi
          classical
          by_cases hkb : KeyBelow P v
          · have hz := roundDown_good hlam hd (y := y) ⟨hr.1.1, hr.1.2.1, hr.1.2.1⟩ hkb
            have hm : MemBox (data P) β (roundDown P y.1) := roundDown_mem hr.1.2.2
            have hlt := weight_split_lt P β j t hlo hhi _ hz hm (roundDown_frac y.1 hj)
            simp only [entryCost, eL, eR, hkb, ↓reduceIte]
            omega
          · simp only [entryCost, eL, eR, hkb, ↓reduceIte]
            omega
      · rw [dite_eq_right hfrac]
        push Not at hfrac
        have hpt : toPoint (data P) (fun j => ⌊y.1 j⌋, y.2) = y := by
          obtain ⟨z, w⟩ := y
          simp only [toPoint, Prod.mk.injEq, and_true]
          funext j
          exact cast_floor_of_fract (hfrac j)
        set w : Solution P.toPublic := (fun j => ⌊y.1 j⌋, y.2)
        have hkeep : ∀ f : Entry P.toPublic, keepEntry P.toPublic w f = true ↔
            f.2 < (objective (data P) y : WithBot ℝ) := by
          intro f
          unfold keepEntry
          rw [decide_eq_true_iff]
          change f.2 < (objective (data P) (toPoint (data P) w) : WithBot ℝ) ↔ _
          rw [hpt]
        refine ⟨⟨⟨fun γ hγ => ?_, fun x hx => ?_, fun x hx hxi => ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
        · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hγ
          have hmem : f.1 ∈ ((β, k) :: rest).map Prod.fst :=
            List.mem_map.2 ⟨f, List.mem_cons_of_mem _ (List.mem_filter.1 hf).1, rfl⟩
          exact hs.good.nonempty f.1 hmem
        · cases hx
          refine ⟨by rw [hpt]; exact hr.1.1, fun j => ⟨?_, ?_⟩⟩
          · exact Int.le_floor.2 (hr.1.2.1 j).1
          · have h1 := (hr.1.2.1 j).2
            have h2 : (⌊y.1 j⌋ : ℝ) ≤ P.hi j := (Int.floor_le _).trans h1
            exact_mod_cast h2
        · have hlt := hxi _ rfl
          rw [hpt] at hlt
          obtain ⟨γ, hγ, hmem⟩ := hs.good.covered x hx (fun u hu => hlt.trans (himp u hu))
          simp only [List.map_cons, List.mem_cons] at hγ
          rcases hγ with rfl | hγ
          · exact absurd (hr.2 _ (relaxation_of_mixed hx hmem)) (not_le.2 hlt)
          · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hγ
            refine ⟨f.1, List.mem_map.2 ⟨f, List.mem_filter.2 ⟨hf, (hkeep f).2 ?_⟩, rfl⟩, hmem⟩
            exact (hs.key f (by simp [hf]) _ (relaxation_of_mixed hx hmem)).trans_lt
              (WithBot.coe_lt_coe.2 hlt)
        · exact hs.sorted.of_cons.filter _
        · intro f hf
          exact hs.key f (by simp [(List.mem_filter.1 hf).1])
        · intro f hf u hu
          cases hu
          rw [hpt]
          exact (hkeep f).1 (List.mem_filter.1 hf).2
        · change boxPotential P (rest.filter (keepEntry P.toPublic w)) + 1 ≤ _
          have h1 : boxPotential P (rest.filter (keepEntry P.toPublic w)) ≤
              boxPotential P rest := by
            unfold boxPotential potential
            rw [List.map_map, List.map_map]
            exact sum_map_filter_le _ _ rest
          omega
        · change gapPotential P (rest.filter (keepEntry P.toPublic w)) + 1 ≤ _
          have h2 : gapPotential P (rest.filter (keepEntry P.toPublic w)) ≤ gapPotential P rest :=
            sum_map_filter_le _ _ rest
          rw [hgp, hhead]
          omega
    · rw [ite_eq_left himp]
      refine hrestInv inc rfl (hsub ⟨fun γ hγ => hs.good.nonempty γ (by simp_all),
        hs.good.feasible, fun x hx hxi => ?_⟩)
      obtain ⟨γ, hγ, hmem⟩ := hs.good.covered x hx hxi
      simp only [List.map_cons, List.mem_cons] at hγ
      rcases hγ with rfl | hγ
      · exfalso
        apply himp
        intro u hu
        exact (hr.2 _ (relaxation_of_mixed hx hmem)).trans_lt (hxi u hu)
      · exact ⟨γ, hγ, hmem⟩

lemma bestBoundUpdate_nil (P : Params) (s : BestBoundState P.toPublic)
    (r : Option (Point P.toPublic))
    (h : s.nodes = []) : bestBoundUpdate P.toPublic s r = s := by
  unfold bestBoundUpdate
  rw [h]

lemma initialNodes_map (P : Params) :
    (initialNodes P.toPublic).map Prod.fst =
      OracleTemplate.BoundedMixedIntegerLinear.initialStack (data P) := by
  classical
  unfold initialNodes OracleTemplate.BoundedMixedIntegerLinear.initialStack
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

lemma inv_initial (P : Params) : Inv P ⟨initialNodes P.toPublic, none⟩ := by
  classical
  have hg := OracleTemplate.BoundedMixedIntegerLinear.good_initial (data P)
  rw [← initialNodes_map] at hg
  refine ⟨hg, ?_, fun e he x _ => ?_, fun _ _ w hw => by cases hw⟩
  · unfold initialNodes
    split_ifs <;> simp
  · unfold initialNodes at he
    split_ifs at he
    · simp only [List.mem_singleton] at he
      subst he
      exact bot_le
    · simp at he

lemma boxPotential_initial (P : Params) :
    boxPotential P (initialNodes P.toPublic) ≤ 2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1 := by
  unfold boxPotential
  rw [initialNodes_map]
  exact OracleTemplate.BoundedMixedIntegerLinear.potential_initial (data P)

lemma weight_root_le (P : Params) : weight P (P.lo, P.hi) ≤ 2 * P.p * (goodPoints P).card := by
  classical
  unfold weight
  calc ∑ z ∈ (goodPoints P).filter (MemBox (data P) (P.lo, P.hi)), slack P (P.lo, P.hi) z
      ≤ ∑ z ∈ goodPoints P, slack P (P.lo, P.hi) z :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ ∑ _z ∈ goodPoints P, 2 * P.p := Finset.sum_le_sum fun z _ => slack_le_root P z
    _ = 2 * P.p * (goodPoints P).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma gapPotential_initial (P : Params) :
    gapPotential P (initialNodes P.toPublic) ≤ 1 + 4 * P.p * (goodPoints P).card := by
  classical
  have hw := weight_root_le P
  unfold initialNodes
  split_ifs
  · simp only [gapPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold entryCost
    have : (if KeyBelow P (⊥ : WithBot ℝ) then 1 else 0) ≤ 1 := by split_ifs <;> omega
    simp only at this ⊢
    nlinarith
  · simp [gapPotential]

lemma nodes_nil_of_boxPotential {P : Params} {s : BestBoundState P.toPublic} (hs : Inv P s)
    (h : boxPotential P s.nodes = 0) : s.nodes = [] := by
  have := OracleTemplate.BoundedMixedIntegerLinear.stack_nil_of_potential (P := data P)
    (s := ⟨s.nodes.map Prod.fst, s.incumbent⟩) hs.good h
  simpa using this

lemma nodes_nil_of_gapPotential {P : Params} {s : BestBoundState P.toPublic} (hs : Inv P s)
    (h : gapPotential P s.nodes = 0) : s.nodes = [] := by
  cases hn : s.nodes with
  | nil => rfl
  | cons e rest =>
    exfalso
    have hc := entryCost_head hs hn
    rw [hn, gapPotential_cons] at h
    omega

lemma run_inv (P : Params) (hlam : ∀ i, 0 ≤ P.lam i) (hd : P.d + P.lam ᵥ* P.G = 0)
    (O : Oracle (Box P.toPublic) (Option (Point P.toPublic)))
    (hO : IsRelaxationOracle (data P) O) (seed : (bestBoundBranchAndBound P.toPublic).Seed)
    (ξ : (k : ℕ) → O.Seed k) (k : ℕ) :
    let A := bestBoundBranchAndBound P.toPublic
    let F := fun sc : A.State × List ((Fin 1 × Box P.toPublic) × Option (Point P.toPublic)) =>
      let query := A.query sc.1
      let reply := O.answer sc.2 query (ξ sc.2.length)
      (A.update sc.1 reply, sc.2 ++ [(query, reply)])
    Inv P (F^[k] (A.initial seed, [])).1 ∧
      ((F^[k] (A.initial seed, [])).1.nodes = [] ∨
        (boxPotential P (F^[k] (A.initial seed, [])).1.nodes + k ≤
            boxPotential P (initialNodes P.toPublic) ∧
          gapPotential P (F^[k] (A.initial seed, [])).1.nodes + k ≤
            gapPotential P (initialNodes P.toPublic))) := by
  intro A F
  induction k with
  | zero => exact ⟨inv_initial P, Or.inr ⟨le_refl _, le_refl _⟩⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set sc := F^[k] (A.initial seed, [])
    obtain ⟨hg, hk⟩ := ih
    have hr : SolvesRelaxation (data P) (sc.1.nodes.headD ((P.lo, P.hi), ⊥)).1
        (O.answer sc.2 (A.query sc.1) (ξ sc.2.length)) := hO _ _ _
    change Inv P (bestBoundUpdate P.toPublic sc.1 _) ∧
      ((bestBoundUpdate P.toPublic sc.1 _).nodes = [] ∨
        (boxPotential P (bestBoundUpdate P.toPublic sc.1 _).nodes + (k + 1) ≤
            boxPotential P (initialNodes P.toPublic) ∧
          gapPotential P (bestBoundUpdate P.toPublic sc.1 _).nodes + (k + 1) ≤
            gapPotential P (initialNodes P.toPublic)))
    by_cases hnil : sc.1.nodes = []
    · rw [bestBoundUpdate_nil P sc.1 _ hnil]
      exact ⟨hg, Or.inl hnil⟩
    · obtain ⟨hg', hp1, hp2⟩ := inv_update hlam hd hg hr hnil
      refine ⟨hg', Or.inr ?_⟩
      rcases hk with hk | ⟨hk1, hk2⟩
      · exact absurd hk hnil
      · exact ⟨by omega, by omega⟩

lemma bestBound_solves (P : Params) (hlam : ∀ i, 0 ≤ P.lam i) (hd : P.d + P.lam ᵥ* P.G = 0)
    (O : Oracle (Box P.toPublic) (Option (Point P.toPublic)))
    (hO : IsRelaxationOracle (data P) O) (seed : (bestBoundBranchAndBound P.toPublic).Seed)
    (ξ : (k : ℕ) → O.Seed k) :
    SolvesMixed (data P) (execute O (bestBoundBranchAndBound P.toPublic)
      (fun _ => min (2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1)
        (1 + 4 * P.p * (goodPoints P).card)) seed ξ) := by
  rw [execute_indexed]
  set K := min (2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1) (1 + 4 * P.p * (goodPoints P).card)
  obtain ⟨hg, hk⟩ := run_inv P hlam hd O hO seed ξ K
  refine solves_of_good (P := data P) hg.good (List.map_eq_nil_iff.2 ?_)
  rcases hk with hk | ⟨hk1, hk2⟩
  · exact hk
  · have hb := boxPotential_initial P
    have hgp := gapPotential_initial P
    rcases min_choice (2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1)
      (1 + 4 * P.p * (goodPoints P).card) with h | h
    · exact nodes_nil_of_boxPotential hg (by have hKe : K = _ := h; omega)
    · exact nodes_nil_of_gapPotential hg (by have hKe : K = _ := h; omega)

lemma incumbent_none_of_infeasible (P : Params)
    (hinf : ∀ x, ¬ RelaxationFeasible (data P) (P.lo, P.hi) x)
    (O : Oracle (Box P.toPublic) (Option (Point P.toPublic)))
    (hO : IsRelaxationOracle (data P) O) (seed : (bestBoundBranchAndBound P.toPublic).Seed)
    (ξ : (k : ℕ) → O.Seed k) (k : ℕ) :
    let A := bestBoundBranchAndBound P.toPublic
    let F := fun sc : A.State × List ((Fin 1 × Box P.toPublic) × Option (Point P.toPublic)) =>
      let query := A.query sc.1
      let reply := O.answer sc.2 query (ξ sc.2.length)
      (A.update sc.1 reply, sc.2 ++ [(query, reply)])
    (F^[k] (A.initial seed, [])).1.incumbent = none := by
  intro A F
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set sc := F^[k] (A.initial seed, [])
    have hr : SolvesRelaxation (data P) (sc.1.nodes.headD ((P.lo, P.hi), ⊥)).1
        (O.answer sc.2 (A.query sc.1) (ξ sc.2.length)) := hO _ _ _
    change (bestBoundUpdate P.toPublic sc.1
      (O.answer sc.2 (A.query sc.1) (ξ sc.2.length))).incumbent = none
    generalize O.answer sc.2 (A.query sc.1) (ξ sc.2.length) = r at hr
    rcases hn : sc.1.nodes with _ | ⟨e, rest⟩
    · rw [bestBoundUpdate_nil P sc.1 r hn]
      exact ih
    · rw [hn] at hr
      rcases r with _ | x
      · simp only [bestBoundUpdate, hn]
        exact ih
      · exfalso
        obtain ⟨⟨h1, h2, _⟩, _⟩ := hr
        exact hinf x ⟨h1, h2, h2⟩

lemma bestBound_solves_infeasible (P : Params)
    (hinf : ∀ x, ¬ RelaxationFeasible (data P) (P.lo, P.hi) x)
    (O : Oracle (Box P.toPublic) (Option (Point P.toPublic)))
    (hO : IsRelaxationOracle (data P) O) (seed : (bestBoundBranchAndBound P.toPublic).Seed)
    (ξ : (k : ℕ) → O.Seed k) (K : ℕ) :
    SolvesMixed (data P) (execute O (bestBoundBranchAndBound P.toPublic) (fun _ => K) seed ξ) := by
  have h := incumbent_none_of_infeasible P hinf O hO seed ξ K
  rw [execute_indexed]
  refine (?_ : ∀ o : Option (Solution P.toPublic), o = none → SolvesMixed (data P) o) _ h
  rintro _ rfl x hx
  exact hinf _ (relaxation_of_mixed hx fun j => hx.2 j)

end OracleTemplate.HiddenMixedIntegerLinear
