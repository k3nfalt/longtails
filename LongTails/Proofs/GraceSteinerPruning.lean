import LongTails.Proofs.GraceSteinerCuts

namespace LongTails.Proofs.GraceSteinerPruning

open GraceSteinerCuts

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

def Joins (a : Endpoints V E) (e : E) (u v : V) :=
  (a.left e = u ∧ a.right e = v) ∨ (a.left e = v ∧ a.right e = u)

structure Branches (a : Endpoints V E) (F : Finset E) (r : V) (U : Finset V) where
  root_mem : r ∈ U
  parent : V → V
  depth : V → ℕ
  depth_root : depth r = 0
  parent_root : parent r = r
  branch : ∀ v ∈ U, v ≠ r → parent v ∈ U ∧ depth (parent v) + 1 = depth v ∧
    ∃ e ∈ F, Joins a e v (parent v)

variable {a : Endpoints V E} {F : Finset E} {r : V} {U : Finset V}

def singleton (a : Endpoints V E) (F : Finset E) (r : V) : Branches a F r {r} :=
  ⟨by simp, id, fun _ => 0, rfl, rfl, by simp⟩

omit [Fintype V] in
def insertLeaf (T : Branches a F r U) (e : E) (he : e ∈ F) (i j : V)
    (hi : i ∈ U) (hj : j ∉ U) (hij : Joins a e j i) : Branches a F r (insert j U) := by
  let par := Function.update T.parent j i
  let d := Function.update T.depth j (T.depth i + 1)
  have hr : r ≠ j := fun h => hj (h ▸ T.root_mem)
  refine ⟨Finset.mem_insert_of_mem T.root_mem, par, d, ?_, ?_, ?_⟩
  · simpa [d, Function.update_of_ne hr] using T.depth_root
  · simpa [par, Function.update_of_ne hr] using T.parent_root
  · intro v hv hvr
    rcases Finset.mem_insert.mp hv with rfl | hv
    · have hne : i ≠ v := fun h => hj (h ▸ hi)
      simp [par, d, Function.update_of_ne hne, hi, show ∃ e ∈ F, Joins a e v i from ⟨e, he, hij⟩]
    · have hvj : v ≠ j := fun h => hj (h ▸ hv)
      obtain ⟨hp, hd, hb⟩ := T.branch v hv hvr
      have hpj : T.parent v ≠ j := fun h => hj (h ▸ hp)
      exact ⟨by simp [par, Function.update_of_ne hvj, hp],
        by simpa [par, d, Function.update_of_ne hvj, Function.update_of_ne hpj] using hd,
        by simpa [par, Function.update_of_ne hvj] using hb⟩

omit [DecidableEq E] in
lemma exists_spanning {S : Finset V} (hr : r ∈ S) (h : Connects a S F) :
    ∃ U : Finset V, S ⊆ U ∧ Nonempty (Branches a F r U) := by
  classical
  let sets := Finset.univ.filter (fun U : Finset V => Nonempty (Branches a F r U))
  have hs : sets.Nonempty := ⟨{r}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨singleton a F r⟩⟩⟩
  obtain ⟨U, hU, hmax⟩ := Finset.exists_max_image sets Finset.card hs
  obtain ⟨T⟩ := (Finset.mem_filter.mp hU).2
  refine ⟨U, ?_, ⟨T⟩⟩
  by_contra! hn
  obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp hn
  obtain ⟨e, he, hc⟩ := h U ⟨⟨r, hr, T.root_mem⟩, ⟨v, hv, hvU⟩⟩
  have extend (i j : V) (hi : i ∈ U) (hj : j ∉ U) (hij : Joins a e j i) : False := by
    have ht := insertLeaf T e he i j hi hj hij
    have hm := hmax (insert j U) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨ht⟩⟩)
    rw [Finset.card_insert_of_notMem hj] at hm
    omega
  by_cases hl : a.left e ∈ U
  · have hn : a.right e ∉ U := fun hm => hc ⟨fun _ => hm, fun _ => hl⟩
    exact extend _ _ hl hn (Or.inr ⟨rfl,rfl⟩)
  · have hm : a.right e ∈ U := by by_contra hn; exact hc (by simp [hl,hn])
    exact extend _ _ hm hl (Or.inl ⟨rfl,rfl⟩)

omit [DecidableEq E] in
lemma exists_pruned {S : Finset V} (hr : r ∈ S) (h : Connects a S F) :
    ∃ (U : Finset V) (T : Branches a F r U), S ⊆ U ∧
      ∀ u ∈ U, u ∉ S → ∃ v ∈ U.erase r, T.parent v = u := by
  classical
  let sets := Finset.univ.filter (fun U : Finset V => S ⊆ U ∧ Nonempty (Branches a F r U))
  obtain ⟨W, hS, hW⟩ := exists_spanning hr h
  have hn : sets.Nonempty := ⟨W, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS, hW⟩⟩
  obtain ⟨U, hU, hmin⟩ := Finset.exists_min_image sets Finset.card hn
  obtain ⟨hSU, ⟨T⟩⟩ := (Finset.mem_filter.mp hU).2
  refine ⟨U, T, hSU, ?_⟩
  intro u hu hus
  by_contra! hleaf
  have hE : S ⊆ U.erase u := fun i hi =>
    Finset.mem_erase.mpr ⟨fun h => hus (h ▸ hi), hSU hi⟩
  let tree : Branches a F r (U.erase u) := {
    root_mem := hE hr
    parent := T.parent
    depth := T.depth
    depth_root := T.depth_root
    parent_root := T.parent_root
    branch := by
      intro v hv hvr
      have hvU := (Finset.mem_erase.mp hv).2
      obtain ⟨hp, hb⟩ := T.branch v hvU hvr
      exact ⟨Finset.mem_erase.mpr ⟨hleaf v (Finset.mem_erase.mpr ⟨hvr, hvU⟩), hp⟩, hb⟩ }
  have hm := hmin (U.erase u) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE, ⟨tree⟩⟩)
  exact (Finset.card_erase_lt_of_mem hu).not_ge hm

omit [Fintype V] [DecidableEq E] in
lemma terminal_degrees {S : Finset V} (T : Branches a F r U) (hr : r ∈ S) (hSU : S ⊆ U)
    (hchildren : ∀ u ∈ U, u ∉ S → ∃ v ∈ U.erase r, T.parent v = u) :
    ∑ v ∈ U.erase r, ((if v ∈ S then 1 else 0) + (if T.parent v ∈ S then 1 else 0)) ≤
      2 * (S.card - 1) := by
  classical
  let nodes := U.erase r
  let inn := nodes.filter (fun v => T.parent v ∉ S)
  let term := nodes.filter (fun v => T.parent v ∈ S)
  have hs : U \ S ⊆ inn.image T.parent := by
    intro u hu
    obtain ⟨hU, huS⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨v, hv, he⟩ := hchildren u hU huS
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, by simpa [he] using huS⟩, he⟩
  have hl := (Finset.card_le_card hs).trans Finset.card_image_le
  have hsplit : term.card + inn.card = nodes.card := Finset.card_filter_add_card_filter_not ..
  have him : nodes.filter (fun v => v ∈ S) = S.erase r := by
    ext v; simp only [nodes, Finset.mem_filter, Finset.mem_erase]; grind
  have hU := Finset.card_erase_add_one T.root_mem
  have hS := Finset.card_erase_add_one hr
  have hsub := Finset.card_sdiff_add_card_eq_card hSU
  change ∑ v ∈ nodes, _ ≤ _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_boole, him]
  change (S.erase r).card + term.card ≤ _
  dsimp only [nodes] at hsplit
  omega

omit [Fintype V] [DecidableEq E] in
lemma edge_incidence (a : Endpoints V E) (S : Finset V) (e : E) (u v : V)
    (he : Joins a e u v) (hne : u ≠ v) :
    incidence a S e = (if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0) := by
  classical
  have split (i : V) : (if Crosses a {i} e then 1 else 0 : ℕ) =
      (if u = i then 1 else 0) + (if v = i then 1 else 0) := by
    rcases he with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;>
      by_cases hu : u = i <;> by_cases hv : v = i <;> simp_all [Crosses]
  simp only [incidence, split, Finset.sum_add_distrib, Finset.sum_ite_eq]

lemma prune_connector [Nonempty E] {S : Finset V} (hr : r ∈ S) (h : Connects a S F) :
    ∃ F' ⊆ F, Connects a S F' ∧ ∑ e ∈ F', incidence a S e ≤ 2 * (S.card - 1) := by
  classical
  obtain ⟨U, T, hSU, hchildren⟩ := exists_pruned hr h
  let nodes := U.erase r
  let label (v : V) := if h : v ∈ nodes then
    (T.branch v (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1).2.2.choose
    else Classical.choice ‹Nonempty E›
  have edge (v : V) (hv : v ∈ nodes) : label v ∈ F ∧ Joins a (label v) v (T.parent v) := by
    simp only [label, dite_eq_left hv]
    exact (T.branch v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1).2.2.choose_spec
  have depth (v : V) (hv : v ∈ nodes) : T.depth (T.parent v) + 1 = T.depth v :=
    (T.branch v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1).2.1
  have diff (v : V) (hv : v ∈ nodes) : v ≠ T.parent v := by
    intro he
    have hd := depth v hv
    rw [← he] at hd
    omega
  have hinj : Set.InjOn label nodes := by
    intro u hu v hv heq
    have ha := (edge u hu).2
    have hb := (edge v hv).2
    rw [← heq] at hb
    have hd := depth u hu
    have hd' := depth v hv
    unfold Joins at ha hb
    grind
  refine ⟨nodes.image label, Finset.image_subset_iff.mpr (fun v hv => (edge v hv).1), ?_, ?_⟩
  · intro C hC
    by_contra! hn
    have same (v : V) (hv : v ∈ U) : v ∈ C ↔ r ∈ C := by
      induction v using (measure T.depth).wf.induction with
      | h v ih =>
        by_cases he : v = r
        · simp [he]
        · have hn' : v ∈ nodes := Finset.mem_erase.mpr ⟨he, hv⟩
          have hp := (T.branch v hv he).1
          have hl := hn (label v) (Finset.mem_image_of_mem _ hn')
          have hd := depth v hn'
          have hsmall : T.depth (T.parent v) < T.depth v := by omega
          have hpar := ih (T.parent v) hsmall hp
          have hc : a.left (label v) ∈ C ↔ a.right (label v) ∈ C := Classical.not_not.mp hl
          rcases (edge v hn').2 with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> rw [h₁,h₂] at hc <;> tauto
    obtain ⟨⟨i, hi, hiC⟩, ⟨j, hj, hjC⟩⟩ := hC
    exact hjC ((same j (hSU hj)).mpr ((same i (hSU hi)).mp hiC))
  · rw [Finset.sum_image hinj]
    calc
      _ = _ := Finset.sum_congr rfl fun v hv => edge_incidence a S (label v) v (T.parent v)
        (edge v hv).2 (diff v hv)
      _ ≤ _ := terminal_degrees T hr hSU hchildren

end LongTails.Proofs.GraceSteinerPruning
