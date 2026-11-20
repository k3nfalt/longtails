import LongTails.Proofs.GraceExchangeBlock

namespace LongTails.Proofs.GraceRoutedValues

open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.GraceRouting
open LongTails.Algorithms.GraceTree
open GraceExchangeBlock (afterReads)
open LeonTranscript (wire)

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n} (A : Routes p S r)

lemma after_cons (D q : ℕ) (phase : Phase) (k : ℕ) (v : Fin p.n → Values)
    (i j : Fin p.n) (ids : List (Fin p.n)) (acc : Values)
    (hv : ∀ x ∈ A.items D phase k j i, v j x < 2 ^ q) :
    afterReads A D q phase k v i (j::ids) acc = afterReads A D q phase k v i ids
      (fun x => if x ∈ A.items D phase k j i then
        match phase with | .reduce => acc x + v j x | .broadcast => v j x
        else acc x) := by
  let xs := A.items D phase k j i
  have hn : xs.Nodup := List.Nodup.filter _ List.nodup_range
  by_cases he : xs = []
  · simp [afterReads,show A.items D phase k j i = [] from he]
  · have he' : xs.isEmpty = false := by simpa using he
    change afterReads A D q phase k v i ids
      (if xs.isEmpty then acc else unpack phase q xs (wire (pack q xs (v j))) acc) = _
    rw [he']
    simp only [Bool.false_eq_true, ↓reduceIte,wire,GraceRouting.packet_contents phase q xs (v j) hn hv]
    cases phase <;> rfl

lemma reduce_read (D q k : ℕ) (v : Fin p.n → Values) (i : Fin p.n)
    (ids : List (Fin p.n)) (acc : Values) (x : ℕ)
    (hv : ∀ j, ∀ y ∈ A.items D .reduce k j i, v j y < 2 ^ q) :
    afterReads A D q .reduce k v i ids acc x = acc x +
      (ids.map fun j => if x ∈ A.items D .reduce k j i then v j x else 0).sum := by
  induction ids generalizing acc with
  | nil => simp [afterReads]
  | cons j js ih =>
    rw [after_cons A _ _ _ _ _ _ _ _ _ (hv j),ih]
    by_cases h : x ∈ A.items D .reduce k j i <;> simp [h,add_assoc]

lemma broadcast_read (D q k : ℕ) (v : Fin p.n → Values) (i : Fin p.n)
    (ids : List (Fin p.n)) (acc : Values) (x y : ℕ)
    (hv : ∀ j, ∀ z ∈ A.items D .broadcast k j i, v j z < 2 ^ q)
    (hs : ∀ j ∈ ids, x ∈ A.items D .broadcast k j i → v j x = y) :
    afterReads A D q .broadcast k v i ids acc x =
      if ∃ j ∈ ids, x ∈ A.items D .broadcast k j i then y else acc x := by
  induction ids generalizing acc with
  | nil => simp [afterReads]
  | cons j js ih =>
    rw [after_cons A _ _ _ _ _ _ _ _ _ (hv j),
      ih _ (fun u hu => hs u (List.mem_cons_of_mem j hu))]
    by_cases h : ∃ u ∈ js, x ∈ A.items D .broadcast k u i
    · obtain ⟨u,hu,hx⟩ := h
      simp [show ∃ u ∈ js, x ∈ A.items D .broadcast k u i from ⟨u,hu,hx⟩]
    · by_cases hx : x ∈ A.items D .broadcast k j i <;> simp_all

def tick (x : ℕ) (i : Fin p.n) := x / A.P + (A.height - ((A.route x).depth i + 1))

def up (D : ℕ) (a : Fin p.n → Values) (k : ℕ) (i : Fin p.n) (x : ℕ) :=
  if x < D ∧ tick A x i < k then
    (A.route x).subtotal (fun j => a j x) ((A.route x).depth i) i
  else a i x

lemma reduce_items (D k x : ℕ) (i j : Fin p.n) :
    x ∈ A.items D .reduce k j i ↔ x < D ∧ j ∈ (A.route x).children i ∧ tick A x i = k := by
  simp only [Routes.items,List.mem_filter,List.mem_range,Tree.children,Finset.mem_filter]
  have hs : A.sends .reduce k x j i = true ↔ j ∈ (A.route x).nodes ∧ j ≠ r ∧
      (A.route x).parent j = i ∧ x / A.P + (A.height - (A.route x).depth j) = k :=
    ⟨fun h => of_decide_eq_true h,fun h => decide_eq_true h⟩
  rw [hs]
  unfold tick
  constructor
  · rintro ⟨hx,hv,hn,hp,ht⟩
    have hl := (A.route x).parent_depth j hv hn
    rw [hp] at hl
    exact ⟨hx,⟨hv,hn,hp⟩,by rwa [hl]⟩
  · rintro ⟨hx,⟨hv,hn,hp⟩,ht⟩
    have hl := (A.route x).parent_depth j hv hn
    rw [hp] at hl
    exact ⟨hx,hv,hn,hp,by rwa [← hl]⟩

lemma subtotal_bound (a : Fin p.n → Values) (i : Fin p.n) (x : ℕ) :
    (A.route x).subtotal (fun j => a j x) ((A.route x).depth i) i ≤ ∑ j ∈ S, a j x := by
  apply Finset.sum_le_sum
  intro j _
  split <;> simp

lemma up_bounded (D : ℕ) (a : Fin p.n → Values) (q : ℕ)
    (ha : ∀ i ∉ S, ∀ x, a i x = 0) (ht : ∀ x < D, (∑ i ∈ S, a i x) < 2 ^ q)
    (k : ℕ) (i : Fin p.n) (x : ℕ) (hx : x < D) : up A D a k i x < 2 ^ q := by
  unfold up
  split
  · exact (subtotal_bound A a i x).trans_lt (ht x hx)
  · by_cases hi : i ∈ S
    · exact (Finset.single_le_sum (f := fun j => a j x) (fun _ _ => Nat.zero_le _) hi).trans_lt (ht x hx)
    · simp [ha i hi x]

lemma child_ready (D : ℕ) (a : Fin p.n → Values) (i j : Fin p.n) (x : ℕ)
    (ha : ∀ i ∉ S, ∀ x, a i x = 0) (hx : x < D) (hj : j ∈ (A.route x).children i) :
    up A D a (tick A x i) j x =
      (A.route x).subtotal (fun u => a u x) ((A.route x).depth i + 1) j := by
  obtain ⟨hv,hn,hp⟩ := Finset.mem_filter.mp hj
  have hd := (A.route x).parent_depth j hv hn
  rw [hp] at hd
  have hh := GraceRouting.depth_le_height A hv
  by_cases h : (A.route x).depth j < A.height
  · have hlt : tick A x j < tick A x i := by unfold tick; omega
    simp [up,hx,hlt,hd]
  · have hc : (A.route x).children j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hm,hr,hpar⟩ := Finset.mem_filter.mp hu
      have hl := (A.route x).parent_depth u hm hr
      have hu' : (A.route x).depth u ≤ A.height := GraceRouting.depth_le_height A hm
      rw [hpar] at hl
      omega
    rw [hd,GraceTree.sum_children _ _ j _ rfl,hc]
    simp only [Finset.sum_empty,add_zero]
    unfold up
    have heq : tick A x j = tick A x i := by unfold tick; omega
    simp [heq]
    by_cases hs : j ∈ S
    · simp [hs]
    · simp [hs,ha j hs]

lemma up_step (D q k : ℕ) (a : Fin p.n → Values)
    (ha : ∀ i ∉ S, ∀ x, a i x = 0) (ht : ∀ x < D, (∑ j ∈ S, a j x) < 2 ^ q)
    (i : Fin p.n) : afterReads A D q .reduce k (up A D a k) i (List.finRange p.n)
      (up A D a k i) = up A D a (k+1) i := by
  funext x
  rw [reduce_read A _ _ _ _ _ _ _ _ (fun j y hy =>
    up_bounded A D a q ha ht k j y ((reduce_items A D k y i j).mp hy).1),
    ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  simp only [reduce_items]
  by_cases he : x < D ∧ tick A x i = k
  · obtain ⟨hx,rfl⟩ := he
    simp only [hx, true_and, and_true, up, lt_self_iff_false, ite_false,
      Nat.lt_succ_self, ite_true]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun j => j ∈ (A.route x).children i) = (A.route x).children i := by ext; simp
    rw [hf, GraceTree.sum_children _ _ i _ rfl]
    apply congrArg₂ (· + ·)
    · by_cases hi : i ∈ S <;> simp_all
    · apply Finset.sum_congr rfl
      intro j hj
      simpa [up,hx] using child_ready A D a i j x ha hx hj
  · have hnone (j : Fin p.n) : ¬ (x < D ∧ j ∈ (A.route x).children i ∧ tick A x i = k) :=
      fun hh => he ⟨hh.1,hh.2.2⟩
    simp only [hnone,ite_false,Finset.sum_const_zero,add_zero,up]
    have hiff : (x < D ∧ tick A x i < k) ↔ (x < D ∧ tick A x i < k+1) := by omega
    simp only [hiff]

lemma up_root (D : ℕ) (a : Fin p.n → Values) (x : ℕ) (hx : x < D) :
    up A D a (A.slots D) r x = ∑ j ∈ S, a j x := by
  have hq : x / A.P ≤ D / A.P := Nat.div_le_div_right hx.le
  have hlt : tick A x r < A.slots D := by unfold tick Routes.slots; omega
  simp [up,hx,hlt,(A.route x).depth_root,GraceTree.root_total]

def down (D : ℕ) (z : Values) (k : ℕ) (i : Fin p.n) (x : ℕ) :=
  if i = r ∨ (x < D ∧ i ∈ (A.route x).nodes ∧ A.slot .broadcast x i < k) then z x else 0

lemma broadcast_items (D k x : ℕ) (i j : Fin p.n) :
    x ∈ A.items D .broadcast k j i ↔
      x < D ∧ i ∈ (A.route x).nodes ∧ i ≠ r ∧ (A.route x).parent i = j ∧ A.slot .broadcast x i = k := by
  simp only [Routes.items,List.mem_filter,List.mem_range]
  exact and_congr_right fun _ => ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

lemma down_step (D q k : ℕ) (z : Values) (hz : ∀ x < D, z x < 2 ^ q)
    (i : Fin p.n) : afterReads A D q .broadcast k (down A D z k) i (List.finRange p.n)
      (down A D z k i) = down A D z (k+1) i := by
  funext x
  rw [broadcast_read A _ _ _ _ _ _ _ _ (z x)]
  · simp only [broadcast_items,List.mem_finRange,true_and,exists_and_left,exists_eq_left']
    unfold down
    by_cases h : i = r
    · simp [h]
    · by_cases hv : i ∈ (A.route x).nodes <;> by_cases hx : x < D <;> simp_all <;>
        split_ifs <;> omega
  · intro j y hy
    have hx := ((broadcast_items A D k y i j).mp hy).1
    unfold down
    split
    · exact hz y hx
    · positivity
  · intro j _ h
    obtain ⟨hx,hi,hr,hp,hk⟩ := (broadcast_items A D k x i j).mp h
    have hj := (A.route x).parent_mem i hi
    have hd := (A.route x).parent_depth i hi hr
    rw [hp] at hj hd
    by_cases h : j = r
    · simp [down,h]
    · have hh := (A.route x).parent_depth j hj h
      have ht : A.slot .broadcast x j < k := by
        rw [← hk]
        simp only [Routes.slot]
        omega
      simp [down,hx,hj,ht]

lemma down_terminal (D : ℕ) (z : Values) (i : Fin p.n) (hi : i ∈ S) (x : ℕ) (hx : x < D) :
    down A D z (A.slots D) i x = z x := by
  have hm := (A.route x).terminals hi
  simp [down,hx,hm,GraceRouting.slot_lt A hx .broadcast hm]

end LongTails.Proofs.GraceRoutedValues
