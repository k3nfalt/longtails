import LongTails.Algorithms.GraceRouting
import LongTails.Proofs.GracePacket
import LongTails.Proofs.GraceTree

namespace LongTails.Proofs.GraceRouting

open LongTails.Algorithms.GraceRouting
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.GraceTree

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n} (A : Routes p S r)

lemma packet_length (q : ℕ) (xs : List ℕ) (values : Values) :
    (pack q xs values).length = xs.length * q := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih =>
    change (_ ++ pack q xs values).length = _
    rw [List.length_append, GracePacket.word_length, ih]
    simp [Nat.add_mul, Nat.add_comm]

lemma packet_contents (phase : Phase) (q : ℕ) (xs : List ℕ) (values : Values)
    (hn : xs.Nodup) (hv : ∀ x ∈ xs, values x < 2 ^ q) (tail : List Bool) (acc : Values) :
    unpack phase q xs (pack q xs values ++ tail) acc =
      fun x => if x ∈ xs then
        match phase with | .reduce => acc x + values x | .broadcast => values x
      else acc x := by
  induction xs generalizing acc with
  | nil => simp [unpack]
  | cons x xs ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hn
    change unpack phase q (x :: xs)
      ((LongTails.Algorithms.GracePacket.word q (values x) ++ pack q xs values) ++ tail) acc = _
    rw [List.append_assoc]
    unfold unpack
    rw [GracePacket.read_word q _ (hv x (by simp))]
    have hd : List.drop q (LongTails.Algorithms.GracePacket.word q (values x) ++
        (pack q xs values ++ tail)) = pack q xs values ++ tail := by
      conv_lhs => arg 1; rw [← GracePacket.word_length q (values x)]
      exact List.drop_left
    rw [hd, ih hnd (fun j hj => hv j (List.mem_cons_of_mem _ hj))]
    funext j
    by_cases he : j = x
    · subst j; cases phase <;> simp [hnot]
    · simp [he]

lemma depth_le_height {a : Fin A.P} {v : Fin p.n} (hv : v ∈ (A.tree a).nodes) :
    (A.tree a).depth v ≤ A.height :=
  (Finset.le_sup (f := (A.tree a).depth) hv).trans (Finset.le_sup (f := fun b => (A.tree b).nodes.sup (A.tree b).depth) (Finset.mem_univ a))

lemma height_lt_workers : A.height < p.n := by
  rw [Routes.height, Finset.sup_lt_iff (by exact p.n.pos)]
  intro a _
  rw [Finset.sup_lt_iff (by exact p.n.pos)]
  exact fun v hv => GraceTree.depth_lt_workers (A.tree a) v hv

lemma sends_edge {phase : Phase} {k x : ℕ} {i j : Fin p.n} (h : A.sends phase k x i j) :
    p.G.Adj i j := by
  cases phase with
  | reduce =>
    have h := of_decide_eq_true h
    dsimp only [source, target] at h
    exact h.2.2.1 ▸ (A.route x).parent_edge i h.1 h.2.1
  | broadcast =>
    have h := of_decide_eq_true h
    dsimp only [source, target] at h
    exact h.2.2.1 ▸ ((A.route x).parent_edge j h.1 h.2.1).symm

lemma slot_lt {D x : ℕ} (hx : x < D) (phase : Phase) {v : Fin p.n}
    (hv : v ∈ (A.route x).nodes) : A.slot phase x v < A.slots D := by
  have hd : x / A.P ≤ D / A.P := Nat.div_le_div_right hx.le
  have hh : (A.route x).depth v ≤ A.height := depth_le_height A hv
  cases phase <;> simp only [Routes.slot, Routes.slots] <;> omega

lemma items_load (D : ℕ) (phase : Phase) (k : ℕ) (i j : Fin p.n) :
    (A.items D phase k i j).length ≤ (A.linkLanes i j).card := by
  classical
  let xs := A.items D phase k i j
  have hn : xs.Nodup := List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hn]
  have facts {x : ℕ} (hx : x ∈ xs.toFinset) :
      A.lane x ∈ A.linkLanes i j ∧ A.slot phase x (source (p := p) phase i j) = k := by
    have hs := (List.mem_filter.mp (List.mem_toFinset.mp hx)).2
    have ht := of_decide_eq_true hs
    cases phase with
    | reduce => exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inl ⟨ht.1, ht.2.1, ht.2.2.1⟩⟩, ht.2.2.2⟩
    | broadcast => exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr ⟨ht.1, ht.2.1, ht.2.2.1⟩⟩, ht.2.2.2⟩
  refine Finset.card_le_card_of_injOn A.lane (fun _ hx => (facts hx).1) ?_
  intro x hx y hy hxy
  have hk := (facts hx).2.trans (facts hy).2.symm
  have ht : A.route x = A.route y := congrArg A.tree hxy
  have hquot : x / A.P = y / A.P := by
    simp only [Routes.slot, ht, Nat.add_right_cancel_iff] at hk
    exact hk
  have hmod : x % A.P = y % A.P := congrArg Fin.val hxy
  rw [← Nat.div_add_mod' x (A.P : ℕ), ← Nat.div_add_mod' y (A.P : ℕ), hquot, hmod]

lemma lanes_symm (i j : Fin p.n) : A.linkLanes i j = A.linkLanes j i := by
  ext a
  simp [Routes.linkLanes, or_comm]

lemma link_time (q : ℕ) {i j : Fin p.n} (he : p.G.Adj i j)
    (hs : p.b i j = p.b j i) :
    ((q + DistributedTemplate.clockBits : ℕ) : DistributedTemplate.Time) *
      (A.linkLanes i j).card / p.b i j ≤ A.frameTime q := by
  have bound (e : LongTails.Algorithms.GraceGraph.Link p) :
      ((q + DistributedTemplate.clockBits : ℕ) : DistributedTemplate.Time) *
        (A.linkLanes e.val.1 e.val.2).card / p.b e.val.1 e.val.2 ≤ A.frameTime q :=
    Finset.le_sup (f := fun e : LongTails.Algorithms.GraceGraph.Link p =>
      ((q + DistributedTemplate.clockBits : ℕ) : DistributedTemplate.Time) *
        (A.linkLanes e.val.1 e.val.2).card / p.b e.val.1 e.val.2) (Finset.mem_univ e)
  rcases lt_or_gt_of_ne he.ne with hij | hji
  · exact bound ⟨(i,j),hij,he⟩
  · rw [lanes_symm A i j, hs]; exact bound ⟨(j,i),hji,he.symm⟩

lemma wire_time (D q : ℕ) (phase : Phase) (k : ℕ) (i j : Fin p.n) (values : Values)
    (hpos : (A.items D phase k i j) ≠ [])
    (hs : p.b i j = p.b j i) :
    (((pack q (A.items D phase k i j) values ++
        List.replicate DistributedTemplate.clockBits false).length : ℕ) : DistributedTemplate.Time) /
      p.b i j ≤ A.frameTime q := by
  let xs := A.items D phase k i j
  have hlen : 1 ≤ xs.length := List.length_pos_iff.mpr hpos
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hpos
  have he := sends_edge A (List.mem_filter.mp hx).2
  have hc : xs.length * q + DistributedTemplate.clockBits ≤
      (q + DistributedTemplate.clockBits) * (A.linkLanes i j).card := by
    calc
      _ ≤ q * xs.length + DistributedTemplate.clockBits * xs.length := by
        rw [Nat.mul_comm q]
        exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left DistributedTemplate.clockBits hlen) _
      _ ≤ _ := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_left _ (items_load A ..)
  rw [List.length_append, List.length_replicate, packet_length]
  refine le_trans ?_ (link_time A q he hs)
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast hc

end LongTails.Proofs.GraceRouting
