import LongTails.Algorithms.GraceGraph
import LongTails.Algorithms.GraceRouting
import LongTails.Proofs.GracePacketPipeline
import LongTails.Proofs.GraceFractionalPacking
import LongTails.Proofs.GraceSteinerPrices

namespace LongTails.Proofs.GraceGraphPacking

open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.GraceGraph
open LongTails.Algorithms.GraceTree
open GraceSteinerCuts

abbrev ends (p : Params) : Endpoints (Fin p.n) (Link p) := ⟨fun e => e.val.1, fun e => e.val.2⟩

lemma cuts_iff (p : Params) (S C : Finset (Fin p.n)) :
    C ∈ cuts p S ↔ Splits S C := by simp [cuts, Splits, Finset.Nonempty]

lemma cut_coe (p : Params) (C : Finset (Fin p.n)) :
    (LongTails.Algorithms.GraceGraph.cut p C : ℝ) =
      GraceSteinerCuts.cut (ends p) (fun e => (capacity p e : ℝ)) C := by
  unfold LongTails.Algorithms.GraceGraph.cut GraceSteinerCuts.cut
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e.val.1 ∈ C ↔ e.val.2 ∈ C <;> simp [Crosses, he]

lemma alpha_le (p : Params) (S C : Finset (Fin p.n)) (h : Splits S C) :
    α p S ≤ LongTails.Algorithms.GraceGraph.cut p C := by
  have hm := Finset.mem_image_of_mem (LongTails.Algorithms.GraceGraph.cut p) ((cuts_iff ..).mpr h)
  unfold α
  dsimp only
  rw [dite_eq_left (show _ from ⟨_,hm⟩)]
  exact Finset.min'_le _ _ hm

lemma graph_connects (p : Params) (hG : p.G.Connected) (S : Finset (Fin p.n)) :
    Connects (ends p) S Finset.univ := by
  intro C hC
  by_contra! hn
  have adj {i j : Fin p.n} (hadj : p.G.Adj i j) : i ∈ C ↔ j ∈ C := by
    rcases lt_or_gt_of_ne hadj.ne with hl | hl
    · let e : Link p := ⟨(i,j),hl,hadj⟩
      exact Classical.not_not.mp (hn e (Finset.mem_univ _))
    · let e : Link p := ⟨(j,i),hl,hadj.symm⟩
      exact Iff.symm (Classical.not_not.mp (hn e (Finset.mem_univ _)))
  obtain ⟨⟨i, _, hiC⟩, ⟨j, _, hjC⟩⟩ := hC
  have walk {x y : Fin p.n} (w : p.G.Walk x y) : x ∈ C ↔ y ∈ C := by
    induction w with
    | nil => rfl
    | cons h _ ih => exact (adj h).trans ih
  obtain ⟨w⟩ := hG i j
  exact hjC ((walk w).mp hiC)

lemma alpha_pos (p : Params) {S : Finset (Fin p.n)} (hsize : 1 < S.card)
    (hG : p.G.Connected) (hb : ∀ i j, p.G.Adj i j → 0 < p.b i j) : 0 < α p S := by
  classical
  let cutVal := LongTails.Algorithms.GraceGraph.cut p
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨j,hj,hne⟩ := Finset.exists_mem_ne hsize i
  have hs : Splits S {i} := ⟨⟨i,hi,by simp⟩,⟨j,hj,by simpa using hne⟩⟩
  have hm := Finset.mem_image_of_mem cutVal ((cuts_iff ..).mpr hs)
  let vals := (cuts p S).image cutVal
  have hval : vals.Nonempty := ⟨_,hm⟩
  change 0 < (if h : vals.Nonempty then vals.min' h else 0)
  rw [dite_eq_left hval]
  obtain ⟨C, hC, he⟩ := Finset.mem_image.mp (vals.min'_mem hval)
  rw [← he]
  obtain ⟨e, _, hcross⟩ := graph_connects p hG S C ((cuts_iff ..).mp hC)
  have hed : ¬ (e.val.1 ∈ C ↔ e.val.2 ∈ C) := hcross
  have hcap := hb _ _ e.property.2
  change 0 < ∑ k : Link p, if (k.val.1 ∈ C ↔ k.val.2 ∈ C) then 0 else capacity p k
  apply Finset.sum_pos' (fun _ _ => zero_le)
  exact ⟨e, Finset.mem_univ _, by simpa [hed,capacity] using hcap⟩

abbrev Connector (p : Params) (S : Finset (Fin p.n)) :=
  {F : Finset (Link p) // Connects (ends p) S F}

lemma fractional_connectors (p : Params) {S : Finset (Fin p.n)}
    (hrate : 0 < α p S) :
    ∃ (m : ℕ+) (F : Fin m → Connector p S) (w : Fin m → ℝ), m ≤ Fintype.card (Link p) + 1 ∧
      (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∀ e : Link p,
        (∑ i, if e ∈ (F i).val then w i else 0) ≤ 2 * (capacity p e : ℝ) / (α p S : ℝ) := by
  classical
  let load (f : Connector p S) (e : Link p) : ℝ := if e ∈ f.val then 1 else 0
  let rate : ℝ := α p S
  have hrate' : 0 < rate := by exact_mod_cast hrate
  have price (c : Link p → ℝ) (hc : ∀ e, 0 ≤ c e) :
      ∃ f : Connector p S, ∑ e, load f e * c e ≤ ∑ e, (2 * (capacity p e : ℝ) / rate) * c e := by
    obtain ⟨F, hF, hcost⟩ := GraceSteinerPrices.price_bound (ends p) S .univ (Finset.subset_univ _)
      (by simp) (fun e => (capacity p e : ℝ)) c (fun _ => NNReal.coe_nonneg _) hc rate hrate'
      (fun C hC => by rw [← cut_coe]; exact_mod_cast alpha_le p S C hC)
    refine ⟨⟨F,hF⟩, ?_⟩
    have he : (∑ e, load ⟨F,hF⟩ e * c e) = ∑ e ∈ F, c e := by
      simp [load, ite_mul, Finset.sum_ite_mem]
    rw [he]
    have hr : (∑ e, (2 * (capacity p e : ℝ) / rate) * c e) =
        (2 * (∑ e, (capacity p e : ℝ) * c e)) / rate := by
      rw [Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hr]
    exact (le_div_iff₀ hrate').mpr (by simpa [mul_comm rate] using hcost)
  obtain ⟨m,F,w,hm,hw,hsum,hload⟩ := GraceFractionalPacking.packing_of_price_bound load _ price
  exact ⟨m,F,w,hm,hw,hsum,fun e => by simpa [load, mul_ite] using hload e⟩

lemma tree_of_connector (p : Params) {S : Finset (Fin p.n)} {r : Fin p.n} (hr : r ∈ S)
    (F : Connector p S) :
    ∃ T : Tree p S r, ∀ v ∈ T.nodes, v ≠ r →
      ∃ e ∈ F.val, GraceSteinerPruning.Joins (ends p) e v (T.parent v) := by
  obtain ⟨U,hSU,⟨b⟩⟩ := GraceSteinerPruning.exists_spanning hr F.property
  refine ⟨{
    nodes := U
    terminals := hSU
    parent := b.parent
    depth := b.depth
    root_mem := b.root_mem
    depth_root := b.depth_root
    parent_root := b.parent_root
    parent_mem := by
      intro v hv; by_cases he : v = r
      · simpa [he, b.parent_root] using b.root_mem
      · exact (b.branch _ hv he).1
    parent_edge := by
      intro v hv he
      obtain ⟨e, _, h | h⟩ := (b.branch v hv he).2.2
      · rw [← h.2, ← h.1]; exact e.property.2
      · rw [← h.1, ← h.2]; exact e.property.2.symm
    parent_depth := fun _ hv he => (b.branch _ hv he).2.1 }, ?_⟩
  exact fun v hv he => (b.branch v hv he).2.2

lemma link_unique (p : Params) (e f : Link p)
    (h : GraceSteinerPruning.Joins (ends p) f e.val.1 e.val.2 ∨
      GraceSteinerPruning.Joins (ends p) f e.val.2 e.val.1) : f = e := by
  have he := e.property.1
  have hf := f.property.1
  apply Subtype.ext
  apply Prod.ext <;> dsimp [GraceSteinerPruning.Joins, ends] at h <;> grind

lemma integral_routes (p : Params) {S : Finset (Fin p.n)} {r : Fin p.n}
    (hr : r ∈ S) (hrate : 0 < α p S) :
    ∃ (m : ℕ+) (A : LongTails.Algorithms.GraceRouting.Routes p S r),
      m ≤ Fintype.card (Link p) + 1 ∧ (m : ℕ) ≤ A.P ∧ ∀ e : Link p,
      ((A.linkLanes e.val.1 e.val.2).card : ℝ) ≤ 4 * m / (α p S : ℝ) * capacity p e := by
  classical
  obtain ⟨m,F,w,hm,hw,hsum,hload⟩ := fractional_connectors p hrate
  choose trees htrees using fun k => tree_of_connector p hr (F k)
  let c (i : Fin m) := ⌊2 * (m : ℝ) * w i⌋₊
  let Lanes := Σ i, Fin (c i)
  have hcard : Fintype.card Lanes = ∑ i, c i := by simp [Lanes, Fintype.card_sigma]
  have hcount : (m : ℕ) ≤ Fintype.card Lanes := by
    rw [hcard]
    simpa [c] using GracePacketPipeline.lane_count w hsum
  let P : ℕ+ := ⟨Fintype.card Lanes, m.pos.trans_le hcount⟩
  let index : Fin P ≃ Lanes := (Fintype.equivFin Lanes).symm
  let A : LongTails.Algorithms.GraceRouting.Routes p S r := ⟨P, fun k => trees (index k).1⟩
  refine ⟨m,A,hm,hcount,?_⟩
  intro e
  let allowed := Finset.univ.filter (fun k => e ∈ (F k).val)
  have uses {k : Fin P} (hk : k ∈ A.linkLanes e.val.1 e.val.2) : e ∈ (F (index k).1).val := by
    obtain ⟨hmem, hn, he⟩ | ⟨hmem, hn, he⟩ := (Finset.mem_filter.mp hk).2
    · obtain ⟨f, hf, hj⟩ := htrees (index k).1 _ hmem hn
      change (trees (index k).1).parent e.val.1 = e.val.2 at he
      exact link_unique p e f (Or.inl (he ▸ hj)) ▸ hf
    · obtain ⟨f, hf, hj⟩ := htrees (index k).1 _ hmem hn
      change (trees (index k).1).parent e.val.2 = e.val.1 at he
      exact link_unique p e f (Or.inr (he ▸ hj)) ▸ hf
  have bound : (A.linkLanes e.val.1 e.val.2).card ≤ ∑ i ∈ allowed, c i := by
    calc
      _ ≤ (Finset.univ.filter fun k : Fin P => e ∈ (F (index k).1).val).card :=
        Finset.card_le_card fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ k, uses hk⟩
      _ = ∑ z : Lanes, if e ∈ (F z.1).val then 1 else 0 := by
        rw [← index.sum_comp (fun z => if e ∈ (F z.1).val then (1 : ℕ) else 0)]
        simp
      _ = _ := by
        rw [Fintype.sum_sigma]
        simp [allowed, Finset.sum_filter]
        exact Finset.sum_congr rfl fun i _ => by by_cases h : e ∈ (F i).val <;> simp [h]
  have hsum' : (∑ k ∈ allowed, w k) ≤ 2 * (capacity p e : ℝ) / (α p S : ℝ) := by
    simpa [allowed, Finset.sum_filter] using hload e
  have hcap := GracePacketPipeline.link_load w (fun k => (hw k).le) allowed hsum'
  have hcap' : ((∑ i ∈ allowed, c i : ℕ) : ℝ) ≤
      2 * m / (α p S : ℝ) * (2 * (capacity p e : ℝ)) := by simpa [c] using hcap
  exact (Nat.cast_le.mpr bound).trans (hcap'.trans_eq (by ring))

end LongTails.Proofs.GraceGraphPacking
