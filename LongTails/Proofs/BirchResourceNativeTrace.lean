import LongTails.Proofs.BirchResourceNativePacket
import LongTails.Proofs.BirchResourceNativeCertificate

namespace LongTails.Proofs.BirchResourceNativeTrace

open Finset LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchResourceNative
open LongTails.Proofs.BirchResourceNativePacket
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchResourceNativeCertificate

structure Plan.Valid (p : Plan) (B K : ℕ) : Prop where
  zero : p.cut 0 = 0
  initial : p.cut 1 = 1
  strict : ∀ k < K, p.cut k < p.cut (k + 1)
  phase : ∀ n < p.cut K, p.phase n < K ∧ p.cut (p.phase n) ≤ n ∧ n < p.cut (p.phase n + 1)
  parent : ∀ n < p.cut K, ∀ j, p.parent n = some j → j < n ∧ p.phase j = p.phase n
  volume : ∀ n < p.cut K, 0 < p.accepted n ∧ p.accepted n ≤ p.paid n ∧ p.accepted n ≤ B
  reset : p.accepted 0 = B
  quota : ∀ k < K, ∑ n ∈ Ico (p.cut k) (p.cut (k + 1)), p.accepted n = B

lemma cut_le {p : Plan} {B K : ℕ} (h : Plan.Valid p B K) {k l : ℕ}
    (hkl : k ≤ l) (hl : l ≤ K) : p.cut k ≤ p.cut l := by
  induction l with
  | zero =>
    have he : k = 0 := by omega
    rw [he]
  | succ l ih =>
    by_cases he : k = l + 1
    · rw [he]
    · exact (ih (by omega) (by omega)).trans (h.strict l (by omega)).le

structure Prefix (p : Plan) (B : ℕ) (es : List Event) (n : ℕ) : Prop where
  legal : ValidFrom 1 {} es
  stateCount : (run es).nextState = 2 * n + 1
  directionCount : (run es).nextDirection = n
  work : (run es).nextRaw = ∑ j ∈ range n, p.paid j
  global : ∀ j ≤ n, ((run es).states (2 * j)).history = range j
  privateHead : ∀ j < n,
    range (p.cut (p.phase j)) ⊆ ((run es).states (2 * j + 1)).history ∧
      ((run es).states (2 * j + 1)).history ⊆ range (j + 1)
  direction : ∀ j < n,
    range (p.cut (p.phase j)) ⊆ ((run es).directions j).history ∧
      ((run es).directions j).history ⊆ range j ∧
      ((run es).directions j).refresh = refresh B j (p.accepted j) ∧
      ((run es).directions j).movement = movement B j (p.accepted j) ∧
      ((run es).directions j).raw.Nodup ∧ ((run es).directions j).raw.length = p.accepted j

lemma prefix_empty (p : Plan) (B : ℕ) : Prefix p B [] 0 := by
  refine ⟨trivial, rfl, rfl, by simp [run], ?_, ?_, ?_⟩
  · intro j hj
    have he : j = 0 := by omega
    subst j
    rfl
  · intro j hj
    omega
  · intro j hj
    omega

lemma source_history {p : Plan} {B K n : ℕ} {es : List Event}
    (hp : Plan.Valid p B K) (h : Prefix p B es n) (hn : n < p.cut K) :
    p.source n < (run es).nextState ∧
      range (p.cut (p.phase n)) ⊆ ((run es).states (p.source n)).history ∧
      ((run es).states (p.source n)).history ⊆ range n := by
  have hcut := (hp.phase n hn).2.1
  unfold Plan.source
  split
  · rw [h.global _ hcut]
    exact ⟨by rw [h.stateCount]; omega, Subset.rfl, range_mono hcut⟩
  · rename_i j hj
    obtain ⟨hle, hphase⟩ := hp.parent n hn j hj
    obtain ⟨hsub, hpast⟩ := h.privateHead j hle
    rw [hphase] at hsub
    exact ⟨by rw [h.stateCount]; omega, hsub, hpast.trans (range_mono (by omega))⟩

lemma gains {B n b : ℕ} (hB : 0 < B) (hb : b ≤ B) :
    refresh B n b ≤ 1 ∧ 0 ≤ movement B n b ∧ movement B n b ≤ refresh B n b := by
  by_cases hz : n = 0
  · simp [refresh, movement, hz]
    norm_num
  · simp only [refresh, movement, ite_eq_right hz]
    refine ⟨?_, by positivity, le_rfl⟩
    apply (div_le_iff₀ (by positivity)).2
    have hb' : (b : ℝ) ≤ B := Nat.cast_le.mpr hb
    linarith

lemma append_packet {p : Plan} {B K n : ℕ} {es : List Event}
    (hp : Plan.Valid p B K) (h : Prefix p B es n) (hB : 0 < B) (hn : n < p.cut K) :
    Prefix p B (doPacket p B es n) (n + 1) ∧
      (run (doPacket p B es n)).markers = (run es).markers := by
  let s := run es
  let b := p.accepted n
  let z := p.paid n - b
  let β := refresh B n b
  let w := movement B n b
  let q := packetCode s (p.source n) b z β w
  have hs : RetiredPast s := retired_past_fold 1 {} es (by simp [RetiredPast]) h.legal
  obtain ⟨hbound, hprefix, hpast⟩ := source_history hp h hn
  obtain ⟨hb, hpaid, hvol⟩ := hp.volume n hn
  obtain ⟨hβ, hw, hwb⟩ := gains hB hvol
  have hsc : s.nextState = 2 * n + 1 := h.stateCount
  have hdc : s.nextDirection = n := h.directionCount
  have ha : (s.states (s.nextState - 1)).history = range s.nextDirection := by
    rw [hsc, hdc, Nat.add_sub_cancel]
    exact h.global _ le_rfl
  have hpast' : (s.states (p.source n)).history ⊆ range s.nextDirection := hdc ▸ hpast
  have hv : run (doPacket p B es n) = q.foldl step s := List.foldl_append
  obtain ⟨hlegal, he⟩ := packet 1 s (p.source n) b z β w hs (by decide) hb hbound
    (by omega) hβ hw hwb ha hpast'
  refine ⟨⟨(valid_append _ _ _ _).2 ⟨h.legal, hlegal⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hv.trans rfl ▸ he.markers⟩
  · rw [hv, he.stateCount, hsc]
    omega
  · rw [hv, he.directionCount, hdc]
  · rw [hv, he.raw, h.work, sum_range_succ]
    change (∑ j ∈ range n, p.paid j) + p.accepted n + (p.paid n - p.accepted n) = _
    omega
  · intro j hj
    rw [hv]
    by_cases hz : j = n + 1
    · rw [hz, show 2 * (n + 1) = s.nextState + 1 by omega, he.publishedHistory, hdc]
    · rw [he.oldState _ (by omega)]
      exact h.global j (by omega)
  · intro j hj
    rw [hv]
    by_cases hz : j = n
    · subst j
      rw [← hsc, he.privateHistory, hdc]
      exact ⟨hprefix.trans (subset_insert _ _), insert_subset (mem_range.mpr (by omega))
        (hpast.trans (range_mono (by omega)))⟩
    · rw [he.oldState _ (by omega)]
      exact h.privateHead j (by omega)
  · intro j hj
    rw [hv]
    by_cases hz : j = n
    · subst j
      rw [← hdc, he.direction, hdc]
      exact ⟨hprefix, hpast, rfl, rfl, List.nodup_range', List.length_range'⟩
    · rw [he.oldDirection _ (by omega)]
      exact h.direction j (by omega)

lemma append_range {p : Plan} {B K n : ℕ} {es : List Event}
    (hp : Plan.Valid p B K) (h : Prefix p B es n) (hB : 0 < B)
    (q : ℕ) (hn : n + q ≤ p.cut K) :
    let out := (List.range' n q).foldl (doPacket p B) es
    Prefix p B out (n + q) ∧ (run out).markers = (run es).markers := by
  induction q generalizing n es with
  | zero =>
    exact ⟨h, rfl⟩
  | succ q ih =>
    obtain ⟨ha, hm⟩ := append_packet hp h hB (by omega)
    rw [List.range'_succ, List.foldl_cons]
    have hb := ih ha (by omega)
    rw [show n + (q + 1) = n + 1 + q by omega]
    exact ⟨hb.1, hb.2.trans hm⟩

structure Marked (p : Plan) (B : ℕ) (es : List Event) (k : ℕ) : Prop where
  prefixData : Prefix p B es (p.cut k)
  size : (run es).markers.length = k + 1
  last : (run es).markers.getLast?.getD 0 = 2 * p.cut k
  labels : ∀ j ≤ k, (run es).markers[j]?.getD 0 = 2 * p.cut j

lemma code_marked {p : Plan} {B K : ℕ} (hp : Plan.Valid p B K) (hB : 0 < B)
    (k : ℕ) (hk : k ≤ K) : Marked p B (code p B k) k := by
  induction k with
  | zero =>
    rw [code]
    refine ⟨?_, rfl, by simp [run, hp.zero], ?_⟩
    · rw [hp.zero]
      exact prefix_empty p B
    · intro j hj
      have he : j = 0 := by omega
      subst j
      simp [run, hp.zero]
  | succ k ih =>
    have hk' : k < K := by omega
    have h := ih hk'.le
    let es := code p B k
    let q := p.cut (k + 1) - p.cut k
    let out := (List.range' (p.cut k) q).foldl (doPacket p B) es
    let v := 2 * p.cut (k + 1)
    have hcut := (hp.strict k hk').le
    have he : p.cut k + q = p.cut (k + 1) := by dsimp [q]; omega
    have ht : p.cut (k + 1) ≤ p.cut K := cut_le hp hk le_rfl
    obtain ⟨ha, hm⟩ := append_range hp h.prefixData hB q (he.symm ▸ ht)
    rw [he] at ha
    have hmark : (Event.mark v).Valid 1 (run out) := by
      refine ⟨?_, ?_⟩
      · rw [ha.stateCount]
        dsimp [v]
        omega
      · rw [hm, h.last, ha.global _ hcut, ha.global _ le_rfl]
        exact range_mono hcut
    have hcode : code p B (k + 1) = out ++ [.mark v] := rfl
    have hr : run (code p B (k + 1)) = step (run out) (.mark v) := by
      rw [hcode]
      exact List.foldl_append
    have hvalid : ValidFrom 1 {} (code p B (k + 1)) := by
      rw [hcode]
      exact (valid_append _ _ _ _).2 ⟨ha.legal, hmark, trivial⟩
    have hmarks : (run (code p B (k + 1))).markers = (run es).markers ++ [v] := by
      rw [hr]
      change (run out).markers ++ [v] = _
      rw [hm]
    refine ⟨⟨hvalid, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hr]
      exact ha.stateCount
    · rw [hr]
      exact ha.directionCount
    · rw [hr]
      exact ha.work
    · rw [hr]
      exact ha.global
    · rw [hr]
      exact ha.privateHead
    · rw [hr]
      exact ha.direction
    · rw [hmarks, List.length_append, h.size]
      rfl
    · rw [hmarks]
      simp [v]
    · intro j hj
      rw [hmarks]
      by_cases he' : j = k + 1
      · subst j
        have hlen : (run es).markers.length = k + 1 := h.size
        rw [List.getElem?_append_right hlen.le, hlen, Nat.sub_self]
        rfl
      · rw [List.getElem?_append_left (by rw [h.size]; omega)]
        exact h.labels j (by omega)

open LongTails.Proofs.BirchCollectionOrdering (ordering_history_mem)

lemma profile {p : Plan} {B K : ℕ} (hp : Plan.Valid p B K) (hB : 0 < B) (hK : 0 < K) :
    PacketProfile (run (code p B K)) (ordering p K) K B := by
  let s := run (code p B K)
  let o := ordering p K
  have hs := code_marked hp hB K le_rfl
  have hl : o.labels.length = p.cut K := List.length_range
  have hn : 0 < p.cut K := by
    have h := cut_le hp (show 1 ≤ K by omega) le_rfl
    rw [hp.initial] at h
    omega
  have hid (j : ℕ) (hj : j < p.cut K) : o.label j = j := by
    have hi : j < (List.range (p.cut K)).length := by simpa using hj
    simp [o, ordering, LongTails.Setups.BirchCollections.Ordering.label, List.getElem?_eq_getElem hi]
  have hhist (j : ℕ) (hj : j < p.cut K) : o.history s j = (s.directions j).history := by
    ext i
    have hpast := (hs.prefixData.direction j hj).2.1
    rw [ordering_history_mem s o j i (hl.symm ▸ hj), hid j hj]
    constructor
    · rintro ⟨hi, h⟩
      rwa [hid i (hl ▸ hi)] at h
    · intro hi
      have hj' := (mem_range.mp (hpast hi)).trans hj
      exact ⟨hl.symm ▸ hj', by rw [hid i hj']; exact hi⟩
  have hraw (j : ℕ) (hj : j < p.cut K) : (o.raw s j).card = p.accepted j := by
    have he := (hs.prefixData.direction j hj).2.2.2.2
    unfold Ordering.raw
    rw [hid j hj, List.toFinset_card_of_nodup he.1, he.2]
  have href (j : ℕ) (hj : j < p.cut K) :
      o.refresh s j = refresh B j (p.accepted j) := by
    unfold Ordering.refresh
    rw [ite_eq_left (hl.symm ▸ hj), hid j hj]
    exact (hs.prefixData.direction j hj).2.2.1
  have hmov (j : ℕ) (hj : j < p.cut K) :
      o.movement s j = movement B j (p.accepted j) := by
    unfold Ordering.movement
    rw [ite_eq_left (hl.symm ▸ hj), hid j hj]
    exact (hs.prefixData.direction j hj).2.2.2.1
  refine ⟨?_, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_,
    hp.initial, ?_, ?_, ?_, ?_⟩
  · refine ⟨hl.symm ▸ hn, List.nodup_range, hs.size, hp.zero, hl.symm, hp.strict, ?_, ?_, ?_⟩
    · intro j hj
      rw [hid j (hl ▸ hj), hs.prefixData.directionCount]
      exact hl ▸ hj
    · intro k hk
      rw [hs.labels k hk, hs.prefixData.global _ (cut_le hp hk le_rfl)]
      have hlabel (j : ℕ) (hj : j ∈ range (p.cut k)) : o.label j = j :=
        hid j ((mem_range.mp hj).trans_le (cut_le hp hk le_rfl))
      ext i
      constructor
      · intro hi
        exact mem_image.mpr ⟨i, hi, hlabel i hi⟩
      · rintro hi
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
        rwa [hlabel j hj]
    · intro j
      by_cases hj : j < o.labels.length
      · rw [hhist j (hl ▸ hj)]
        exact (hs.prefixData.direction j (hl ▸ hj)).2.1
      · rw [Ordering.history, ite_eq_right hj]
  · rw [href 0 hn]
    simp [refresh]
  · rw [hmov 0 hn]
    simp [movement]
  · rw [hraw 0 hn, hp.reset]
  · intro j hj
    have he := hp.phase j (hl ▸ hj)
    exact ⟨p.phase j, he.1, rfl, he.2⟩
  · intro j hj
    rw [hhist j (hl ▸ hj)]
    exact (hs.prefixData.direction j (hl ▸ hj)).1
  · intro j hj hj'
    have he := hp.phase j (hl ▸ hj)
    have hp' : 0 < p.phase j := by
      by_contra! hz
      have hz' : p.phase j = 0 := by omega
      rw [hz', hp.initial] at he
      omega
    change 0 < p.cut (p.phase j)
    have h := cut_le hp hp' he.1.le
    rw [hp.initial] at h
    omega
  · intro k hk
    calc
      _ = ∑ j ∈ Ico (p.cut k) (p.cut (k + 1)), p.accepted j := by
        apply sum_congr rfl
        intro j hj
        exact hraw j ((mem_Ico.mp hj).2.trans_le (cut_le hp (by omega) le_rfl))
      _ = B := hp.quota k hk
  · intro j hj hj'
    rw [href j (hl ▸ hj), hmov j (hl ▸ hj), hraw j (hl ▸ hj)]
    simp [refresh, movement, Nat.ne_of_gt hj']

end LongTails.Proofs.BirchResourceNativeTrace
