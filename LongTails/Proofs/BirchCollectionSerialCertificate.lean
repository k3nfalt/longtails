import LongTails.Algorithms.BirchCollectionBatches
import LongTails.Proofs.BirchCollectionReset
import LongTails.Proofs.BirchCollectionOrdering

namespace LongTails.Proofs.BirchCollectionSerialCertificate

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionReset

structure MainData (s : TraceState) (B rounds : ℕ) : Prop where
  states : s.nextState = rounds + 1
  directions : s.nextDirection = rounds
  markers : s.markers = List.range (rounds + 1)
  history : ∀ k ≤ rounds, (s.states k).history = range k
  direction : ∀ k < rounds, (s.directions k).source = k ∧ (s.directions k).target = k + 1 ∧
    (s.directions k).history = range k ∧ (s.directions k).refresh = 1 ∧
    (s.directions k).movement = 1 ∧ (s.directions k).raw.length = B

lemma vanilla_label (K n : ℕ) (hn : n < K) : (vanillaOrdering K).label n = n := by
  have hi : n < (List.range K).length := by simpa using hn
  simp [vanillaOrdering, LongTails.Setups.BirchCollections.Ordering.label,
    List.getElem?_eq_getElem hi]

lemma serial_history (s : TraceState) (B K n : ℕ) (hs : MainData s B K) :
    (vanillaOrdering K).history s n = range n := by
  unfold LongTails.Setups.BirchCollections.Ordering.history
  rw [show (vanillaOrdering K).labels.length = K by simp [vanillaOrdering]]
  split
  · rename_i hn
    rw [vanilla_label K n hn, (hs.direction n hn).2.2.1]
    ext j
    simp only [mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · rintro ⟨hj, hj'⟩
      rwa [vanilla_label K j hj] at hj'
    · intro hj
      have hjK := hj.trans hn
      exact ⟨hjK, by simpa only [vanilla_label K j hjK] using hj⟩
  · rfl

lemma serial_order_valid (s : TraceState) (B K : ℕ) (hs : MainData s B K) (hK : 0 < K) :
    (vanillaOrdering K).Valid s K := by
  refine ⟨by simpa [vanillaOrdering] using hK, List.nodup_range,
    by simp [hs.markers], rfl, by simp [vanillaOrdering], fun _ _ => Nat.lt_succ_self _, ?_, ?_, ?_⟩
  · intro n hn
    have hn' : n < K := by simpa [vanillaOrdering] using hn
    rw [vanilla_label K n hn', hs.directions]
    exact hn'
  · intro k hk
    have hindex : k < (List.range (K + 1)).length := by simpa using Nat.lt_succ_of_le hk
    rw [hs.markers, List.getElem?_eq_getElem hindex, List.getElem_range, Option.getD_some, hs.history k hk]
    change range k = (range k).image (vanillaOrdering K).label
    ext j
    constructor
    · intro hj
      exact mem_image.mpr ⟨j, hj, vanilla_label K j ((mem_range.mp hj).trans_le hk)⟩
    · intro hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      simpa only [vanilla_label K i ((mem_range.mp hi).trans_le hk)] using hi
  · intro n
    rw [serial_history s B K n hs]

lemma serial_step_data (s : TraceState) (B K n : ℕ) (hs : MainData s B K) (hn : n < K)
    (hraw : RawLedger s) (hcompleted : CompletedLedger s) :
    (vanillaOrdering K).refresh s n = 1 ∧ (vanillaOrdering K).movement s n = 1 ∧
      ((vanillaOrdering K).raw s n).card = B := by
  have hn' : n < (vanillaOrdering K).labels.length := by simpa [vanillaOrdering] using hn
  obtain ⟨_, _, _, hrefresh, hmovement, hlength⟩ := hs.direction n hn
  have hnd := (completed_raw s hraw hcompleted n (by rw [hs.directions]; exact hn)).1
  simp only [LongTails.Setups.BirchCollections.Ordering.refresh,
    LongTails.Setups.BirchCollections.Ordering.movement, LongTails.Setups.BirchCollections.Ordering.raw,
    ite_eq_left hn', vanilla_label K n hn, hrefresh, hmovement, true_and]
  rw [List.toFinset_card_of_nodup hnd, hlength]

lemma serial_structural (workers B K D : ℕ) (es : List Event) (hK : 0 < K)
    (hv : ValidFrom workers {} es) (htrace : MainData (run es) B K)
    (hbudget : (run es).nextRaw ≤ B * K + D) :
    Structural (run es) (vanillaOrdering K) { vanillaControls with waste := D } K B := by
  let s := run es
  let o := vanillaOrdering K
  let c := { vanillaControls with waste := D }
  have hraw := rawLedger_run workers es hv
  have hcompleted := completedLedger_run workers es hv
  have horder := serial_order_valid s B K htrace hK
  have hK' : o.labels.length = K := List.length_range
  have hdata (n : ℕ) (hn : n < o.labels.length) :=
    serial_step_data s B K n htrace (hK' ▸ hn) hraw hcompleted
  have hledger := ordering_raw_ledger s o K hraw hcompleted horder
  have haccepted : (∑ n ∈ range o.labels.length, (o.raw s n).card) = B * K := by
    calc
      _ = ∑ _ ∈ range o.labels.length, B :=
        sum_congr rfl fun n hn => (hdata n (mem_range.mp hn)).2.2
      _ = _ := by simp [hK', Nat.mul_comm]
  have hwaste : s.nextRaw - ((range o.labels.length).biUnion (o.raw s)).card ≤
      c.waste := by
    rw [haccepted] at hledger
    change s.nextRaw - _ ≤ D
    have hq : s.nextRaw ≤ B * K + D := hbudget
    omega
  have hmass (k : ℕ) (hk : k < K) :
      (∑ n ∈ Ico (o.cut k) (o.cut (k + 1)), o.movement s n) = 1 := by
    change ∑ n ∈ Ico k (k + 1), o.movement s n = 1
    rw [Nat.Ico_succ_singleton, sum_singleton]
    exact (hdata k (hK'.symm ▸ hk)).2.1
  change Structural s (resetOrdering o) c K B
  refine reset_structural s o c K B horder (by norm_num [Controls.Valid, c, vanillaControls])
    (fun n hn => (hdata n hn).1) ?_ ?_ ?_ ?_ ?_ hwaste
  · intro n _
    change n ≤ n ∧ range n ⊆ o.history s n ∧ (∑ j ∈ Ico n n, o.movement s j) ≤ 1 / 4
    rw [serial_history s B K n htrace]
    norm_num
  · intro k hk
    rw [hmass k hk]
    exact le_rfl
  · intro k hk
    rw [hmass k hk]
    exact le_rfl
  · intro n hn
    rw [(hdata n hn).2.2]
  · intro n hn
    rw [(hdata n hn).2.2, (hdata n hn).2.1]
    simp [c, vanillaControls]

end LongTails.Proofs.BirchCollectionSerialCertificate
