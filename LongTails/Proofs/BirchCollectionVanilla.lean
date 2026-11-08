import LongTails.Proofs.BirchCollectionBatches
import LongTails.Proofs.BirchCollectionReset
import LongTails.Theorems.BirchCollections

namespace LongTails.Proofs.BirchCollectionVanilla

open Finset OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionBatches
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionReset
open LongTails.Proofs.BirchCollectionSuccess

structure VanillaTrace (s : TraceState) (B K : ℕ) : Prop where
  raw : s.nextRaw = B * K
  collections : s.nextCollection = K
  states : s.nextState = K + 1
  directions : s.nextDirection = K
  markers : s.markers = List.range (K + 1)
  history : ∀ k ≤ K, (s.states k).history = range k
  direction : ∀ k < K, s.directions k =
    { collection := k, source := k, target := k + 1, history := range k,
      refresh := 1, movement := 1, raw := List.range' (B * k) B }

lemma vanilla_trace (workers B K : ℕ) (hw : 0 < workers) (hB : 0 < B) :
    ValidFrom workers {} (vanillaEvents B K) ∧ VanillaTrace (run (vanillaEvents B K)) B K := by
  induction K with
  | zero =>
      refine ⟨trivial, ⟨by simp [vanillaEvents, run], rfl, rfl, rfl, rfl, ?_, ?_⟩⟩
      · intro k hk
        have : k = 0 := by omega
        subst k
        rfl
      · intro k hk
        omega
  | succ K ih =>
      obtain ⟨hv, he⟩ := ih
      let es := vanillaEvents B K
      let s := run es
      let next := batchAndMark s 0 K (List.replicate B 0)
      have hret : RetiredPast s := retired_past_fold workers {} es (by simp [RetiredPast]) hv
      have hlast : s.markers.getLast?.getD 0 = K := by
        change (run es).markers.getLast?.getD 0 = K
        rw [he.markers, List.range_succ]
        simp
      have hsource : K < s.nextState := by change K < (run es).nextState; rw [he.states]; omega
      obtain ⟨hn, hf⟩ := batch_and_mark workers s 0 K (List.replicate B 0)
        hret hw hsource (by simpa using hB) (by simp [hw])
        (by rw [hlast]) (by simpa only [hlast] using hsource)
      have hvalid : ValidFrom workers {} (vanillaEvents B (K + 1)) :=
        (valid_append workers {} es next).2 ⟨hv, hn⟩
      refine ⟨hvalid, ?_⟩
      change VanillaTrace (run (es ++ next)) B (K + 1)
      rw [show run (es ++ next) = next.foldl step s from List.foldl_append]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hf.raw, List.length_replicate]
        change (run es).nextRaw + B = B * (K + 1)
        rw [he.raw, Nat.mul_succ]
      · exact hf.collectionCount.trans (congrArg (· + 1) he.collections)
      · exact hf.stateCount.trans (congrArg (· + 1) he.states)
      · exact hf.directionCount.trans (congrArg (· + 1) he.directions)
      · rw [hf.markers]
        change (run es).markers ++ [(run es).nextState] = _
        rw [he.markers, he.states]
        exact List.range_succ.symm
      · intro k hk
        rcases eq_or_lt_of_le hk with hEq | hk
        · subst k
          have htarget : s.nextState = K + 1 := he.states
          rw [← htarget, hf.state]
          change insert (run es).nextDirection ((run es).states K).history = _
          rw [he.directions, he.history K le_rfl, htarget, Finset.range_add_one]
        · have hk' : k ≤ K := by omega
          rw [hf.oldState k (hk'.trans_lt hsource)]
          exact he.history k hk'
      · intro k hk
        have hle : k ≤ K := by omega
        rcases eq_or_lt_of_le hle with hEq | hk'
        · subst k
          have hd : s.nextDirection = K := he.directions
          rw [← hd, hf.direction]
          rw [show s.nextCollection = K from he.collections,
            show s.nextState = K + 1 from he.states,
            show (s.states K).history = range K from he.history K le_rfl,
            show s.nextRaw = B * K from he.raw, List.length_replicate, hd]
        · have hkd : k < s.nextDirection := by change k < (run es).nextDirection; rw [he.directions]; exact hk'
          rw [hf.oldDirection k hkd]
          exact he.direction k hk'

lemma vanilla_label (K n : ℕ) (hn : n < K) : (vanillaOrdering K).label n = n := by
  have hi : n < (List.range K).length := by simpa using hn
  simp [vanillaOrdering, LongTails.Setups.BirchCollections.Ordering.label,
    List.getElem?_eq_getElem hi]

lemma vanilla_history (s : TraceState) (B K n : ℕ) (hs : VanillaTrace s B K) :
    (vanillaOrdering K).history s n = range n := by
  unfold LongTails.Setups.BirchCollections.Ordering.history
  rw [show (vanillaOrdering K).labels.length = K by simp [vanillaOrdering]]
  split
  · rename_i hn
    rw [vanilla_label K n hn, hs.direction n hn]
    ext j
    simp only [mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · rintro ⟨hj, hj'⟩
      rwa [vanilla_label K j hj] at hj'
    · intro hj
      have hjK := hj.trans hn
      exact ⟨hjK, by simpa only [vanilla_label K j hjK] using hj⟩
  · rfl

lemma vanilla_order_valid (s : TraceState) (B K : ℕ) (hs : VanillaTrace s B K) (hK : 0 < K) :
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
    rw [vanilla_history s B K n hs]

lemma vanilla_step_data (s : TraceState) (B K n : ℕ) (hs : VanillaTrace s B K) (hn : n < K) :
    (vanillaOrdering K).refresh s n = 1 ∧ (vanillaOrdering K).movement s n = 1 ∧
      ((vanillaOrdering K).raw s n).card = B := by
  have hn' : n < (vanillaOrdering K).labels.length := by simpa [vanillaOrdering] using hn
  simp only [LongTails.Setups.BirchCollections.Ordering.refresh,
    LongTails.Setups.BirchCollections.Ordering.movement, LongTails.Setups.BirchCollections.Ordering.raw,
    ite_eq_left hn', vanilla_label K n hn, hs.direction n hn, true_and]
  rw [List.toFinset_card_of_nodup List.nodup_range', List.length_range']

lemma vanilla_structural (workers B K : ℕ) (hw : 0 < workers) (hB : 0 < B) (hK : 0 < K) :
    Structural (run (vanillaEvents B K)) (vanillaOrdering K) vanillaControls K B := by
  let es := vanillaEvents B K
  let s := run es
  let o := vanillaOrdering K
  obtain ⟨hv, htrace⟩ := vanilla_trace workers B K hw hB
  have horder := vanilla_order_valid s B K htrace hK
  have hK' : o.labels.length = K := List.length_range
  have hdata (n : ℕ) (hn : n < o.labels.length) :=
    vanilla_step_data s B K n htrace (hK' ▸ hn)
  have hledger := ordering_raw_ledger s o K (rawLedger_run workers es hv)
    (completedLedger_run workers es hv) horder
  have haccepted : (∑ n ∈ range o.labels.length, (o.raw s n).card) = B * K := by
    calc
      _ = ∑ _ ∈ range o.labels.length, B :=
        sum_congr rfl fun n hn => (hdata n (mem_range.mp hn)).2.2
      _ = _ := by simp [hK', Nat.mul_comm]
  have hwaste : s.nextRaw - ((range o.labels.length).biUnion (o.raw s)).card ≤
      vanillaControls.waste := by
    have hraw : s.nextRaw = B * K := htrace.raw
    rw [haccepted, ← hraw] at hledger
    change _ ≤ 0
    omega
  have hmass (k : ℕ) (hk : k < K) :
      (∑ n ∈ Ico (o.cut k) (o.cut (k + 1)), o.movement s n) = 1 := by
    change ∑ n ∈ Ico k (k + 1), o.movement s n = 1
    rw [Nat.Ico_succ_singleton, sum_singleton]
    exact (hdata k (hK'.symm ▸ hk)).2.1
  change Structural s (resetOrdering o) vanillaControls K B
  refine reset_structural s o vanillaControls K B horder (by norm_num [Controls.Valid, vanillaControls])
    (fun n hn => (hdata n hn).1) ?_ ?_ ?_ ?_ ?_ hwaste
  · intro n _
    change n ≤ n ∧ range n ⊆ o.history s n ∧ (∑ j ∈ Ico n n, o.movement s j) ≤ 1 / 4
    rw [vanilla_history s B K n htrace]
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
    simp [vanillaControls]

lemma vanilla_valid (p : Params) (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ) (hw : 0 < p.workers)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ) :
    spec.valid (vanilla p) := by
  let q := vanilla p
  have hB : 0 < batchSize q := by unfold batchSize; omega
  have hK : 0 < horizon q := by unfold horizon; omega
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, hw, hregular,
    (vanilla_trace p.workers (batchSize q) (horizon q) hw hB).1,
    vanilla_structural p.workers (batchSize q) (horizon q) hw hB hK⟩

lemma vanilla_calls (p : Params) (hw : 0 < p.workers) :
    (program (vanilla p)).oracleCalls = batchSize (vanilla p) * horizon (vanilla p) := by
  let q := vanilla p
  have hB : 0 < batchSize q := by unfold batchSize; omega
  rw [program_calls, ← run_raw]
  exact (vanilla_trace p.workers (batchSize q) (horizon q) hw hB).2.raw

lemma vanilla_success (p : Params) (hp : spec.valid (vanilla p))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (vanilla p) I O) :
    let q := vanilla p
    let Q := batchSize q * horizon q
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => Q) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hw : 0 < p.workers := hp.2.2.2.2.2.2.1
  exact execute_success (vanilla p) hp _ (vanilla_calls p hw).le I O hI

end LongTails.Proofs.BirchCollectionVanilla
